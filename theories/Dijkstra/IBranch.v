From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     EuttEv
     Divergence
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant EvAns (E : Type -> Type) : Type -> Type :=
  evans : forall {A : Type} (ev : E A) (ans : A), EvAns E unit.

Arguments evans {E}.

Definition ibranch (E : Type -> Type) (R : Type) := itree (EvAns E) R.

Definition ibranch' (E : Type -> Type) (R : Type) := itree' (EvAns E) R.

Definition ev_stream (E : Type -> Type) := ibranch E unit.

Definition Nil {E : Type -> Type} : ev_stream E := Ret tt.

Definition ev_list (E : Type -> Type) := list (EvAns E unit).

Fixpoint ev_list_to_stream {E : Type -> Type} (l : ev_list E) : ev_stream E :=
  match l with
  | nil => Ret tt
  | e :: t => Vis e (fun _ => ev_list_to_stream t) end.

(*one append for branches and streams, get associativity for free from bind_bind*)
Definition append {E R} (s : ibranch E unit) (b : ibranch E R) :=
  ITree.bind s (fun _ => b).

Notation "s ++ b" := (append s b).

Inductive can_converge {E : Type -> Type} {A : Type} (a : A) : itree E A -> Prop :=
| conv_ret (t : itree E A) : t ≈ Ret a -> can_converge a t
| conv_vis (t : itree E A ) {B : Type} (e : E B) (k : B -> itree E A) (b : B) : 
    t ≈ Vis e k -> can_converge a (k b) -> can_converge a t.
Hint Constructors can_converge.


Global Instance eutt_proper_con_converge {A E} {a : A} : Proper (eutt eq ==> iff) (@can_converge E _ a).
Proof.
  intros t1 t2 Ht. split; intros.
  - induction H.
    + apply conv_ret; auto. rewrite <- Ht. auto. 
    + eapply conv_vis with (e0 := e); eauto. rewrite <- H.
      symmetry. auto.
  - induction H.
    + apply conv_ret; auto. rewrite Ht. auto.
    + eapply conv_vis with (e0 := e); eauto. rewrite Ht.
      auto.
Qed.

Lemma can_converge_branch : forall (E : Type -> Type) (R : Type) 
                                   (b : ibranch E R) (r1 r2 : R),
    can_converge r1 b -> can_converge r2 b -> r1 = r2.
Proof.
  intros. induction H; inversion H0; subst.
  - rewrite H in H1. pinversion H1. subst. auto.
  - rewrite H in H1. pinversion H1.
  - destruct e. destruct b. apply IHcan_converge. rewrite H in H0. inversion H0; subst.
    + pinversion H3.
    + destruct e. destruct b. 
      pinversion H3. apply inj_pair2 in H7. apply inj_pair2 in H8.
      apply inj_pair2 in H9. apply inj_pair2 in H10. subst.
      enough (k tt ≈ k0 tt); try apply REL.
      rewrite H5. auto.
 - destruct e. destruct e0. destruct b. destruct b0.
   apply IHcan_converge. rewrite H in H2.
   pinversion H2.
   repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
   subst. enough (k tt ≈ k0 tt); try apply REL.
   rewrite H4. auto.
Qed.

Definition finite {E : Type -> Type} (s : ev_stream E) : Prop := can_converge tt s.

Lemma finite_nil {E : Type -> Type} : finite (@Nil E).
Proof.
  apply conv_ret. unfold Nil. reflexivity.
Qed.

Lemma can_converge_list_to_stream : forall (E : Type -> Type) (l : ev_list E),
    finite (ev_list_to_stream l).
Proof.
  red. intros. induction l.
  - cbn. constructor. reflexivity.
  - cbn. eapply conv_vis with (e := a) (b := tt); try reflexivity. simpl. auto.
Qed.

Lemma finite_stream_list : forall (E : Type -> Type) (s : ev_stream E),
    finite s -> exists l, (s ≈ ev_list_to_stream l)%itree.
Proof.
  intros. red in H. induction H.
  - exists nil. auto.
  - destruct IHcan_converge as [l Hl]. unfold ev_list in l.
    inversion e. subst.
    exists (e:: l). simpl. rewrite H.
    destruct b. pfold. red. cbn. constructor.
    intros. destruct v. left. auto.
Qed.


(*technically doens't force divergence, it only disallows converges*)
Variant must_divergeF {E : Type -> Type} {A : Type} (F : itree E A -> Prop) : itree' E A -> Prop :=
  | MDivTau (t : itree E A) : F t -> must_divergeF F (TauF t)
  | MDivVis (B : Type) (k : B -> itree E A) (e : E B) : 
      (forall b, F (k b)) -> must_divergeF F (VisF e k).
Hint Constructors must_divergeF.

Definition must_diverge_ {E A} (sim : itree E A -> Prop) t := must_divergeF sim (observe t).

Lemma must_divergeF_mono {E A} (sim sim' : itree E A -> Prop) t
      (IN : must_divergeF sim t)
      (LE : sim <1= sim') : must_divergeF sim' t.
Proof.
  induction IN; eauto. 
Qed.

Lemma must_divergeF_mono' {E A} : monotone1 (@must_diverge_ E A).
Proof.
  unfold must_diverge_.
  red. intros. eapply must_divergeF_mono; eauto.
Qed.
Hint Resolve must_divergeF_mono' : paco. 

Definition must_diverge {E A} := paco1 (@must_diverge_ E A) bot1.

Global Instance eutt_proper_must_diverge {E A R} : Proper (eutt R ==> iff) (@must_diverge E A).
Proof.
  intros t1 t2 Ht. split.
  - revert t1 t2 Ht. pcofix CIH. intros t1 t2 Ht Hdiv.
    punfold Ht. unfold_eqit. pfold. red. punfold Hdiv. red in Hdiv.
    induction Ht.
    + inversion Hdiv.
    + constructor. inversion Hdiv. subst. right.
      pclearbot.
      eapply CIH; eauto.
    + constructor. inversion Hdiv. subst. apply inj_pair2 in H2.
      subst. intros. right. inversion Hdiv. subst. apply inj_pair2 in H4.
      subst. pclearbot. eapply CIH; eauto. apply H2.
    + apply IHHt. inversion Hdiv. subst. pclearbot. punfold H0.
    + constructor. left. pfold. apply IHHt. auto.
  - revert t1 t2 Ht. pcofix CIH. intros t1 t2 Ht Hdiv.
    punfold Ht. unfold_eqit. pfold. red. punfold Hdiv. red in Hdiv.
    induction Ht.
    + inversion Hdiv.
    + constructor. inversion Hdiv. subst. right.
      pclearbot.
      eapply CIH; eauto.
    + constructor. inversion Hdiv. subst. apply inj_pair2 in H2.
      subst. intros. right. inversion Hdiv. subst. apply inj_pair2 in H4.
      subst. pclearbot. eapply CIH; eauto. apply H2.
    +  constructor. left. pfold. apply IHHt. auto. 
    +  apply IHHt. inversion Hdiv. subst. pclearbot. punfold H0.
Qed.

(*weird subtlety for if there is a something like an exit event*)


Lemma not_converge_to_divergence : forall (E : Type -> Type) (A : Type) (t : itree E A), 
    (forall a, ~ can_converge a t) -> divergence t.
Proof.
  intros E A. pcofix CIH. intros.
  pfold. red. destruct (observe t) eqn : Heq.
  - exfalso. apply (H0 r0). specialize (itree_eta t) as Ht.
    rewrite Heq in Ht. rewrite Ht. constructor. reflexivity.
  - constructor. right. apply CIH.
    specialize (itree_eta t) as Ht. rewrite Heq in Ht.
    assert (t ≈ t0). { rewrite Ht. rewrite tau_eutt. reflexivity. }
    setoid_rewrite <- H. auto.
  - (*this case fails if X is an empty type*) 
Abort.


Lemma not_converge_to_must_diverge : forall (E : Type -> Type) (A : Type) (t : itree E A), 
    (forall a, ~ can_converge a t) -> must_diverge t.
Proof.
  intros E A. pcofix CIH. intros t Hcon. pfold.
  red. destruct (observe t) eqn : Heq;
         specialize (itree_eta t) as Ht; rewrite Heq in Ht.
  - exfalso. apply (Hcon r0). rewrite Ht. constructor. reflexivity.
  - constructor. right. apply CIH.
    setoid_rewrite Ht in Hcon. setoid_rewrite tau_eutt in Hcon.
    auto.
  - constructor. right. apply CIH.
    intros a Hcontra. setoid_rewrite Ht in Hcon.
    apply (Hcon a). eapply conv_vis; try reflexivity; eauto.
Qed.

Lemma classic_converge : forall (E : Type -> Type) (A : Type) (t : itree E A),
    (exists a, can_converge a t) \/ must_diverge t.
Proof.
  intros. destruct (classic (exists a, can_converge a t) ); auto.
  right. apply not_converge_to_must_diverge. intros a Hcontra.
  apply H. exists a. auto.
Qed.

Lemma append_vis : forall (E : Type -> Type) (R : Type)
                          (e : EvAns E unit) (k : unit -> ev_stream E) (b : ibranch E R),
                          Vis e k ++ b ≈ Vis e (fun a => k a ++ b).
Proof.
  intros E R. unfold append. intros.
  pfold. red. cbn. constructor. intros. left.
  enough ( (ITree.bind (k v) (fun _ : unit => b) ≈  (ITree.bind (k v) (fun _ : unit => b) ) ) ); auto.
  reflexivity.
Qed.

Global Instance proper_append {E R} : Proper (@eutt (EvAns E) unit unit eq ==> @eutt (EvAns E) R R eq ==> eutt eq) (@append E R).
Proof.
  intros log1 log2 Hlog b1 b2 Hb. unfold append. rewrite Hlog.
  eapply eutt_clo_bind; eauto. reflexivity.
Qed.



Lemma can_converge_append : forall (E : Type -> Type) (R : Type)
                                   (log : ev_stream E) (r : R),
      finite log -> can_converge r (log ++ Ret r).
Proof.
  intros. induction H.
  - unfold append. rewrite H. rewrite bind_ret.
    constructor. reflexivity.
  - rewrite H. inversion e. subst. rewrite append_vis.
    eapply conv_vis with (e0 := e) (k0 := fun a => k a ++ Ret r); eauto; try reflexivity.
Qed.

Lemma converge_ibranch_ev_list : forall (E : Type -> Type) (R : Type) 
                                        (b : ibranch E R) (r : R),
    can_converge r b -> (exists log, (ev_list_to_stream log) ++ Ret r ≈ b)%itree .
Proof.
  intros. induction H.
  - exists nil. cbn. rewrite H.
    pfold. red. cbn. constructor. auto.
  - destruct IHcan_converge as [log Hlog]. inversion e. subst.
    exists (e :: log). cbn. rewrite append_vis. rewrite H.
    pfold. red. cbn. constructor. cbn. intros. destruct v.
    left. destruct b. apply Hlog.
Qed.
Lemma classic_converge_ibranch : forall (E : Type -> Type) (R : Type) (b : ibranch E R),
    (exists r, exists log, ( (ev_list_to_stream log) ++ Ret r ≈ b)%itree ) \/ must_diverge b.
Proof.
  intros.
  destruct (classic_converge _ _ b ); auto. destruct H as [r Hr]. left.
  exists r. apply converge_ibranch_ev_list. auto.
Qed.

Arguments classic_converge_ibranch {E} {R}.


Lemma inv_append_eutt : forall (E : Type -> Type) (R : Type) (r1 r2 : R)
                               (log1 log2 : ev_list E),
    ((ev_list_to_stream log1) ++ Ret r1 ≈ (ev_list_to_stream log2) ++ Ret r2)%itree -> 
    log1 = log2 /\ r1 = r2.
Proof.
  intros. generalize dependent log2. induction log1; intros.
  - destruct log2.
    + split; auto. cbn in H. pinversion H. cbn. unfold append in *.
      cbn in *. subst. auto.
    + pinversion H.
  - destruct log2.
    + pinversion H.
    + cbn in H. unfold append in H. pinversion H. cbn in *.
      repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end.
      subst.
      enough (log1 = log2 /\ r1 = r2).
      { destruct H0. subst. auto. }
      apply IHlog1. apply REL. apply tt.
Qed.

Lemma must_diverge_not_converge : forall (E : Type -> Type) (R : Type) (t : itree E R) (r : R),
    can_converge r t -> ~ must_diverge t.
Proof.
  intros E R t r Hc Hd. induction Hc.
  - rewrite H in Hd. pinversion Hd.
  - apply IHHc. rewrite H in Hd. pinversion Hd.
    apply inj_pair2 in H2. apply inj_pair2 in H3. subst.
    apply H1.
Qed.
