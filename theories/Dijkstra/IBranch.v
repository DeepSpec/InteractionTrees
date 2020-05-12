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
     Logic.IndefiniteDescription
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
  | evans : forall {A : Type} (ev : E A) (ans : A), EvAns E unit
  (*if you can prove there is no answers, don't need to proved one*)
  | evempty : forall {A : Type} (Hempty : A -> void) (ev : E A), EvAns E void
.

(*I can use classical reasoning to say there either exists an answer or a 
  function into void*)
Lemma classic_empty : forall (A : Type), ( exists e : A + (A -> void), True ).
Proof.
  intros. destruct (classic (exists a : A, True)).
  - destruct H; eauto.
  - assert (f : A -> void); eauto. intros.
    exfalso. apply H; eauto.
Qed.

(* find where I can import this axiom from *)
Axiom classicT : forall (P : Prop), {P} + {~ P}.

Arguments evans {E}.
Arguments evempty {E}.

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

Ltac contra_void := try match goal with | a : void |- _ => contradiction end. 

Lemma can_converge_branch : forall (E : Type -> Type) (R : Type) 
                                   (b : ibranch E R) (r1 r2 : R),
    can_converge r1 b -> can_converge r2 b -> r1 = r2.
Proof.
  intros. induction H; inversion H0; subst.
  - rewrite H in H1. pinversion H1. subst. auto.
  - rewrite H in H1. pinversion H1.
  - destruct e. destruct b. apply IHcan_converge. rewrite H in H0. inversion H0; subst;
                                                                    contra_void.
    + pinversion H3.
    + destruct e. destruct b. 
      pinversion H3. apply inj_pair2 in H7. apply inj_pair2 in H8.
      apply inj_pair2 in H9. apply inj_pair2 in H10. subst.
      enough (k tt ≈ k0 tt); try apply REL.
      rewrite H5. auto. contradiction.
    + contradiction.
 - destruct e. destruct e0. destruct b. destruct b0.
   apply IHcan_converge. rewrite H in H2.
   pinversion H2.
   repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
   subst. enough (k tt ≈ k0 tt); try apply REL.
   rewrite H4. auto; contra_void.
   + destruct b0.
   + destruct b.
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
    subst. contradiction.
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
    subst. contradiction.
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
    left. destruct b. apply Hlog. subst. contradiction.
Qed.

Lemma classic_converge_ibranch : forall (E : Type -> Type) (R : Type) (b : ibranch E R),
    (exists r, exists log, ( (ev_list_to_stream log) ++ Ret r ≈ b)%itree ) \/ must_diverge b.
Proof.
  intros.
  destruct (classic_converge _ _ b ); auto. destruct H as [r Hr]. left.
  exists r. apply converge_ibranch_ev_list. auto.
Qed.

Arguments classic_converge_ibranch {E} {R}.

Lemma append_nil : forall (E : Type -> Type) (R : Type) (b : ibranch E R),
    (Ret tt ++ b ≈ b)%itree.
Proof.
  intros. unfold append. rewrite bind_ret. reflexivity.
Qed.

Lemma append_assoc : forall (E : Type -> Type) (R : Type) (b : ibranch E R)
                            (log log' : ev_list E),
    ev_list_to_stream (log ++ log')%list ++ b ≈ 
                      (ev_list_to_stream log) ++ (ev_list_to_stream log') ++ b.
Proof.
  intros E R b log. induction log.
  - simpl. intros. rewrite append_nil. reflexivity.
  - cbn. intros. rewrite append_vis. setoid_rewrite IHlog.
    rewrite append_vis. reflexivity.
Qed.

Lemma append_div : forall (E : Type -> Type) (R : Type) (b : ibranch E R)
                          (log : ev_list E),
    must_diverge b -> must_diverge ((ev_list_to_stream log) ++ b).
Proof.
  intros. induction log.
  - cbn. unfold append. rewrite bind_ret. auto.
  - cbn. unfold append.
    pfold. red. cbn. constructor. intros. left. auto.
Qed.

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


Variant REvRef (E : Type -> Type) : forall (A B : Type), EvAns E A -> E B -> Prop := 
  | rer {A : Type} (e : E A) (a : A) : REvRef E unit A (evans A e a) e
  | ree {A : Type} (e : E A) (Hempty : A -> void) : REvRef E void A (evempty A Hempty e) e
.
Hint Constructors REvRef.

(*shouldn't need an empty case*)
Variant RAnsRef (E : Type -> Type) : forall (A B : Type), EvAns E A -> A -> E B -> B -> Prop :=
  | rar {A : Type} (e : E A) (a : A) : RAnsRef E unit A (evans A e a) tt e a.
Hint Constructors RAnsRef.

Definition branch_refine {E R}  (t : itree E R) (b : ibranch E R)  := 
   euttEv (REvRef E) (RAnsRef E) eq b t.
(*
(*a bit hacky, but I can worry about elegance of definition later*)
Definition branch_refine {E R} (b : ibranch E R) (t : itree E R) : Prop :=
  exists t', exists b', (b' ≈ b)%itree /\ t' ≈ t /\ euttEv (REvRef E) (RAnsRef E) eq b' t'.
*)
Notation "b ⊑ t" := (branch_refine t b) (at level 70).



Lemma branch_refine_proper_left' : forall (E : Type -> Type) (R : Type) (b1 b2 : ibranch E R)
                (t : itree E R), (b1 ≈ b2)%itree -> euttEv (REvRef E) (RAnsRef E) eq b1 t -> 
                                 euttEv (REvRef E) (RAnsRef E) eq b2 t.
Proof. 
  intros E R. pcofix CIH. intros. pfold. red.
  punfold H1. red in H1.  punfold H0. red in H0.
  genobs_clear t ot3.
  hinduction H0 before CIH; intros; clear b1 b2; eauto.
  - remember (RetF r1) as ot1. hinduction H1 before CIH; intros; inv Heqot1; eauto with paco.
    + constructor. auto.
    + constructor. eapply IHeuttEvF; eauto.
  -  assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst. pclearbot.
      constructor. right. eapply CIH; eauto.
      apply euttEv_inv_tauLR. pfold. auto.
    + inv H1; try (exfalso; eapply EQ; eauto; fail). 
      pclearbot. constructor.
      punfold REL. red in REL.
      hinduction H0 before CIH; intros; subst; try (exfalso; eapply EQ; eauto; fail). 
      * dependent induction REL; rewrite <- x.
        ++ constructor. auto.
        ++ constructor. eapply IHREL; eauto.
      * eapply IHeuttEvF; eauto. clear IHeuttEvF.
        dependent induction REL; try (exfalso; eapply EQ; eauto; fail).  
        ++ pclearbot. rewrite <- x. constructor; auto. pstep_reverse.
        ++ auto. 
        ++ rewrite <- x. constructor; auto. eapply IHREL; eauto.
      * dependent induction REL; rewrite <- x.
        ++ constructor; auto. intros. apply H0 in H1. right.
           pclearbot. eapply CIH; eauto.
        ++ constructor. eapply IHREL; eauto.
  - remember (VisF e k1) as ot1.
    hinduction H1 before CIH; intros; dependent destruction Heqot1.
    + constructor. eapply IHeuttEvF; eauto.
    + pclearbot. constructor; auto. intros. apply H0 in H1. 
      pclearbot. right.
      eapply CIH; eauto.
  - eapply IHeqitF. remember (TauF t1) as otf1. 
    hinduction H1 before CIH; intros;  dependent destruction Heqotf1; eauto.
    + constructor. pclearbot. pstep_reverse.
    + constructor. eapply IHeuttEvF; eauto.
  - constructor. eapply IHeqitF. eauto.

Qed. 

Lemma branch_refine_proper_right' : forall (E : Type -> Type) (R : Type) (b : ibranch E R)
                                   (t1 t2 : itree E R), t1 ≈ t2 -> euttEv (REvRef E) (RAnsRef E) eq b t1 -> 
                                 euttEv (REvRef E) (RAnsRef E) eq b t2.
Proof.
  intros E R. pcofix CIH. intros. punfold H1. red in H1.
  punfold H0. red in H0. pfold. red.
  genobs_clear t2 ot2.
  hinduction H0 before CIH; intros; clear t1; subst; eauto.
  - remember (RetF r2) as ot1. hinduction H1 before CIH; intros; inv Heqot1; eauto with paco.
    + constructor; auto.
    + constructor. eauto.
  - pclearbot. remember (TauF m1) as otm1.
    hinduction H1 before CIH; intros; subst; try (inv Heqotm1).
    + constructor. pclearbot. right. eapply CIH; eauto.
    + constructor. right. eapply CIH; eauto.
      apply euttEv_inv_tauR. pfold. auto.
    + punfold REL. red in REL. 
      dependent induction REL; subst.
      * constructor. clear IHeuttEvF.
        hinduction H1 before CIH; intros; dependent destruction x0.
        ++ rewrite <- x. constructor. auto.
        ++ constructor. auto.
      * eapply IHeuttEvF with (m2 := m0); auto.
        pclearbot. pfold. red. rewrite <- x. constructor; auto.
        punfold REL.
      * constructor. rewrite <- x.
        clear IHeuttEvF. hinduction H1 before CIH; intros; dependent destruction x0.
        ++ constructor. eapply IHeuttEvF; eauto.
        ++ constructor; auto. intros. apply H0 in H1.
           pclearbot. right. eapply CIH; eauto. apply REL.
      * eapply IHeuttEvF; eauto.
      * constructor. rewrite <- x. eapply IHREL; eauto.
  - remember (VisF e k1) as ot1. hinduction H1 before CIH; intros; inv Heqot1.
    + constructor. eauto.
    + apply inj_pair2 in H4. apply inj_pair2 in H3. subst.
      constructor; auto. intros. apply H0 in H1.
      right. pclearbot. eapply CIH; eauto; apply REL.
  - eapply IHeqitF; eauto. remember (TauF t0) as otf0.
    hinduction H1 before CIH; intros; dependent destruction Heqotf0; eauto.
    + constructor. pclearbot. pstep_reverse.
    + constructor. eapply IHeuttEvF; eauto.
  - constructor. eapply IHeqitF. eauto.
Qed.

Instance branch_refine_proper {E R} : Proper (@eutt E R R eq ==> eutt eq ==> iff) branch_refine.
Proof.
  intros b1 b2 Heuttb t1 t2 Heuttt.
  split; intros;
  try (eapply branch_refine_proper_right'; [eauto | eapply branch_refine_proper_left'; eauto]);
  symmetry; auto.
Qed.

Lemma branch_refine_ret : forall (E : Type -> Type) (R : Type) (r : R),
    @branch_refine E R (Ret r) (Ret r).
Proof.
  intros. pfold. constructor. auto.
Qed.

Lemma branch_refine_ret_inv_r : forall (E : Type -> Type) (R : Type) (r : R)
                                     (t : itree E R),
    Ret r ⊑ t -> t ≈ Ret r.
Proof.
  intros. pfold. red. punfold H. red in H. cbn in *.
  dependent induction H; subst.
  - rewrite <- x. constructor. auto.
  - rewrite <- x. constructor; auto.
Qed.

Lemma branch_refine_ret_inv_l : forall (E : Type -> Type) (R : Type) (r : R)
                                     (b : ibranch E R),
    b ⊑ Ret r -> (b ≈ Ret r)%itree.
Proof.
  intros. pfold. red. punfold H. red in H. cbn in *.
  dependent induction H; subst.
  - rewrite <- x. constructor. auto.
  - rewrite <- x. constructor; auto.
Qed.

Lemma branch_refine_vis_inv : forall (E : Type -> Type) (R A: Type) (e : E A) (a : A)
                                     (b :ibranch E R) (k : A -> itree E R),
    branch_refine (Vis e k) (Vis (evans A e a) (fun _ => b))  -> branch_refine (k a) b .
Proof.
  intros E R A e a. intros.
  red in H. red. punfold H. red in H. inversion H. 
  repeat match goal with H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
  subst. 
  assert (RAnsRef E unit A (evans A e a) tt e a); eauto.
  apply H7 in H0. pclearbot. auto.
Qed.

Lemma branch_refine_vis_add : forall (E : Type -> Type) (R A: Type) (e : E A) (a : A)
                                     (b :ibranch E R) (k : A -> itree E R),
    b ⊑ k a -> Vis (evans A e a) (fun _ => b) ⊑ Vis e k.
Proof.
  intros. pfold. red. cbn. constructor; eauto.
  intros. left. inversion H0.
  repeat match goal with H : existT _ _ _ = _   |- _ => apply inj_pair2 in H end.
  subst. auto.
Qed.

Lemma branch_refine_bind : forall (E : Type -> Type) (R S : Type) 
                   (b : ibranch E R) (t : itree E R) (f : R -> ibranch E S) (g : R -> itree E S),
    b ⊑ t -> (forall r, f r ⊑ g r) -> (ITree.bind b f) ⊑ t >>= g.
Proof.
  intros E R S b t f g Hbt Hfg. generalize dependent b. generalize dependent t.
  pcofix CIH. intros. pfold. red. cbn.
  punfold Hbt. red in Hbt. 
  dependent induction Hbt.
  -  specialize (itree_eta b) as Hb. rewrite <- x0 in Hb.
     admit.
  - (*this bind stuff is a headache*)
    (*maybe we can see what else we need*)
Admitted.

Lemma event_ans_constr : forall (E : Type -> Type) (R : Type) (e : E R),
    exists (A : Type), exists e' : EvAns E A, REvRef E A R e' e.
Proof.
  intros.
  destruct (classic_empty R) as  [ [a | Hempty]  _ ] .
  - exists unit. exists (evans R e a). eauto.
  - exists void. exists (evempty R Hempty e). eauto.
Qed.
(* WARNING: this function should not be used for computation  *)
CoFixpoint determinize_ (E : Type -> Type) (R : Type) (ot : itree' E R) : ibranch E R.
  destruct ot.
- apply (Ret r).
- apply (Tau (determinize_ E R (observe t) ) ).
- specialize (classic_empty X) as H. 
  apply constructive_indefinite_description in H. destruct H as [ [x | f] _].
  + apply (Vis (evans X e x) (fun _ =>  (determinize_ E R (observe (k x)) ) )) .
  + apply (Vis (evempty X f e) (fun v : void => match v return ibranch E R with end)  ).
Defined.

Definition determinize {E R} t := determinize_ E R (observe t).

Lemma itree_refine_nonempty : forall (E : Type -> Type) (R : Type) (t : itree E R),
    exists b : ibranch E R, b ⊑ t.
Proof.
  intros. exists (determinize t). generalize dependent t.
  pcofix CIH. intros. pfold. red. unfold determinize. destruct (observe t).
  - cbn. constructor. auto.
  - cbn. constructor. right. apply CIH.
  - unfold observe. cbn. cbn. destruct (constructive_indefinite_description (fun _ : X + (X -> void) => True)
                   (classic_empty X)).
    destruct x as [x | f]; cbn.
    + constructor; eauto. intros. right. 
      inversion H. 
      repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
      subst. apply CIH.
    + constructor; auto. intros. contradiction. 
Qed.

    Lemma refine_set_eq_to_eutt_vis_aux : forall (E : Type -> Type) (R : Type) (r : itree E R -> itree E R -> Prop)
      (CIH : forall t1 t2 : itree E R, (forall b : ibranch E R, b ⊑ t1 <-> b ⊑ t2) -> r t1 t2)
      (t1 t2 : itree E R)
      (H0 : forall b : ibranch E R, b ⊑ t1 <-> b ⊑ t2)
      (A B : Type) (e : E A) (e0 : E B)
      (k : A -> itree E R) (k0 : B -> itree E R)
      (Ht1 : t1 ≅ Vis e k) (Ht2 : t2 ≅ Vis e0 k0 ),
      eqitF eq true true id (upaco2 (eqit_ eq true true id) r) (VisF e k) (VisF e0 k0).
Proof.
  intros.
  destruct (classic_empty A) as [ [a | Ha] _ ].
  - specialize  branch_refine_vis_add with (e := e) (k := k) (a := a) as Hbrv.
    assert (exists b, b ⊑ (k a) ). 
    { apply itree_refine_nonempty. }
    destruct H as [b Hbk]. apply branch_refine_vis_add with (e := e) in Hbk.
    rewrite <- Ht1 in Hbk.
    apply H0 in Hbk as Hbk0.
    rewrite Ht1 in Hbk. rewrite Ht2 in Hbk0.
    pinversion Hbk.
    pinversion Hbk0.
    repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
    subst.
    inversion H10.
    repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
    subst.
    repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
    subst. constructor.
    intros. right. eapply CIH; eauto.
    intros. setoid_rewrite Ht1 in H0. setoid_rewrite Ht2 in H0.
    split; intros.
    + apply branch_refine_vis_add with (e := e) in H. apply H0 in H.
      apply branch_refine_vis_inv in H. auto.
    + apply branch_refine_vis_add with (e := e) in H. apply H0 in H.
      apply branch_refine_vis_inv in H. auto.
  - set (fun v : void => match v return ibranch E R with end) as ke.
    set (Vis (evempty A Ha e) ke) as b.
    assert (b ⊑ t1).
    {
      unfold b. rewrite Ht1. pfold. red. cbn.
      constructor; intuition.
    }
    apply H0 in H as H1. unfold b in *. clear b.
    rewrite Ht1 in H. rewrite Ht2 in H1.
    pinversion H. pinversion H1.
    repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
    subst. inversion H12.
    repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
    subst.
    repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
    subst.
    constructor.
    intros. right. eapply CIH.
    intros. setoid_rewrite Ht1 in H0. setoid_rewrite Ht2 in H0.
    split; intros; contradiction.
Qed.

Lemma branch_refine_vis : forall (E : Type -> Type) (R A : Type) (b : ibranch E R)
                                 (e : E A) (k : A -> itree E R),
    b ⊑ Vis e k -> exists X, exists e0 : EvAns E X, exists k0, (b ≈ Vis e0 k0)%itree.
Proof.
  intros. punfold H. red in H. cbn in H.
  dependent induction H.
  - enough 
      (exists (X : Type) (e0 : EvAns E X) (k0 : X -> itree (EvAns E) R), (t1 ≈ Vis e0 k0)%itree).
    {
      destruct H0 as [ X [e0 [k0 Ht1] ] ].
      exists X. exists e0. exists k0.
      specialize (itree_eta b) as Hb. rewrite <- x in Hb. rewrite Hb.
      rewrite tau_eutt. auto.
    }
    eapply IHeuttEvF; eauto.
  - exists A0. exists e1. exists k1.
    specialize (itree_eta b) as Hb. rewrite <- x in Hb.
    rewrite Hb. reflexivity.
Qed.

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.


Lemma branch_refine_vis_l : forall (E : Type -> Type) (R A: Type) (t : itree E R)
                                   (e : EvAns E A) (k : A -> ibranch E R),
    Vis e k ⊑ t -> exists X, exists e0 : E X, exists k0 : X -> itree E R, t ≈ Vis e0 k0.
Proof.
  intros. punfold H. red in H. cbn in *.
  dependent induction H.
  - assert (t2 ≈ t).
    {
      specialize (itree_eta t). rewrite <- x. intros.
      rewrite H0. rewrite tau_eutt. reflexivity.
    }
    setoid_rewrite <- H0. eapply IHeuttEvF; eauto.
  - exists B. exists e2.  exists k2. specialize (itree_eta t) as Ht.
      rewrite <- x in Ht. rewrite Ht. reflexivity.
Qed.

Lemma branch_refine_can_converge_ex : forall (E : Type -> Type) (R : Type)
                         (t : itree E R) (r : R),
    can_converge r t -> exists b, can_converge r b /\ b ⊑ t.
Proof.
  intros. induction H.
  - exists (Ret r). rewrite H. split.
    + constructor. reflexivity.
    + apply branch_refine_ret.
  - destruct IHcan_converge as [br [Hrbr Hrefbr] ].
    exists  (Vis (evans B e b) (fun _ => br) ). split.
    + eapply conv_vis with (b0 := tt); try reflexivity. auto.
    + rewrite H. apply branch_refine_vis_add. auto.
Qed.

Lemma branch_refine_can_converge : forall (E : Type -> Type) (R : Type)
                         (t : itree E R) (r : R) (b : ibranch E R),
    can_converge r b -> b ⊑ t -> can_converge r t.
Proof.
  intros. generalize dependent t. induction H; intros.
  - rewrite H in H0. apply branch_refine_ret_inv_r in H0.
    rewrite H0. constructor. reflexivity.
  - rewrite H in H1. apply branch_refine_vis_l in H1 as Ht0.
    destruct Ht0 as [X [e0 [k0 Ht0] ] ].
    rewrite Ht0 in H1. pinversion H1. subst.
    inj_existT. subst. rewrite Ht0. 
    inversion H4; subst; inj_existT; subst; try contradiction.
    eapply conv_vis with (b0 := a); try reflexivity.
    apply IHcan_converge. pclearbot.
    specialize (H9 tt a). assert (RAnsRef E unit X (evans X e0 a) tt e0 a).
    constructor. apply H9 in H2. pclearbot. destruct b. auto.
Qed.

Lemma branch_refine_must_diverge : forall (E : Type -> Type) (R : Type)
                       (t : itree E R) (b : ibranch E R),
    must_diverge t -> b ⊑ t -> must_diverge b.
Proof.
  intros E R. pcofix CIH. intros. punfold H0. red in H0.
  punfold H1. red in H1. pfold. red. dependent induction H1.
  - rewrite <- x in H0. inversion H0.
  - rewrite <- x0. constructor. right. pclearbot. eapply CIH; eauto.
    rewrite <- x in H0. inv H0. pclearbot. auto.
  - rewrite <- x. constructor. left.  pfold. eapply IHeuttEvF; eauto.
  - eapply IHeuttEvF; auto. rewrite <- x in H0. inv H0.
    pclearbot. punfold H2.
  - rewrite <- x0. rewrite <- x in H0. constructor. inv H0.
    inj_existT. subst. intros. right. pclearbot. 
    inversion H; subst; inj_existT; subst; try contradiction. destruct b0. clear H5.
    eapply CIH; try apply H3.
    specialize (H1 tt a). assert (RAnsRef _ _ _ (evans B e2 a) tt e2 a ).
    constructor. apply H1 in H0. unfold id in H0.
    destruct H0; try contradiction. eauto.
Qed.

Lemma branch_refine_converge_bind : forall (E : Type -> Type) (R S : Type)
            (b : ibranch E R) (t : itree E R) (f : R -> ibranch E S) (g : R -> itree E S) (r : R),
    can_converge r b -> b ⊑ t -> f r ⊑ g r -> ITree.bind b f ⊑ ITree.bind t g.
Proof.
  intros. generalize dependent t. dependent induction H; intros.
  - rewrite H. rewrite H in H0. apply branch_refine_ret_inv_r in H0. 
    rewrite H0. repeat rewrite bind_ret. auto.
  - specialize (IHcan_converge H1). 
    rewrite H in H2. apply branch_refine_vis_l in H2 as Ht.
    destruct Ht as [X [e0 [k0 Ht] ] ].
    rewrite Ht in H2. punfold H2. red in H2. cbn in H2. inversion H2; subst.
    inj_existT. subst. pclearbot.
    inversion H5; inj_existT; subst; try contradiction.
    inj_existT. subst. rewrite H. rewrite Ht.
    pfold. red. cbn. constructor; auto.
    intros. apply H10 in H3. pclearbot. left. 
    destruct a0. destruct b. apply IHcan_converge. auto.
Qed.

Lemma branch_refine_diverge_bind : forall (E : Type -> Type) (R S : Type)
                  (b : ibranch E R) (t : itree E R) (f : R -> ibranch E S) (g : R -> itree E S),
    must_diverge b -> b ⊑ t -> ITree.bind b f ⊑ ITree.bind t g.
Proof.
  intros E R S b t f g. generalize dependent b. generalize dependent t.
  pcofix CIH. intros.
  punfold H0. red in H0.
  punfold H1. red in H1. pfold. red. cbn. 
  dependent induction H1.
  - rewrite <- x0 in H0. inv H0.
  - unfold observe. cbn. rewrite <- x0. rewrite <- x.
    cbn. constructor. right. pclearbot. apply CIH; auto.
    rewrite <- x0 in H0. inv H0. pclearbot. auto.
  - unfold observe at 1. cbn. rewrite <- x. cbn. constructor.
    eapply IHeuttEvF; eauto. rewrite <- x in H0. inv H0. pclearbot. pstep_reverse.
  - unfold observe at 2. cbn. rewrite <- x. cbn. constructor. 
    eapply IHeuttEvF; eauto.
  - unfold observe. cbn. rewrite <- x0. rewrite <- x. cbn. constructor; auto.
    intros.
    rewrite <- x0 in H0. inv H0. inj_existT. subst. pclearbot.
    apply H1 in H2. right. eapply CIH; eauto; try apply H4.
    unfold id in H2. pclearbot. auto.
Qed.
  

Lemma refine_set_eq_to_eutt : forall (E : Type -> Type) (R : Type) (t1 t2 : itree E R),
    (forall b, b ⊑ t1 <-> b ⊑ t2) -> t1 ≈ t2.
Proof.
  intros E R. pcofix CIH. intros.
  pfold. red.
  remember (observe t1) as ot1. remember (observe t2) as ot2.
  destruct (ot1); destruct (ot2).
    (*Ret Ret*)
  - specialize (H0 (Ret r0) ) as Hr0.
    specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2.
    rewrite Ht1 in Hr0. rewrite Ht2 in Hr0.
    assert (Ret r0 ⊑ t2).
    { rewrite Ht2. apply Hr0. pfold. constructor. auto. }
    rewrite Ht2 in H. pinversion H. subst. constructor. auto.
    (*Ret Tau *)
  - specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2.
    setoid_rewrite Ht2 in H0.
    specialize (H0 (Ret r0) ).
    rewrite tau_eutt in H0. constructor; auto.
    assert (Ret r0 ⊑ t1).
    { rewrite Ht1. pfold. constructor. auto. }
    apply H0 in H. punfold H. red in H. cbn in H.
    clear H0 Ht1 Ht2 Heqot1 Heqot2. dependent induction H.
    + rewrite <- x. constructor; auto.
    + rewrite <- x. constructor; auto.
    (*Ret Vis*)
  - exfalso.
    specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2.
    assert (Ret r0 ⊑ t1).
    { rewrite Ht1. pfold. constructor. auto. }
    apply H0 in H. rewrite Ht2 in H. pinversion H.
    (*Tau Ret*)
  - specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2.
    setoid_rewrite Ht1 in H0. setoid_rewrite Ht2 in H0.
    assert (Ret r0 ⊑ t2).
    { rewrite Ht2. pfold. constructor. auto. }
     rewrite Ht2 in H. apply H0 in H as H1. punfold H1.
    clear Heqot1 Heqot2 Ht1 Ht2 H H0. red in H1. cbn in *.
    constructor; auto. inv H1. dependent induction H2; intros; subst.
    + rewrite <- x. auto.
    + rewrite <- x. constructor; auto.
    (*Tau Tau*)
  - constructor. right. eapply CIH. 
    intros. 
    specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2.
    assert (t1 ≈ t). { rewrite Ht1. rewrite tau_eutt. reflexivity. }
    assert (t2 ≈ t0). { rewrite Ht2. rewrite tau_eutt. reflexivity. }
    rewrite <- H. rewrite <- H1. auto.
    (*Tau Vis*)
  - specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2. 
    specialize (itree_refine_nonempty _ _ (t1) ) as [b Hbt1].
    apply H0 in Hbt1 as Hbt2. rewrite Ht1 in Hbt1.
    rewrite tau_eutt in Hbt1. 
    rewrite Ht2 in Hbt2.
    apply branch_refine_vis in Hbt2 as Hb.
    destruct Hb as [Y [e0 [k0 Hb] ] ].
    rewrite Hb in Hbt2.
    rewrite Hb in Hbt1. clear Hb b.
    constructor; auto. 
    setoid_rewrite Ht1 in H0. setoid_rewrite tau_eutt in H0.
    clear Heqot1 Heqot2. clear Ht1 t1.
    punfold Hbt1. red in Hbt1. cbn in *.
    dependent induction Hbt1.
    + rewrite <- x. constructor; auto. eapply IHHbt1; eauto.
      assert (t0 ≈ t).
      { 
        specialize (itree_eta t) as Ht. rewrite <- x in Ht. rewrite Ht.
        rewrite tau_eutt. reflexivity. 
      }
      setoid_rewrite H. auto.
    + rewrite <- x.
      specialize (itree_eta t) as Ht. rewrite <- x in Ht.
      eapply refine_set_eq_to_eutt_vis_aux; eauto.
    (*Vis Ret*)
  - exfalso.
    specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2.
    assert (Ret r0 ⊑ t2).
    { rewrite Ht2. pfold. constructor. auto. }
    apply H0 in H. rewrite Ht1 in H. pinversion H.
    (*Vis Tau*)
  - specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2. 
    specialize (itree_refine_nonempty _ _ (t2) ) as [b Hbt2].
    apply H0 in Hbt2 as Hbt1. rewrite Ht1 in Hbt1.
    rewrite Ht2 in Hbt2.
    rewrite tau_eutt in Hbt2. 
    apply branch_refine_vis in Hbt1 as Hb.
    destruct Hb as [Y [e0 [k0 Hb] ] ].
    rewrite Hb in Hbt2.
    rewrite Hb in Hbt1. clear Hb b.
    constructor; auto. 
    setoid_rewrite Ht2 in H0. setoid_rewrite tau_eutt in H0.
    clear Heqot1 Heqot2. clear Ht2 t2.
    punfold Hbt2. red in Hbt2. cbn in *.
    dependent induction Hbt2.
    + rewrite <- x. constructor; auto. eapply IHHbt2; eauto.
      assert (t2 ≈ t).
      { 
        specialize (itree_eta t) as Ht. rewrite <- x in Ht. rewrite Ht.
        rewrite tau_eutt. reflexivity. 
      }
      setoid_rewrite H. auto.
    + rewrite <- x.
      specialize (itree_eta t) as Ht. rewrite <- x in Ht.
      eapply refine_set_eq_to_eutt_vis_aux; eauto.
    (*Vis Vis*)
  - specialize (itree_eta t1) as Ht1. rewrite <- Heqot1 in Ht1.
    specialize (itree_eta t2) as Ht2. rewrite <- Heqot2 in Ht2.
    eapply refine_set_eq_to_eutt_vis_aux; eauto.
Qed.

Definition peel_vis {E R S A B} (e0 : E A) (a : A) (k0 : unit -> ibranch E R)
           (e1 : E B) (k1 : B -> itree E S) 
           (peel : ibranch' E R -> itree' E S -> ibranch E S) : ibranch E S.
destruct (classicT (A = B) ).
- subst. apply (Vis (evans _ e0 a) (fun _ => peel (observe (k0 tt)) (observe (k1 a) ) ) ).
- apply ITree.spin.
Defined.

CoFixpoint peel_ {E R S} (ob : ibranch' E R) (ot : itree' E S) : ibranch E S :=
  match ob, ot with
  | TauF b, TauF t => Tau (peel_ (observe b) (observe t))
  | _, RetF s => Ret s
  | TauF b, ot => Tau (peel_ (observe b) ot )
  | ob, TauF t => Tau (peel_ ob (observe t) )
  | VisF (evempty _ Hempty e) _ , _ => Vis (evempty _ Hempty e) (fun v : void => match v with end)
  (* The type of this is problematic need some tricky dependently typed programming
     in order to have this work
  *)

  | VisF (evans _ e0 a) k0, VisF e1 k1 => peel_vis e0 a k0 e1 k1 peel_
  | _, _ => ITree.spin 
  end.

Definition peel {E R S} (b : ibranch E R) (t : itree E S) : ibranch E S :=
  peel_ (observe b) (observe t).
 
Inductive branch_prefix {E : Type -> Type} {R S: Type} 
          (F : ibranch E R -> ibranch E S -> Prop) : ibranch' E R -> ibranch' E S -> Prop := 
| ret_prefix (r : R) (ob : ibranch' E S) : branch_prefix F (RetF r) ob
| vis_ans_prefix {A : Type} (e : E A) (a : A) (br :ibranch E R) (bs :ibranch E S) :
    F br bs -> branch_prefix F (VisF (evans A e a) (fun _ => br) ) (VisF (evans A e a) (fun _ => bs))
| vis_empty_prefix {A : Type} (e : E A) (Hempty : A -> void) :
    branch_prefix F (VisF (evempty A Hempty e) (fun v : void => match v with end) )
                    (VisF (evempty A Hempty e) (fun v : void => match v with end) )
| tau_lr_prefix (br : ibranch E R) (bs : ibranch E S) : 
    F br bs -> branch_prefix F (TauF br) (TauF bs)
(* can add eutt style inductive tau rules *)


.



Lemma refine_ret_vis_contra : forall (E: Type -> Type) (R A: Type)
                     (r : R) (e : E A) (k : A -> itree E R),
    ~ (Ret r ⊑ Vis e k).
Proof.
  intros. intro Hcontra. pinversion Hcontra.
Qed.

(* maybe a better way of doing it is to use strong LEM to see if X = A in the vis case
   then I can remove that if statement given

 *)

Lemma peel_t_ret : forall E R S (b : ibranch E S) (t : itree E R) r, t ≅ Ret r -> (peel b t ≅ Ret r)%itree.
Proof.
  intros.  unfold peel.
  pinversion H; subst; try inv CHECK.
  destruct (observe b); cbn; auto. 
  - pfold. red. cbn. constructor. auto.
  - pfold. red. cbn. constructor; auto.
  - pfold. red. cbn. simpl. destruct e.
    + cbn. constructor. auto.
    + cbn. constructor. auto.
Qed.

(*doing these proofs, may require some techniques you don't really know*)

Lemma peel_refine_t : forall (E : Type -> Type) (R S : Type)
                  (b : ibranch E S) (t : itree E R) (f : R -> itree E S)
     (HeuttEv : b ⊑ ITree.bind t f),
    peel b t ⊑ t.
Proof.
  intros E R S b t f. generalize dependent b. generalize dependent t.
  pcofix CIH. intros.
  punfold HeuttEv. red in HeuttEv. cbn in HeuttEv. pfold. red.
  unfold peel.
  destruct (observe t) eqn : Heq.
  - destruct (observe b); cbn; try (constructor; auto).
    destruct e; cbn; constructor; auto.
  - dependent induction HeuttEv.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_tau in x. pinversion x.
      inv CHECK.
    + rewrite <- x0. cbn. constructor. right. eapply CIH.
      pclearbot. symmetry in Heq. apply simpobs in x0.
      apply simpobs in x. apply simpobs in Heq.
      apply eq_sub_eutt in x0. apply eq_sub_eutt in Heq.
      rewrite tau_eutt in Heq. rewrite tau_eutt in x0.
      rewrite <- Heq. rewrite x. rewrite tau_eutt. auto.
    + rewrite <- x. cbn. constructor. right. eapply CIH.
      clear IHHeuttEv. symmetry in Heq. apply simpobs in Heq.
      apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
      rewrite <- Heq. pfold. auto.
    + cbn. destruct (observe b) eqn : Heq'.
      * cbn. rewrite <- Heq'. constructor. right. eapply CIH. 
        symmetry in Heq'.
        apply simpobs in Heq'. rewrite Heq'.
        symmetry in Heq. apply simpobs in Heq.
        apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
        rewrite <- Heq. apply simpobs in x. rewrite x.
        rewrite tau_eutt. pfold. auto.
      * cbn. clear IHHeuttEv. 
        constructor. right. eapply CIH. 
        symmetry in Heq. apply simpobs in Heq.
        apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
        rewrite <- Heq.
        apply simpobs in x. apply eq_sub_eutt in x.
        rewrite tau_eutt in x. rewrite x.
        enough (Tau t1 ⊑ t2). 
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * destruct e; cbn.
        ++ constructor. right. rewrite <- Heq'. clear IHHeuttEv.
           eapply CIH. symmetry in Heq.
           apply simpobs in Heq. apply eq_sub_eutt in Heq. 
           rewrite tau_eutt in Heq. apply simpobs in x.
           apply eq_sub_eutt in x. rewrite tau_eutt in x.
           rewrite <- Heq. rewrite x. pfold. red.
           rewrite Heq'. auto.
        ++ constructor. right. rewrite <- Heq'. clear IHHeuttEv.
           eapply CIH. symmetry in Heq.
           apply simpobs in Heq. apply eq_sub_eutt in Heq. 
           rewrite tau_eutt in Heq. apply simpobs in x.
           apply eq_sub_eutt in x. rewrite tau_eutt in x.
           rewrite <- Heq. rewrite x. pfold. red.
           rewrite Heq'. auto.
    + exfalso. symmetry in Heq. apply simpobs in Heq.
      apply simpobs in x.
      rewrite Heq in x. rewrite bind_tau in x. pinversion x.
      inv CHECK.
  - dependent induction HeuttEv.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x; inv CHECK.
    + rewrite <- x. cbn. constructor. eapply IHHeuttEv; eauto.
    + exfalso. symmetry in Heq. apply simpobs in x. apply simpobs in Heq.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x; inv CHECK.
    + rewrite <- x0.
      symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x. pinversion x.
      subst. inj_existT; subst.
      inversion H; subst; inj_existT; subst.
      * unfold observe. cbn. unfold peel_vis.
        assert (B = B). auto.
        destruct (classicT (B = B) ); try contradiction.
        unfold eq_rect_r, eq_rect. 
        remember (eq_sym e) as He. clear HeqHe.
        dependent destruction He. cbn. constructor; eauto.
        intros. inversion H2. subst; inj_existT; subst.
        apply H0 in H2. pclearbot. unfold id. right. eapply CIH.
        enough (k2 b0 ≈ ITree.bind (k b0) f ).
        { rewrite <- H3. auto. }
        red in x1. cbn in x1. inversion x1. subst; inj_existT; subst.
        symmetry. pclearbot. specialize ( REL0 b0).
        apply eq_sub_eutt. auto.
      * cbn. constructor; eauto. intros. contradiction.
Qed.
