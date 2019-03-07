Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Core.ITree.

From ITree Require Export
     Eq.Eq.

Import ITreeNotations.
Local Open Scope itree.

Section FiniteTaus.

Context {E : Type -> Type} {R : Type}.

(* [notau t] holds when [t] does not start with a [Tau]. *)
Definition notauF {I} (t : itreeF E R I) : Prop :=
  match t with
  | TauF _ => False
  | _ => True
  end.

Notation notau t := (notauF (observe t)).

(* [untaus t t'] holds when [t = Tau (... Tau t' ...)]:
   [t] steps to [t'] by "peeling off" a finite number of [Tau].
   "Peel off" means to remove only taus at the root of the tree,
   not any behind a [Vis] step). *)
Inductive untausF :
  itreeF E R (itree E R) -> itreeF E R (itree E R) -> Prop :=
| NoTau ot0 : untausF ot0 ot0
| OneTau ot t' ot0 (OBS: TauF t' = ot) (TAUS: untausF (observe t') ot0): untausF ot ot0
.
Hint Constructors untausF.

Definition unalltausF ot ot0 := untausF ot ot0 /\ notauF ot0.
Hint Unfold unalltausF.

Lemma unalltausF_untausF ot ot0 : unalltausF ot ot0 -> untausF ot ot0.
Proof. intros []; auto. Qed.
Hint Resolve unalltausF_untausF.

Lemma unalltausF_notauF ot ot0 : unalltausF ot ot0 -> notauF ot0.
Proof. intros []; auto. Qed.
Hint Resolve unalltausF_notauF.

(* [finite_taus t] holds when [t] has a finite number of taus
   to peel. *)
Definition finite_tausF ot : Prop := exists ot', unalltausF ot ot'.
Hint Unfold finite_tausF.

(** ** Lemmas *)

Lemma untaus_all ot ot' :
  untausF ot ot' -> notauF ot' -> unalltausF ot ot'.
Proof. induction 1; eauto. Qed.

Lemma unalltaus_notau ot ot' : unalltausF ot ot' -> notauF ot'.
Proof. intros. induction H; eauto. Qed.

Lemma notau_tau I (ot : itreeF E R I) (t0 : I)
  (NOTAU : notauF ot)
  (OBS: TauF t0 = ot): False.
Proof. subst. auto. Qed.
Hint Resolve notau_tau.

Lemma notau_ret I (ot: itreeF E R I) r (OBS: RetF r = ot) : notauF ot.
Proof. subst. red. eauto. Qed.
Hint Resolve notau_ret.

Lemma notau_vis I (ot : itreeF E R I) u (e: E u) k (OBS: VisF e k = ot) : notauF ot.
Proof. intros. subst. red. eauto. Qed.
Hint Resolve notau_vis.

(* If [t] does not start with [Tau], removing all [Tau] does
   nothing. Can be thought of as [notau_unalltaus] composed with
   [unalltaus_injective] (below). *)
Lemma unalltaus_notau_id ot ot' :
  unalltausF ot ot' -> notauF ot -> ot = ot'.
Proof.
  intros [[ | ]] ?; eauto. exfalso; eauto.
Qed.

(* There is only one way to peel off all taus. *)
Lemma unalltaus_injective ot ot1 ot2 :
    unalltausF ot ot1 -> unalltausF ot ot2 -> ot1 = ot2.
Proof.
  intros [Huntaus Hnotau]. revert ot2 Hnotau.
  induction Huntaus; intros; eauto using unalltaus_notau_id.
  eapply IHHuntaus; eauto.
  destruct H as [Huntaus' Hnotau'].
  destruct Huntaus'.
  + exfalso; eauto.
  + subst. inversion OBS0; subst; eauto.
Qed.

(* Adding a [Tau] to [t1] then peeling them all off produces
   the same result as peeling them all off from [t1]. *)
Lemma unalltaus_tau t ot1 ot2
    (OBS: TauF t = ot1)
    (TAUS: unalltausF ot1 ot2):
  unalltausF (observe t) ot2.
Proof.
  destruct TAUS as [Huntaus Hnotau].
  destruct Huntaus.
  - exfalso; eauto.
  - subst; inversion OBS0; subst; eauto.
Qed.

Lemma unalltaus_tau' t ot1 ot2
    (OBS: TauF t = ot1)
    (TAUS: unalltausF (observe t) ot2):
  unalltausF ot1 ot2.
Proof.
  destruct TAUS as [Huntaus Hnotau].
  subst. eauto.
Qed.

Lemma notauF_untausF ot1 ot2
      (NOTAU : notauF ot1)
      (UNTAUS : untausF ot1 ot2) : ot1 = ot2.
Proof.
  destruct UNTAUS; eauto.
  exfalso; eauto.
Qed.

Definition untausF_shift (t1 t2 : itree E R) :
  untausF (TauF t1) (TauF t2) -> untausF (observe t1) (observe t2).
Proof.
  intros H.
  inversion H; subst.
  { constructor. }
  clear H.
  inversion OBS; subst; clear OBS.
  remember (observe t1) as ot1.
  remember (TauF t2) as tt2.
  generalize dependent t1.
  generalize dependent t2.
  induction TAUS; intros; subst; econstructor; eauto.
Qed.

Definition untausF_trans (t1 t2 t3 : itreeF E R _) :
  untausF t1 t2 -> untausF t2 t3 -> untausF t1 t3.
Proof.
  induction 1; auto.
  subst; econstructor; auto.
Qed.

Definition untausF_strong_ind
           (P : itreeF E R _ -> Prop)
           (ot1 ot2 : itreeF E R _)
           (Huntaus : untausF ot1 ot2)
           (Hnotau : notauF ot2)
           (STEP : forall ot1
               (Huntaus : untausF ot1 ot2)
               (IH: forall t1' oti
                     (NEXT: ot1 = TauF t1')
                     (UNTAUS: untausF (observe t1') oti),
                   P oti),
               P ot1)
  : P ot1.
Proof.
  enough (H : forall oti,
             untausF ot1 oti ->
             untausF oti ot2 ->
             P oti
         ).
  { apply H; eauto. }
  revert STEP.
  induction Huntaus; intros; subst.
  - eapply STEP; eauto.
    intros; subst. dependent destruction H; inv Hnotau.
  - destruct H0; auto.
    subst. apply STEP; eauto.
    intros. inv NEXT.
    apply IHHuntaus; eauto.
    + clear -H UNTAUS.
      remember (TauF t') as ott'. remember (TauF t1') as ott1'.
      move H at top. revert_until H. induction H; intros; subst.
      * inv Heqott1'. eauto.
      * inv Heqott'. dependent destruction H; eauto.
    + genobs t1' ot1'. revert UNTAUS. clear -Hnotau H0. induction H0; intros.
      * dependent destruction UNTAUS; eauto.
        subst. simpobs. inv Hnotau.
      * subst. dependent destruction UNTAUS; eauto.
Qed.

(* If [t] does not start with [Tau], then it starts with finitely
   many [Tau]. *)
Lemma notau_finite_taus ot : notauF ot -> finite_tausF ot.
Proof. eauto. Qed.

(* [Vis] and [Ret] start with no taus, of course. *)
Lemma finite_taus_ret ot (r : R) (OBS: RetF r = ot) : finite_tausF ot.
Proof. eauto 10. Qed.

Lemma finite_taus_vis {u} ot (e : E u) (k : u -> itree E R) (OBS: VisF e k = ot):
  finite_tausF ot.
Proof. eauto 10. Qed.

(* [finite_taus] is preserved by removing or adding one [Tau]. *)
Lemma finite_taus_tau t':
  finite_tausF (TauF t') <-> finite_tausF (observe t').
Proof.
  split; intros [? [Huntaus Hnotau]]; eauto 10.
  inv Huntaus.
  - contradiction.
  - inv OBS; eauto.
Qed.

(* (* [finite_taus] is preserved by removing or adding any finite *)
(*    number of [Tau]. *) *)
Lemma untaus_finite_taus ot ot':
    untausF ot ot' -> (finite_tausF ot <-> finite_tausF ot').
Proof.
  induction 1; intros; subst.
  - reflexivity.
  - erewrite finite_taus_tau; eauto.
Qed.

Lemma untaus_untaus : forall (ot1 ot2 ot3: itreeF E R _),
    untausF ot1 ot2 -> untausF ot2 ot3 -> untausF ot1 ot3.
Proof.
  intros t1 t2 t3. induction 1; simpl; eauto.
Qed.

Lemma untaus_unalltaus_rev (ot1 ot2 ot3: itreeF E R _) :
    untausF ot1 ot2 -> unalltausF ot1 ot3 -> unalltausF ot2 ot3.
Proof.
  intros H. revert ot3.
  induction H; intros.
  - eauto with arith.
  - destruct H0 as [Huntaus Hnotau].
    destruct Huntaus.
    + exfalso; eauto.
    + inv OBS0. inversion H0; subst; eauto.
Qed.

Lemma unalltausF_ret : forall x (t: itree' E R),
    unalltausF (RetF x) t -> t = RetF x.
Proof.
  intros x t [UNT NOT]; inversion UNT; subst; clear UNT; [reflexivity | easy].
Qed.

Lemma unalltausF_vis {S}: forall e (k: S -> itree E R) (t: itree' E R),
    unalltausF (VisF e k) t -> t = VisF e k.
Proof.
  intros e k t [UNT NOT]; inversion UNT; subst; clear UNT; [reflexivity | easy].
Qed.

End FiniteTaus.

Arguments untaus_unalltaus_rev : clear implicits.

Hint Resolve unalltausF_notauF.
Hint Resolve unalltausF_untausF.

Hint Constructors untausF.
Hint Unfold unalltausF.
Hint Unfold finite_tausF.
Hint Resolve notau_ret.
Hint Resolve notau_vis.
Hint Resolve notau_tau.

Notation finite_taus t := (finite_tausF (observe t)).
Notation untaus t t' := (untausF (observe t) (observe t')).
Notation unalltaus t t' := (unalltausF (observe t) (observe t')).

Ltac auto_untaus :=
  repeat match goal with
  | [ H1 : notauF ?X, H2 : unalltausF ?X ?Y |- _ ] =>
    assert_fails (unify X Y);
    replace Y with X in * by apply (unalltaus_notau_id _ _ H2 H1)
  | [ H1 : unalltausF ?X ?Y, H2 : unalltausF ?X ?Z |- _ ] =>
    assert_fails (unify Y Z);
    replace Z with Y in * by apply (unalltaus_injective _ _ _ H1 H2)
  end; auto.

Section NOTAU.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).


(* Equivalence between visible steps of computation (i.e., [Vis] or
   [Ret], parameterized by a relation [euttE] between continuations
   in the [Vis] case. *)
Variant eq_notauF {I J} (euttE : I -> J -> Prop)
: itreeF E R1 I -> itreeF E R2 J -> Prop :=
| Eutt_ret : forall r1 r2,
    RR r1 r2 ->
    eq_notauF euttE (RetF r1) (RetF r2)
| Eutt_vis : forall u (e : E u) k1 k2,
    (forall x, euttE (k1 x) (k2 x)) ->
    eq_notauF euttE (VisF e k1) (VisF e k2).
Hint Constructors eq_notauF.

(* Paco takes the greatest fixpoints of monotone relations. *)

Lemma monotone_eq_notauF : forall I J (r r' : I -> J -> Prop) x1 x2
      (IN: eq_notauF r x1 x2)
      (LE: r <2= r'),
    eq_notauF r' x1 x2.
Proof. pmonauto. Qed.
Hint Resolve monotone_eq_notauF.

Lemma eq_notauF_vis_inv1 {I J} {euttE : I -> J -> Prop} {U}
  ot (e : E U) k :
  eq_notauF euttE ot (VisF e k) ->
  exists k',
    ot = VisF e k' /\ (forall x, euttE (k' x) (k x)).
Proof.
  intros. remember (VisF e k) as t.
  inversion H; subst; try discriminate.
  inversion H2; subst; auto_inj_pair2; subst; eauto.
Qed.


Lemma eq_unalltaus (t1 : itree E R1) (t2 : itree E R2) ot1'
    (FT: unalltausF (observe t1) ot1')
    (EQV: eq_itree RR t1 t2) :
  exists ot2', unalltausF (observe t2) ot2'.
Proof.
  genobs t1 ot1. revert t1 Heqot1 t2 EQV.
  destruct FT as [Huntaus Hnotau].
  induction Huntaus; intros; punfold EQV; unfold_eq_itree; subst.
  - eexists. constructor; eauto. inv EQV; simpl; eauto.
  - inv EQV; simpobs; try inv Heqot1.
    pclearbot. edestruct IHHuntaus as [? []]; eauto.
Qed.

Lemma eq_unalltaus_eqF (t : itree E R1) (s : itree E R2) ot'
    (UNTAUS : unalltausF (observe t) ot')
    (EQV: eq_itree RR t s) :
  exists os', unalltausF (observe s) os' /\ eq_itreeF RR (eq_itree RR) ot' os'.
Proof.
  destruct UNTAUS as [Huntaus Hnotau].
  remember (observe t) as ot. revert s t Heqot EQV.
  induction Huntaus; intros; punfold EQV; unfold_eq_itree.
  - eexists (observe s). split.
    inv EQV; simpobs; eauto.
    subst; eauto.
    eapply eq_itreeF_mono; eauto.
    intros ? ? [| []]; eauto.
  - inv EQV; simpobs; inversion Heqot; subst.
    destruct REL as [| []].
    edestruct IHHuntaus as [? [[]]]; eauto 10.
Qed.

Lemma eq_unalltaus_eq (t : itree E R1) (s : itree E R2) t'
    (UNTAUS : unalltausF (observe t) (observe t'))
    (EQV: eq_itree RR t s) :
  exists s', unalltausF (observe s) (observe s') /\ eq_itree RR t' s'.
Proof.
  eapply eq_unalltaus_eqF in UNTAUS; try eassumption.
  destruct UNTAUS as [os' []]. eexists (go os'); split; eauto.
  pfold. eapply eq_itreeF_mono; eauto.
Qed.

End NOTAU.

Hint Resolve monotone_eq_notauF.
Hint Constructors eq_notauF.

(** *** [eq_notauF] lemmas *)

Lemma eq_notauF_and {E R1 R2} (RR : R1 -> R2 -> Prop) {I J}
        (euttE1 euttE2 euttE : I -> J -> Prop) :
  (forall t1 t2, euttE1 t1 t2 -> euttE2 t1 t2 -> euttE t1 t2) ->
  forall (ot1 : itreeF E R1 I) (ot2 : itreeF E R2 J),
    eq_notauF RR euttE1 ot1 ot2 -> eq_notauF RR euttE2 ot1 ot2 ->
    eq_notauF RR euttE ot1 ot2.
Proof.
  intros ? ? ? [] Hen2; inversion Hen2; auto.
  auto_inj_pair2; subst; auto.
Qed.

Lemma eq_notauF_flip {E R1 R2} (RR : R1 -> R2 -> Prop) {I J}
      (euttE : I -> J -> Prop) :
  forall (ot1 : itreeF E R1 I) (ot2 : itreeF E R2 J),
    eq_notauF (flip RR) (flip euttE) ot2 ot1 ->
    eq_notauF RR euttE ot1 ot2.
Proof.
  intros ? ? []; auto.
Qed.

Delimit Scope euttE_scope with euttE.

(** ** Generalized symmetry and transitivity *)

Lemma Symmetric_eq_notauF_ {E R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      {I J} (r1 : I -> J -> Prop) (r2 : J -> I -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i)
      (ot1 : itreeF E R1 I) (ot2 : itreeF E R2 J) :
  eq_notauF RR1 r1 ot1 ot2 ->
  eq_notauF RR2 r2 ot2 ot1.
Proof. intros []; auto. Qed.

Lemma Transitive_eq_notauF_ {E R1 R2 R3}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      (RR3 : R1 -> R3 -> Prop)
      {I J K} (r1 : I -> J -> Prop) (r2 : J -> K -> Prop)
      (r3 : I -> K -> Prop)
      (TRANS_RR : forall r1 r2 r3, RR1 r1 r2 -> RR2 r2 r3 -> RR3 r1 r3)
      (TRANS_r : forall i j k, r1 i j -> r2 j k -> r3 i k)
      (ot1 : itreeF E R1 I) ot2 ot3 :
  eq_notauF RR1 r1 ot1 ot2 ->
  eq_notauF RR2 r2 ot2 ot3 ->
  eq_notauF RR3 r3 ot1 ot3.
Proof.
  intros [] I2; inversion I2; eauto.
  auto_inj_pair2; subst; eauto.
Qed.

Section NOTAU_rel.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

(* Reflexivity of [eq_notauF], modulo a few assumptions. *)
Lemma Reflexive_eq_notauF `{Reflexive _ RR} I (eq_ : I -> I -> Prop) :
  Reflexive eq_ ->
  forall (ot : itreeF E R I), notauF ot -> eq_notauF RR eq_ ot ot.
Proof.
  intros. destruct ot; try contradiction; econstructor; intros; subst; eauto.
Qed.

Global Instance Symmetric_eq_notauF `{Symmetric _ RR} I (eq_ : I -> I -> Prop) :
  Symmetric eq_ -> Symmetric (@eq_notauF E _ _ RR _ _ eq_).
Proof.
  repeat intro. eapply Symmetric_eq_notauF_; eauto.
Qed.

Global Instance Transitive_eq_notauF `{Transitive _ RR} I (eq_ : I -> I -> Prop) :
  Transitive eq_ -> Transitive (@eq_notauF E _ _ RR _ _ eq_).
Proof.
  repeat intro. eapply Transitive_eq_notauF_; eauto.
Qed.

End NOTAU_rel.

Global Instance eq_itree_notauF {E R} :
  Proper (going (@eq_itree E R _ eq) ==> flip impl) notauF.
Proof.
  intros ? ? [] ?; punfold H. inv H; simpl in *; subst; eauto.
Qed.

Lemma untaus_bind {E S R} : forall t t' (k: S -> itree E R)
      (UNTAUS: untausF (observe t) (observe t')),
  untausF (observe (ITree.bind t k)) (observe (ITree.bind t' k)).
Proof.
  intros. genobs t ot; genobs t' ot'. revert t Heqot t' Heqot'.
  induction UNTAUS; intros; subst.
  - rewrite !unfold_bind; simpobs; eauto.
  - rewrite unfold_bind. simpobs. cbn. eauto.
Qed.

Lemma untaus_bindF {E S R} : forall t t' (k: S -> itree E R)
      (UNTAUS: untausF (observe t) t'),
  untausF (observe (ITree.bind t k)) (observe (ITree.bind (go t') k)).
Proof.
  intros; eapply untaus_bind; eauto.
Qed.

Lemma finite_taus_bind_fst {E R S}
      (t : itree E R) (f : R -> itree E S) :
  finite_taus (ITree.bind t f) -> finite_taus t.
Proof.
  intros [tf' [TAUS PROP]].
  genobs (ITree.bind t f) obtf. move TAUS at top. revert_until TAUS.
  induction TAUS; intros; subst.
  - rewrite unfold_bind in PROP.
    genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
  - genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
    rewrite unfold_bind in Heqobtf. simpobs. inv Heqobtf.
    eapply finite_taus_tau; eauto.
Qed.

Lemma finite_taus_bind {E R S}
      (t : itree E R) (f : R -> itree E S)
      (FINt: finite_tausF (observe t))
      (FINk: forall v, finite_tausF (observe (f v))):
  finite_tausF (observe (ITree.bind t f)).
Proof.
  rewrite unfold_bind.
  genobs t ot. clear Heqot t.
  destruct FINt as [ot' [UNT NOTAU]].
  induction UNT; subst.
  - destruct ot0; inv NOTAU; simpl; eauto 7.
  - apply finite_taus_tau. eauto.
Qed.
