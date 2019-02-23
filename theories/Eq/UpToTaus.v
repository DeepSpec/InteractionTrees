(* Equivalence up to taus *)
(* We consider tau as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many taus between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. The main consequence of this
   choice is that equivalence up to taus is an equivalence relation.
 *)

(* TODO:
   - Generalize Reflexivity, Symmetry, Transitivity to heterogeneous
     eutt.
   - Make eutt a notation instead of a definition?
 *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import Core Eq.Eq.

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

Section EUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(* Equivalence between visible steps of computation (i.e., [Vis] or
   [Ret], parameterized by a relation [eutt] between continuations
   in the [Vis] case. *)
Variant eq_notauF {I J} (eutt : I -> J -> Prop)
: itreeF E R1 I -> itreeF E R2 J -> Prop :=
| Eutt_ret : forall r1 r2,
    RR r1 r2 ->
    eq_notauF eutt (RetF r1) (RetF r2)
| Eutt_vis : forall u (e : E u) k1 k2,
    (forall x, eutt (k1 x) (k2 x)) ->
    eq_notauF eutt (VisF e k1) (VisF e k2).
Hint Constructors eq_notauF.

(*
Variant eq_notauF' {I} (eutt : relation I)
: relation (itreeF E R I) :=
| Eutt_ret' : forall r, eq_notauF' eutt (RetF r) (RetF r)
| Eutt_vis' : forall {u1 u2} (e1 : E u1) (e2 : E u2) k1 k2,
    eq_dep _ E _ e1 _ e2 ->
    (forall x1 x2, JMeq x1 x2 -> eutt (k1 x1) (k2 x2)) ->
    eq_notauF' eutt (VisF e1 k1) (VisF e2 k2).
Hint Constructors eq_notauF'.

Lemma eq_notauF_eq_eq_notauF': forall I (eutt : relation I) t s,
  eq_notauF eutt t s <-> eq_notauF' eutt t s.
Proof.
  split; intros EUTT; destruct EUTT; eauto.
  - econstructor; intros; subst; eauto.
  - assert (u1 = u2) by (inv H; eauto).
    subst. apply eq_dep_eq in H. subst. eauto.
Qed.
*)

(* [eutt_ eutt t1 t2] means that, if [t1] or [t2] ever takes a
   visible step ([Vis] or [Ret]), then the other takes the same
   step, and the subsequent continuations (in the [Vis] case) are
   related by [eutt]. In particular, [(t1 = spin)%eq_itree] if
   and only if [(t2 = spin)%eq_itree]. Note also that in that
   case, the parameter [eutt] is irrelevant.

   This is the relation we will take a fixpoint of. *)
Inductive euttF (eutt : itree E R1 -> itree E R2 -> Prop)
          (ot1 : itreeF E R1 (itree E R1))
          (ot2 : itreeF E R2 (itree E R2)) : Prop :=
| euttF_ (FIN: finite_tausF ot1 <-> finite_tausF ot2)
         (EQV: forall ot1' ot2'
                  (UNTAUS1: unalltausF ot1 ot1')
                  (UNTAUS2: unalltausF ot2 ot2'),
               eq_notauF eutt ot1' ot2')
.
Hint Constructors euttF.

Definition eutt_ (eutt : itree E R1 -> itree E R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) : Prop :=
  euttF eutt (observe t1) (observe t2).
Hint Unfold eutt_.

(* Paco takes the greatest fixpoints of monotone relations. *)

Lemma monotone_eq_notauF : forall I J (r r' : I -> J -> Prop) x1 x2
      (IN: eq_notauF r x1 x2)
      (LE: r <2= r'),
    eq_notauF r' x1 x2.
Proof. pmonauto. Qed.
Hint Resolve monotone_eq_notauF.

(* [eutt_] is monotone. *)
Lemma monotone_eutt_ : monotone2 eutt_.
Proof. pmonauto. Qed.
Hint Resolve monotone_eutt_ : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition eutt : itree E R1 -> itree E R2 -> Prop := paco2 eutt_ bot2.

Global Arguments eutt t1%itree t2%itree.

Infix "≈" := eutt (at level 70) : itree_scope.

(* Lemmas about the auxiliary relations. *)

(* Many have a name [X_Y] to represent an implication
   [X _ -> Y _] (possibly with more arguments on either side). *)

(**)

Lemma euttF_tau r t1 t2 t1' t2'
    (OBS1: TauF t1' = observe t1)
    (OBS2: TauF t2' = observe t2)
    (REL: eutt_ r t1' t2'):
  eutt_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - simpobs. rewrite !finite_taus_tau. eauto.
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
Qed.

Lemma euttF_tau_left r t1 t2 t1'
    (OBS: TauF t1 = observe t1')
    (REL: eutt_ r t1' t2):
  eutt_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - rewrite <- FIN. symmetry. rewrite <- OBS. rewrite <- finite_taus_tau; eauto. reflexivity.
  - intros. eapply EQV; eauto. rewrite <- OBS. inversion UNTAUS1. constructor; auto.
    econstructor; eauto.
Qed.

Lemma euttF_tau_right r t1 t2 t2'
    (OBS: TauF t2 = observe t2')
    (REL: eutt_ r t1 t2'):
  eutt_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - rewrite FIN. rewrite <- OBS. rewrite <- finite_taus_tau; eauto. reflexivity.
  - intros. eapply EQV; eauto. rewrite <- OBS. inversion UNTAUS2. constructor; auto.
    econstructor; eauto.
Qed.

Lemma euttF_vis {u} (r : _ -> _ -> Prop) t1 t2 (e : _ u) k1 k2
    (OBS1: VisF e k1 = observe t1)
    (OBS2: VisF e k2 = observe t2)
    (REL: forall x, r (k1 x) (k2 x)):
  eutt_ r t1 t2.
Proof.
  intros. econstructor.
  - split; intros; eapply notau_finite_taus; eauto.
  - intros.
    apply unalltaus_notau_id in UNTAUS1; eauto.
    apply unalltaus_notau_id in UNTAUS2; eauto.
    simpobs. subst. eauto.
Qed.

(**)

Lemma eutt_strengthen :
  forall r (t1 : itree E R1) (t2 : itree E R2)
     (FIN: finite_taus t1 <-> finite_taus t2)
     (EQV: forall t1' t2'
              (UNT1: unalltaus t1 t1')
              (UNT2: unalltaus t2 t2'),
         paco2 (eutt_ ∘ gres2 eutt_) r t1' t2'),
    paco2 (eutt_ ∘ gres2 eutt_) r t1 t2.
Proof.
  intros. pfold. econstructor; eauto.
  intros.
  hexploit (EQV (go ot1') (go ot2')); eauto.
  intros EQV'. punfold EQV'. destruct EQV'.
  eapply EQV0;
    repeat constructor; eauto.
Qed.

(**)

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

Lemma eutt_Ret x y :
  RR x y -> eutt (Ret x) (Ret y).
Proof.
  intros; pfold.
  constructor.
  split; intros; eapply finite_taus_ret; reflexivity.
  intros.
  apply unalltausF_ret in UNTAUS1.
  apply unalltausF_ret in UNTAUS2.
  subst; constructor; assumption.
Qed.

Lemma eutt_Vis {U} (e: E U) k k' :
  (forall x, eutt (k x) (k' x)) ->
  eutt (Vis e k) (Vis e k').
Proof.
  intros.
  pfold; constructor.
  split; intros; eapply finite_taus_vis; reflexivity.
  intros.
  cbn in *.
  apply unalltausF_vis in UNTAUS1.
  apply unalltausF_vis in UNTAUS2.
  subst; constructor.
  intros x; specialize (H x).
  punfold H.
Qed.

End EUTT.

Hint Constructors eq_notauF.
Hint Constructors euttF.
Hint Resolve monotone_eutt_ : paco.

Delimit Scope eutt_scope with eutt.

Section EUTT_rel.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

(* Reflexivity of [eq_notauF], modulo a few assumptions. *)
Lemma Reflexive_eq_notauF `{Reflexive _ RR} I (eq_ : I -> I -> Prop) (ot : itreeF E R I) :
  Reflexive eq_ -> notauF ot -> eq_notauF RR eq_ ot ot.
Proof.
  intros. destruct ot; try contradiction; econstructor; intros; subst; eauto.
Qed.

Global Instance subrelation_eq_eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt RR).
Proof.
  pcofix CIH. intros.
  pfold. econstructor.
  { split; [|apply flip_eq_itree in H0]; intros; destruct H as [n [? ?]]; eauto using eq_unalltaus. }

  intros. eapply eq_unalltaus_eqF in H0; eauto. destruct H0 as [s' [UNTAUS' EQV']].
  hexploit @unalltaus_injective; [apply UNTAUS' | apply UNTAUS2 | intro X]; subst.
  inv EQV'; simpobs; eauto.
  eapply unalltaus_notau in UNTAUS1. contradiction.
Qed.

End EUTT_rel.

Section EUTT_eq.

Context {E : Type -> Type} {R : Type}.

Global Instance Reflexive_euttF
       {RR : R -> R -> Prop} `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive r -> Reflexive (euttF RR r).
Proof.
  split.
  - reflexivity.
  - intros.
    erewrite (unalltaus_injective _ _ _ UNTAUS1 UNTAUS2).
    apply Reflexive_eq_notauF; eauto.
Qed.

Global Instance Reflexive_eutt
       {RR : R -> R -> Prop} `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (paco2 (eutt_ RR) r).
Proof.
  pcofix CIH.
  intros. pfold. red. apply Reflexive_euttF; eauto.
Qed.

Let eutt : itree E R -> itree E R -> Prop := eutt eq.

Infix "≈" := eutt (at level 70) : itree_scope.

Global Instance Symmetric_eutt (r : itree E R -> itree E R -> Prop)
         (Sr : Symmetric r) :
  Symmetric (paco2 (eutt_ eq) r).
Proof.
  pcofix Symmetric_eutt.
  intros t1 t2 H12.
  punfold H12.
  pfold.
  destruct H12 as [I12 H12].
  split.
  - symmetry; assumption.
  - intros. hexploit H12; eauto. intros.
    inv H; eauto.
    econstructor. intros. destruct (H0 x); eauto.
Qed.

Global Instance Transitive_eutt : Transitive eutt.
Proof.
  pcofix Transitive_eutt.
  intros t1 t2 t3 H12 H23.
  punfold H12.
  punfold H23.
  pfold.
  destruct H12 as [I12 H12].
  destruct H23 as [I23 H23].
  split.
  - etransitivity; eauto.
  - intros t1' t3' H1 H3.
    destruct I12 as [I1 I2].
    destruct I1 as [n2' [t2' TAUS2]]; eauto.
    hexploit H12; eauto. intros REL1.
    hexploit H23; eauto. intros REL2.
    destruct REL1; inversion REL2; clear REL2.
    + subst; eauto.
    + auto_inj_pair2; subst.
      econstructor; auto. intros.
      specialize (H x); specialize (H6 x). pclearbot. eauto.
Qed.

(**)

(* [eutt] is preserved by removing one [Tau]. *)
Lemma tauF_eutt (t t': itree E R) (OBS: TauF t' = observe t): t ≈ t'.
Proof.
  pfold. split.
  - simpobs. rewrite finite_taus_tau. reflexivity.
  - intros t1' t2' H1 H2.
    eapply unalltaus_tau in H1; eauto.
    assert (X := unalltaus_injective _ _ _ H1 H2).
    subst; apply Reflexive_eq_notauF; eauto.
    left. apply Reflexive_eutt.
Qed.

Lemma tau_eutt (t: itree E R) : Tau t ≈ t.
Proof.
  eapply tauF_eutt. eauto.
Qed.

(* [eutt] is preserved by removing all [Tau]. *)
Lemma untaus_eutt (t t' : itree E R) : untausF (observe t) (observe t') -> t ≈ t'.
Proof.
  intros H.
  pfold. split.
  - eapply untaus_finite_taus; eauto.
  - induction H; intros.
    + rewrite (unalltaus_injective _ _ _ UNTAUS1 UNTAUS2).
      apply Reflexive_eq_notauF; eauto.
      left; apply Reflexive_eutt.
    + eapply unalltaus_tau in UNTAUS1; eauto.
Qed.

(* We can now rewrite with [eutt] equalities. *)
Global Instance Equivalence_eutt : @Equivalence (itree E R) eutt.
Proof. constructor; typeclasses eauto. Qed.

(**)

Global Instance eutt_go : Proper (go_sim eutt ==> eutt) go.
Proof. repeat intro; eauto. Qed.

Global Instance eutt_observe : Proper (eutt ==> go_sim eutt) observe.
Proof.
  repeat intro. punfold H. pfold. destruct H. econstructor; eauto.
Qed.

Global Instance eutt_tauF : Proper (eutt ==> go_sim eutt) (fun t => TauF t).
Proof.
  repeat intro. pfold. punfold H.
  destruct H. econstructor.
  - split; intros; simpl.
    + rewrite finite_taus_tau, <-FIN, <-finite_taus_tau; eauto.
    + rewrite finite_taus_tau, FIN, <-finite_taus_tau; eauto.
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
Qed.

Global Instance eutt_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> go_sim eutt) (VisF e).
Proof.
  repeat intro. red in H. pfold. econstructor.
  - repeat econstructor.
  - intros.
    destruct UNTAUS1 as [UNTAUS1 Hnotau1].
    destruct UNTAUS2 as [UNTAUS2 Hnotau2].
    dependent destruction UNTAUS1.
    dependent destruction UNTAUS2. simpobs.
    econstructor; intros; left; apply H.
Qed.

Global Instance eq_itree_notauF :
  Proper (go_sim (@eq_itree E R _ eq) ==> flip impl) notauF.
Proof.
  repeat intro. punfold H. inv H; simpl in *; subst; eauto.
Qed.

(* If [t1] and [t2] are equivalent, then either both start with
   finitely many taus, or both [spin]. *)
Global Instance eutt_finite_taus :
  Proper (go_sim eutt ==> flip impl) finite_tausF.
Proof.
  repeat intro. punfold H. eapply H. eauto.
Qed.

Inductive eutt_trans_clo (r: itree E R -> itree E R -> Prop) :
  itree E R -> itree E R -> Prop :=
| eutt_pre_clo_intro (t1 t2 t3 t4: itree E R)
      (EQVl: t1 ≈ t2)
      (EQVr: t4 ≈ t3)
      (REL: r t2 t3)
  : eutt_trans_clo r t1 t4
.
Hint Constructors eutt_trans_clo.

Lemma eutt_clo_trans : weak_respectful2 (eutt_ eq) eutt_trans_clo.
Proof.
  econstructor; [pmonauto|].
  intros. inv PR.
  punfold EQVl. punfold EQVr. destruct EQVl, EQVr. split.
  { rewrite FIN, FIN0. apply GF in REL. destruct REL. eauto. }

  intros. apply proj1 in FIN. edestruct FIN as [n'' [t2'' TAUS'']]; [eexists; eauto|].
  hexploit EQV; eauto. intros EUTT1.
  apply proj1 in FIN0. edestruct FIN0 as [n''' [t2''' TAUS''']]; [eexists; eauto|].
  hexploit EQV0; eauto. intros EUTT2.
  apply GF in REL. destruct REL.
  hexploit EQV1; eauto. intros EUTT3.
  destruct EUTT1; destruct EUTT2;
    try (solve [subst; inversion EUTT3; auto]).
  remember (VisF _ _) as o2 in EUTT3.
  remember (VisF _ _) as o3 in EUTT3.
  inversion EUTT3; subst; try discriminate.
  inversion H2; clear H2; inversion H3; clear H3.
  subst; auto_inj_pair2; subst.
  econstructor. intros.
  specialize (H x); specialize (H0 x); specialize (H1 x).
  pclearbot. eauto using rclo2.
Qed.

End EUTT_eq.

Arguments eutt_clo_trans : clear implicits.

Hint Constructors eutt_trans_clo.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

(**)

Lemma eutt_tau {E R1 R2} (RR : R1 -> R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) :
  eutt RR t1 t2 -> eutt RR (Tau t1) (Tau t2).
Proof.
  intros H. 
  pfold. eapply euttF_tau. reflexivity. reflexivity. punfold H.
Qed.

Lemma eq_itree_vis {E R1 R2} (RR : R1 -> R2 -> Prop)
      {U} (e : E U) (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
  (forall u, eq_itree RR (k1 u) (k2 u)) ->
  eq_itree RR (Vis e k1) (Vis e k2).
Proof.
  intros; pfold; constructor; left. apply H.
Qed.

Lemma eq_itree_ret {E R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  RR r1 r2 -> @eq_itree E _ _ RR (Ret r1) (Ret r2).
Proof.
  intros; pfold; eauto; constructor; auto.
Qed.

(* Lemmas about [bind]. *)

Lemma untaus_bind {E S R} : forall t t' (k: S -> itree E R)
      (UNTAUS: untausF (observe t) (observe t')),
  untausF (observe (ITree.bind t k)) (observe (ITree.bind t' k)).
Proof.
  intros. genobs t ot; genobs t' ot'. revert t Heqot t' Heqot'.
  induction UNTAUS; intros; subst.
  - rewrite !bind_unfold; simpobs; eauto.
  - rewrite bind_unfold. simpobs. cbn. eauto.
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
  - rewrite bind_unfold in PROP.
    genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
  - genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
    rewrite bind_unfold in Heqobtf. simpobs. inv Heqobtf. unfold_bind.
    eapply finite_taus_tau; eauto.
Qed.

Lemma finite_taus_bind {E R S}
      (t : itree E R) (f : R -> itree E S)
      (FINt: finite_tausF (observe t))
      (FINk: forall v, finite_tausF (observe (f v))):
  finite_tausF (observe (ITree.bind t f)).
Proof.
  rewrite bind_unfold.
  genobs t ot. clear Heqot t.
  destruct FINt as [ot' [UNT NOTAU]].
  induction UNT; subst.
  - destruct ot0; inv NOTAU; simpl; eauto 7.
  - apply finite_taus_tau. eauto.
Qed.

Inductive eutt_bind_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| eutt_bind_clo_intro U (t1 t2: itree E U) k1 k2
      (EQV: t1 ≈ t2)
      (REL: forall v, r (k1 v) (k2 v))
  : eutt_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eutt_bind_clo.

Lemma bind_clo_finite_taus E U R (t1 t2: itree E U) (k1 k2: U -> itree E R)
    (FT: finite_taus (ITree.bind t1 k1))
    (FTk: forall v, finite_taus (k1 v) -> finite_taus (k2 v))
    (EQV: t1 ≈ t2):
  finite_taus (ITree.bind t2 k2).
Proof.
  punfold EQV. destruct EQV as [[FTt _] EQV].
  assert (FT1 := FT). apply finite_taus_bind_fst in FT1.
  assert (FT2 := FT1). apply FTt in FT2.
  destruct FT1 as [a [FT1 NT1]], FT2 as [b [FT2 NT2]].
  rewrite @untaus_finite_taus in FT; [|eapply untaus_bindF, FT1].
  rewrite bind_unfold. genobs t2 ot2. clear Heqot2 t2.
  induction FT2.
  - destruct ot0; inv NT2; simpl; eauto 7.
    hexploit EQV; eauto. intros EQV'. inv EQV'.
    rewrite bind_unfold in FT. eauto.
  - subst. eapply finite_taus_tau; eauto.
    eapply IHFT2; eauto using unalltaus_tau'.
Qed.

Lemma eutt_clo_bind E R: weak_respectful2 (@eutt_ E R _ eq) eutt_bind_clo.
Proof.
  econstructor; [pmonauto|].
  intros. destruct PR. split.
  - assert (EQV':=EQV). symmetry in EQV'.
    split; intros; eapply bind_clo_finite_taus; eauto; intros.
    + edestruct GF; eauto. apply FIN. eauto.
    + edestruct GF; eauto. apply FIN. eauto.
  - punfold EQV. destruct EQV.
    intros.
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS1|]. intros [a FT1].
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS2|]. intros [b FT2].
    specialize (EQV _ _ FT1 FT2).
    destruct FT1 as [FT1 Hnotau1]. destruct FT2 as [FT2 Hnotau2].
    hexploit @untaus_bindF; [ eapply FT1 | ]. intros UT1.
    hexploit @untaus_bindF; [ eapply FT2 | ]. intros UT2.
    hexploit @untaus_unalltaus_rev; [apply UT1| |]. eauto. intros UAT1.
    hexploit @untaus_unalltaus_rev; [apply UT2| |]; eauto. intros UAT2.
    inv EQV.
    + rewrite bind_unfold in UAT1, UAT2. simpobs. cbn in *.
      eapply GF in REL. destruct REL.
      eapply monotone_eq_notauF; eauto using rclo2.
    + rewrite bind_unfold in UAT1, UAT2. simpobs. cbn in *.
      destruct UAT1 as [UAT1 _]. destruct UAT2 as [UAT2 _].
      dependent destruction UAT1. dependent destruction UAT2. simpobs.
      econstructor. intros. specialize (H x). pclearbot. fold_bind. eauto using rclo2.
Qed.

(* [eutt] is a congruence wrt. [bind] *)

Global Instance eutt_bind {E R S} :
  Proper (eutt eq ==>
          pointwise_relation _ (eutt eq) ==>
          eutt eq) (@ITree.bind E R S).
Proof.
  repeat intro. pupto2_init.
  pupto2 eutt_clo_bind. econstructor; eauto.
  intros. pupto2_final. apply H0.
Qed.

Global Instance eutt_paco {E R} r:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (paco2 (@eutt_ E R _ eq ∘ gres2 (eutt_ eq)) r).
Proof.
  repeat intro. pupto2 eutt_clo_trans. eauto.
Qed.

Global Instance eutt_gres {E R} r:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (gres2 (@eutt_ E R _ eq) r).
Proof.
  repeat intro. pupto2 eutt_clo_trans. eauto.
Qed.

Global Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt eq ==> eutt eq) (@ITree.map E R S).
Proof.
  unfold ITree.map. repeat red.
  intros; eapply eutt_bind; eauto.
  intro. rewrite H. reflexivity.
Qed.

Global Instance eutt_forever {E R S} :
  Proper (eutt eq ==> eutt eq) (@ITree.forever E R S).
Proof.
Admitted.

Global Instance eutt_when {E} (b : bool) :
  Proper (eutt eq ==> eutt eq) (@ITree.when E b).
Proof.
Admitted.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt eq (ITree.map g (ITree.map f t))
          (ITree.map (fun x => g (f x)) t).
Proof.
  apply subrelation_eq_eutt, map_map.
Qed.

Global Instance eutt_eq_under_rr {E : Type -> Type}
       {R1 R2 : Type} (RR: R1 -> R2 -> Prop):
  Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> iff) (eutt RR).
Admitted.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma eutt_bind_gen {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    eutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> eutt SS (s1 r1) (s2 r2)) ->
                  @eutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Admitted.

Definition observing {E R}
           (f : itree' E R -> itree' E R -> Prop)
           (x y : itree E R) :=
  f x.(observe) y.(observe).

Inductive euttF1' {E R} (r : itree E R -> itree E R -> Prop) :
  itree' E R -> itree' E R -> Prop :=
| euttF1_Tau_L : forall t1 t2,
    euttF1' r t1.(observe) t2 ->
    euttF1' r (TauF t1) t2
| euttF1_Tau_R : forall t1 t2,
    euttF1' r t1 t2.(observe) ->
    euttF1' r t1 (TauF t2)
| euttF1_euttF0 : forall t1 t2,
    eq_notauF eq r t1 t2 ->
    euttF1' r t1 t2
.

Definition euttF1 {E R} (r : relation (itree E R)) :
  relation (itree E R) := observing (euttF1' r).

Lemma euttF1_euttF {E R} (r : relation (itree E R)) :
  forall t1 t2,
    euttF1 r t1 t2 -> eutt_ eq r t1 t2.
Proof.
Admitted.

Inductive euttF' {E R} (eutt: relation (itree E R)) (eqtaus: relation (itreeF E R _))
  : relation (itreeF E R _) :=
| euttF'_ret r : euttF' eutt eqtaus (RetF r) (RetF r)
| euttF'_vis u (e : E u) k1 k2
      (EUTTK: forall x, eutt (k1 x) (k2 x)):
    euttF' eutt eqtaus (VisF e k1) (VisF e k2)
| euttF'_tau_tau t1 t2
      (EQTAUS: eqtaus (observe t1) (observe t2)):
    euttF' eutt eqtaus (TauF t1) (TauF t2)
| euttF'_tau_left t1 ot2
      (EQTAUS: euttF' eutt eqtaus (observe t1) ot2):
    euttF' eutt eqtaus (TauF t1) ot2
| euttF'_right ot1 t2
      (EQTAUS: euttF' eutt eqtaus ot1 (observe t2)):
    euttF' eutt eqtaus ot1 (TauF t2)
.
Hint Constructors euttF'.

Definition eutt'_ {E R} eutt t1 t2 := paco2 (@euttF' E R eutt) bot2 (* (fun x y => eutt (go x) (go y)) *) (observe t1) (observe t2).
Hint Unfold eutt'_.

Definition eutt' {E R} := paco2 (@eutt'_ E R) bot2.
Hint Unfold eutt'.

Lemma euttF'_mon {E R} r r' s s' x y
    (EUTT: @euttF' E R r s x y)
    (LEr: r <2= r')
    (LEs: s <2= s'):
  euttF' r' s' x y.
Proof.
  induction EUTT; eauto.
Qed.

Lemma reflexive_euttF' {E R} eutt eqtaus (r1:Reflexive eutt) (r:Reflexive eqtaus) : Reflexive (@euttF' E R eutt eqtaus).
Proof.
  unfold Reflexive. intros x.
  destruct x; eauto.
Qed.

Lemma monotone_euttF' {E R} eutt : monotone2 (@euttF' E R eutt).
Proof. repeat intro. eauto using euttF'_mon. Qed.
Hint Resolve monotone_euttF' : paco.

Lemma monotone_eutt'_ {E R} : monotone2 (@eutt'_ E R).
Proof. red. eauto using euttF'_mon, paco2_mon_gen. Qed.
Hint Resolve monotone_eutt'_ : paco.

Lemma eutt__is_eutt'_ {E R} r (t1 t2: itree E R) :
  eutt_ eq r t1 t2 <-> eutt'_ r t1 t2.
Proof.
  split; intros.
  { revert t1 t2 H. pcofix CIH'. intros. destruct H0.
    genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
    assert (EM: notauF ot1 \/ notauF ot2 \/ ~(notauF ot1 \/ notauF ot2))
      by (destruct ot1, ot2; simpl; tauto).
    destruct EM as [EM|[EM|EM]].
    - destruct FIN as [FIN _].
      hexploit FIN; eauto 7. clear FIN; intro FIN.
      destruct FIN as [ot' [UNTAUS NOTAU]].
      hexploit EQV; eauto. intros EQNT.
      induction UNTAUS; subst.
      { pfold. inv EQNT; eauto. }
      hexploit IHUNTAUS; eauto.
      { intros. destruct UNTAUS1.
        dependent destruction H; [|subst; contradiction].
        hexploit @unalltaus_injective; [|econstructor|]; eauto. intros; subst; eauto.
      }
      intros EUTT. punfold EUTT.
    - destruct FIN as [_ FIN].
      hexploit FIN; eauto 7. clear FIN; intro FIN.
      destruct FIN as [ot' [UNTAUS NOTAU]].
      hexploit EQV; eauto. intros EQNT.
      induction UNTAUS; subst.
      { pfold. inv EQNT; eauto. }
      hexploit IHUNTAUS; eauto.
      { intros. destruct UNTAUS2.
        dependent destruction H; [|subst; contradiction].
        hexploit @unalltaus_injective; [|econstructor|]; eauto. intros; subst; eauto.
      }
      intros EUTT. punfold EUTT.
    - destruct ot1, ot2; simpl in *; try tauto.
      pfold. econstructor. right. apply CIH'.
      econstructor.
      + rewrite !finite_taus_tau in FIN. eauto.
      + eauto using unalltaus_tau'.
  }
  { punfold H. econstructor; intros.
    - split; intros.
      + genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
        destruct H0 as [ot' [UNTAUS NOTAU]].
        move UNTAUS before r. revert_until UNTAUS.
        induction UNTAUS; intros.
        * induction H; eauto; try contradiction.
          rewrite finite_taus_tau. eauto.
        * induction H; eauto 7; try inv OBS; pclearbot
          ; rewrite ?finite_taus_tau; eauto; eapply IHUNTAUS; eauto.
          punfold EQTAUS.
     + genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
       destruct H0 as [ot' [UNTAUS NOTAU]].
       move UNTAUS before r. revert_until UNTAUS.
       induction UNTAUS; intros.
       * induction H; eauto; try contradiction.
         rewrite finite_taus_tau. eauto.
       * induction H; eauto 7; try inv OBS; pclearbot
         ; rewrite ?finite_taus_tau; eauto; eapply IHUNTAUS; eauto.
         punfold EQTAUS.
    - genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
      destruct UNTAUS1 as [UNTAUS1 NT1]. destruct UNTAUS2 as [UNTAUS2 NT2].
      move UNTAUS2 before r. move UNTAUS1 before r. revert_until UNTAUS1.
      induction UNTAUS1.
      + induction 1; intros.
        * inv H; try contradiction; eauto.
        * subst. inv H; try contradiction. eauto.
      + induction 1; intros; subst.
        * inv H; try contradiction; eauto.
        * inv H; try contradiction; eauto.
          pclearbot. eapply IHUNTAUS1; eauto.
          punfold EQTAUS.
  }
Qed.

Lemma eutt_is_eutt' {E R} r (t1 t2: itree E R) :
  paco2 (eutt_ eq) r t1 t2 <-> paco2 eutt'_ r t1 t2.
Proof.
  split; intros; eapply paco2_mon_gen; eauto; intros; apply eutt__is_eutt'_; eauto.
Qed.

Lemma eutt_is_eutt'_gres {E R} r (t1 t2: itree E R) :
  paco2 (eutt_ eq ∘ gres2 (eutt_ eq)) r t1 t2 <-> paco2 (eutt'_ ∘ gres2 eutt'_) r t1 t2.
Proof.
  split; intros.
  - eapply paco2_mon_gen; eauto. intros.
    red in PR|-*. rewrite <-eutt__is_eutt'_.
    eapply monotone_eutt_; eauto. intros.
    eapply grespectful2_impl; eauto. intros.
    rewrite eutt__is_eutt'_. reflexivity.
  - eapply paco2_mon_gen; eauto. intros.
    red in PR|-*. rewrite eutt__is_eutt'_.
    eapply monotone_eutt'_; eauto. intros.
    eapply grespectful2_impl; eauto. intros.
    rewrite eutt__is_eutt'_. reflexivity.
Qed.

Global Instance eutt'_paco {E R} r:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (paco2 (@eutt'_ E R ∘ gres2 eutt'_) r).
Proof.
  repeat intro.
  rewrite <-eutt_is_eutt'_gres.
  rewrite <-eutt_is_eutt'_gres in H1.
  rewrite H, H0. eauto.
Qed.

Global Instance eutt'_gres {E R} r:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (gres2 (@eutt'_ E R) r).
Proof.
  repeat intro.
  rewrite grespectful2_iff; [|intros; erewrite eutt__is_eutt'_; reflexivity].
  rewrite grespectful2_iff in H1; [|intros; erewrite eutt__is_eutt'_; reflexivity].
  rewrite H, H0. eauto.
Qed.
