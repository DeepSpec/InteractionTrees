(** * Simulation Up To Tau *)

(** A preorder [sutt t1 t2], where every visible step
  ([RetF] or [VisF]) on the left must be matched with a corresponding
  step on the right, ignoring [TauF].

  In particular, [spin := Tau spin] is less than everything.

  The induced equivalence relation is [eutt].

  Various [Proper] lemmas about [eutt] are more easily proved as
  [Proper] lemmas about [sutt] first, and then symmetrizing using
  [eutt_sutt] and [sutt_eutt].
 *)

Require Import Paco.paco.

From Coq Require Import
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Program
     Relations.Relations.

From ITree Require Import
     Core.ITreeDefinition.

From ITree Require Import
     Eq.Eq
     Eq.UpToTaus
     Eq.Shallow.

Section SUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive suttF (sutt: itree' E R1 -> itree' E R2 -> Prop) :
  itree' E R1 -> itree' E R2 -> Prop :=
| suttF_ret r1 r2 : RR r1 r2 -> suttF sutt (RetF r1) (RetF r2)
| suttF_vis u (e : E u) k1 k2
      (SUTTK: forall x, sutt (observe (k1 x)) (observe (k2 x))):
    suttF sutt (VisF e k1) (VisF e k2)
| suttF_tau_right ot1 t2
      (EQTAUS: suttF sutt ot1 (observe t2)):
    suttF sutt ot1 (TauF t2)
| suttF_tau_left t1 ot2
      (EQTAUS: sutt (observe t1) ot2):
    suttF sutt (TauF t1) ot2
.
Hint Constructors suttF.

Definition sutt (t1 : itree E R1) (t2 : itree E R2) :=
  cpn2 suttF bot2 (observe t1) (observe t2).
Hint Unfold sutt.

End SUTT.

Hint Constructors suttF.
Hint Unfold sutt.

Section SUTT_rel.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Lemma reflexive_suttF `{Reflexive _ RR} sutt (r1:Reflexive sutt) : Reflexive (@suttF E _ _ RR sutt).
Proof.
  unfold Reflexive. intros x.
  destruct x; eauto.
Qed.

End SUTT_rel.

Section SUTT_facts.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma monotone_suttF : monotone2 (@suttF E _ _ RR).
Proof. repeat red; intros. induction IN; eauto. Qed.
Hint Resolve monotone_suttF : paco.

End SUTT_facts.

Hint Resolve @monotone_suttF : paco.

Lemma suttF_inv_vis {E R1 R2} (RR : R1 -> R2 -> Prop) sutt :
  forall X e (k1 : X -> itree E R1) (k2 : X -> itree E R2),
    suttF RR sutt (VisF e k1) (VisF e k2) ->
    forall x, sutt (observe (k1 x)) (observe (k2 x)).
Proof.
  intros. inv H. auto_inj_pair2. subst. auto.
Qed.

Lemma sutt_inv_vis {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall X e (k1 : X -> itree E R1) (k2 : X -> itree E R2),
  sutt RR (Vis e k1) (Vis e k2) ->
  forall x, sutt RR (k1 x) (k2 x).
Proof.
  intros. ustep. uunfold H. repeat red in H |- *. simpl in *.
  inv H. auto_inj_pair2. subst. specialize (SUTTK x). uunfold SUTTK. eauto with paco.
Qed.

Lemma sutt_tau_right {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 ->
    sutt RR t1 (Tau t2).
Proof.
  intros. uunfold H. ustep.
  repeat red. repeat red in H. constructor.
  auto.
Qed.

Lemma sutt_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 ->
    sutt RR (Tau t1) t2.
Proof.
  intros. uunfold H. ustep.
  repeat red. repeat red in H. constructor.
  eauto with paco.
Qed.

Lemma sutt_elim_tau_right {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) (t2: itree E R2),
    sutt RR t1 (Tau t2) ->
    sutt RR t1 t2.
Proof.
  ucofix CIH. intros.
  uunfold H0. repeat red in H0.
  inv H0.
  - eapply monotone_suttF; eauto using cpn2_mon_bot with paco.
  - constructor. eauto with paco.
Qed.

Lemma suttF_inv_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) (t2: itree E R2),
    suttF RR (cpn2 (suttF RR) bot2) (TauF t1) (observe t2) ->
    suttF RR (cpn2 (suttF RR) bot2) (observe t1) (observe t2).
Proof.
  intros.
  simpl in *.
  remember (TauF t1) as ott1.
  induction H; intros; subst; try dependent destruction Heqott1; eauto.
  uunfold EQTAUS. eauto.
Qed.

Lemma sutt_inv_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) (t2: itree E R2),
    sutt RR (Tau t1) t2 ->
    sutt RR t1 t2.
Proof.
  intros.
  uunfold H. ustep. repeat red in H |- *.
  apply suttF_inv_tau_left; auto.
Qed.

Theorem sutt_eutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 -> sutt (flip RR) t2 t1 -> eutt RR t1 t2.
Proof.
  ucofix CIH. red. ucofix CIH'. intros.
  uunfold H0. uunfold H1. repeat red in H0, H1. repeat red.
  remember (observe t1). remember (observe t2).
  generalize dependent t1. generalize dependent t2.
  induction H0; intros; subst; auto.
  - constructor. intro. left. eapply suttF_inv_vis in H1. eauto with paco.
  - constructor. eapply IHsuttF; auto. apply suttF_inv_tau_left; auto.
  - clear Heqi t0. clear CIH.
    (* doing induction when one of the trees is a tau doesn't work well *)
    inv H1.
    + remember (observe t2). remember (observe t1).
      generalize dependent t2. generalize dependent t1.
      induction EQTAUS0; intros; try inv Heqi0.
      * constructor. rewrite <- H1. constructor. uunfold EQTAUS. inversion EQTAUS. auto.
      * constructor. rewrite <- H0. constructor. intro. right.
        ubase. apply CIH'; auto. eapply sutt_inv_vis in EQTAUS; eauto.
      * constructor. rewrite <- H0. eapply IHEQTAUS0; eauto. apply sutt_inv_tau_left; auto.
      * constructor. ubase. apply CIH'; auto. apply sutt_elim_tau_right; auto.
    + rewrite <- H0 in *. constructor. ubase. apply CIH'; apply sutt_elim_tau_right; auto.
Qed.

Theorem eutt_sutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    eutt RR t1 t2 -> sutt RR t1 t2.
Proof.
  ucofix CIH. intros.
  uunfold H0. uunfold H0.
  induction H0; constructor; eauto with paco.
  - intros. destruct (EUTTK x); eauto with paco.
  - constructor. eauto with paco.
Qed.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma sutt_bind' {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    sutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> sutt SS (s1 r1) (s2 r2)) ->
                  @sutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Proof.
  (* apply sutt_is_sutt1. *)
  (* apply sutt_is_sutt1 in H. *)
  (* setoid_rewrite sutt_is_sutt1 in H0. *)
  ucofix self; intros.
  uunfold H0.
  genobs t1 ot1. genobs t2 ot2.
  revert t1 t2 Heqot1 Heqot2.
  induction H0; intros.
  - rewrite 2 unfold_bind, <- Heqot1, <- Heqot2; simpl.
    apply H1 in H. uunfold H. eapply gcpn2_mon; eauto with paco; contradiction.
  - rewrite 2 unfold_bind, <- Heqot1, <- Heqot2; simpl.
    constructor. eauto with paco.
  - rewrite (unfold_bind t0), <- Heqot2; simpl.
    constructor. gcpn_fold. eauto with paco.
  - rewrite (unfold_bind t0), <- Heqot1; simpl.
    constructor. subst. eauto with paco.
Qed.

Require Import Coq.Relations.Relations.

Lemma eq_itree_vis_l {E R1 R2} {RR : R1 -> R2 -> Prop} {RC T}
      (e : E T) (k : _ -> _)
      (it : itreeF E _ _)
      (H : @eq_itreeF E R1 R2 RR RC (VisF e k) it)
      :
        exists k', it = VisF e k' /\
                 (forall x, RC (k x) (k' x)).
Proof.
  refine
    match H in eq_itreeF _ _ x y
          return
          match x return Prop with
          | @VisF _ _ _ u e k =>
            exists k' : _ -> _, y = VisF e k' /\ (forall x : u, RC (k x) (k' x))
          | _ => True
          end
    with
    | EqVis _ _ _ _ _ Ek => ltac:(eexists; split; [ reflexivity | eassumption ])
    | _ => I
    end.
Qed.

(* todo: this could be made stronger with eutt rather than eq_itree
 *)
Instance Proper_sutt {E : Type -> Type} {R1 R2 : Type}
: Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==>
          eq_itree eq ==> eq_itree eq ==> Basics.impl)
       (@sutt E R1 R2).
Proof.
  red. red.
  unfold pointwise_relation.
  unfold impl.
  intros x y Hxy.
  red. red.
  do 5 intro.
  revert x0 y0 H x1 y1.
  ucofix CIH.
  intros.
  uunfold H0.
  uunfold H1.
  uunfold H2.
  repeat red in H0. repeat red in H1. repeat red in H2.
  revert H0 H1.
  genobs_clear y0 oy0. genobs_clear y1 oy1. genobs_clear x2 ox2. genobs_clear x3 ox3.
  revert_until CIH.
  induction 1; subst; intros.
  { inv H0. inv H1. econstructor. eauto. }
  { eapply eq_itree_vis_l in H0.
    eapply eq_itree_vis_l in H1.
    destruct H0 as [ ? [ ? ? ] ].
    destruct H1 as [ ? [ ? ? ] ].
    rewrite H. rewrite H1.
    constructor.
    intros.
    ubase.
    specialize (H0 x2).
    specialize (H2 x2).
    eapply CIH; eauto. }
  { inversion H1; clear H1; subst.
    constructor.
    eapply IHsuttF; eauto.
    uunfold REL. eauto. }
  { inversion H0; clear H0; subst.
    constructor.
    ubase.
    change oy1 with (observe (go oy1)).
    eapply CIH.
    - eassumption.
    - instantiate (1:= go ot2).
      ustep. eapply H1.
    - eapply EQTAUS. }
Qed.
