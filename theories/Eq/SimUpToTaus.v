(** * Simulation up to taus *)

(** A preorder [sutt t1 t2], where every visible step
  ([RetF] or [VisF]) on the left must be matched with a corresponding
  step on the right, ignoring [TauF].

  In particular, [spin := Tau spin] is less than everything.

  The induced equivalence relation is [eutt].
[[
  Theorem sutt_eutt : sutt eq t u -> sutt eq u t -> eutt eq t u.
]]
  Various lemmas about [eutt] may be more easily proved as
  [Proper] lemmas about [sutt] first, and then symmetrizing using
  [eutt_sutt] and [sutt_eutt].
 *)

From Coinduction Require Import all.

From Stdlib Require Import
     Morphisms
     Program.Basics.

From ITree Require Import
     Axioms
     Basics.Utils
     Core.ITreeDefinition
     Eq.Eqit
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
Hint Constructors suttF : itree.

Lemma suttF_mono : Proper (leq ==> leq) suttF.
Proof.
  repeat intro.
  induction H0; eauto with itree.
  constructor; intro; apply H, SUTTK.
  constructor; apply H, EQTAUS.
Qed.

Definition sutt_mon := {| body := suttF ; Hbody := suttF_mono |}.

Definition sutt (t1 : itree E R1) (t2 : itree E R2) :=
  gfp sutt_mon (observe t1) (observe t2).
Hint Unfold sutt : itree.

End SUTT.

Global Hint Constructors suttF : itree.
Global Hint Unfold sutt : itree.

(** Sutt-specific tactics, analogous to the eqit-specific tactics in [Eq.Eqit]. *)

Tactic Notation "sstep" :=
  unfold sutt; step; cbn [sutt_mon body].
Tactic Notation "sstep" "in" ident(h) :=
  unfold sutt in h; step in h; cbn [sutt_mon body] in h.

Ltac fold_sutt :=
  match goal with
  | |- context[@suttF ?E ?R1 ?R2 ?RR] =>
      change (@suttF E R1 R2 RR) with (body (@sutt_mon E R1 R2 RR))
  end.
Ltac fold_sutt_in h :=
  match type of h with
  | context[@suttF ?E ?R1 ?R2 ?RR] =>
      change (@suttF E R1 R2 RR) with (body (@sutt_mon E R1 R2 RR)) in h
  end.
Tactic Notation "sunstep" := fold_sutt; unstep.
Tactic Notation "sunstep" "in" ident(h) := fold_sutt_in h; unstep in h.

(* [scoinduction] unfolds [sutt] in the conclusion only, then applies coinduction. *)
Local Ltac revert_one :=
  match goal with [ H : _ |- _ ] => revert H end.
Ltac sunfold_coind :=
  first
    [intros ?; sunfold_coind; revert_one |
     unfold sutt].
Tactic Notation "scoinduction" simple_intropattern(R) simple_intropattern(H) :=
  sunfold_coind; coinduction R H; cbn [sutt_mon body].

Section SUTT_rel.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Lemma reflexive_suttF `{Reflexive _ RR} sutt (r1:Reflexive sutt) : Reflexive (@suttF E _ _ RR sutt).
Proof.
  unfold Reflexive. intros x.
  destruct x; eauto with itree.
Qed.

End SUTT_rel.

Section SUTT_facts.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

End SUTT_facts.

Lemma suttF_inv_vis {E R1 R2} (RR : R1 -> R2 -> Prop) sutt :
  forall X e (k1 : X -> itree E R1) (k2 : X -> itree E R2),
    suttF RR sutt (VisF e k1) (VisF e k2) ->
    forall x, sutt (observe (k1 x)) (observe (k2 x)).
Proof.
  intros. inv H. ddestruction; auto.
Qed.

Lemma sutt_inv_vis {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall X e (k1 : X -> itree E R1) (k2 : X -> itree E R2),
  sutt RR (Vis e k1) (Vis e k2) ->
  forall x, sutt RR (k1 x) (k2 x).
Proof.
  intros. sstep in H. simpl in H.
  now apply (suttF_inv_vis _ _ _ _ _ _ H).
Qed.

Lemma sutt_tau_right {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 ->
    sutt RR t1 (Tau t2).
Proof.
  intros. sstep. sstep in H.
  constructor. auto.
Qed.

Lemma sutt_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 ->
    sutt RR (Tau t1) t2.
Proof.
  intros. sstep.
  constructor. exact H.
Qed.

Lemma sutt_elim_tau_right {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) (t2: itree E R2),
    sutt RR t1 (Tau t2) ->
    sutt RR t1 t2.
Proof.
  unfold sutt at -1. icoinduction c CIH. intros t1 t2 H. sstep in H.
  inv H.
  - eapply suttF_mono; [|exact EQTAUS].
    intros ?? ?. now apply (gfp_chain c).
  - constructor. apply CIH. exact EQTAUS.
Qed.

Lemma suttF_inv_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) ot2,
    suttF RR (gfp (@sutt_mon E R1 R2 RR)) (TauF t1) ot2 ->
    suttF RR (gfp (@sutt_mon E R1 R2 RR)) (observe t1) ot2.
Proof.
  intros.
  remember (TauF t1) as ott1.
  induction H; intros; subst; try dependent destruction Heqott1; eauto with itree.
  sstep in EQTAUS. exact EQTAUS.
Qed.

Lemma sutt_inv_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) (t2: itree E R2),
    sutt RR (Tau t1) t2 ->
    sutt RR t1 t2.
Proof.
  intros. sstep in H. sstep.
  apply suttF_inv_tau_left; auto.
Qed.

Theorem sutt_eutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 -> sutt (flip RR) t2 t1 -> eutt RR t1 t2.
Proof.
  icoinduction c CIH. intros t1 t2 H1 H2.
  sstep in H1. sstep in H2.
  induction H1; intros; subst; auto with itree.
  - (* suttF_vis *)
    constructor. intro x. apply CIH.
    + unfold sutt. exact (SUTTK x).
    + unfold sutt. exact (suttF_inv_vis _ _ _ _ _ _ H2 x).
  - (* suttF_tau_right *)
    constructor; eauto. eapply IHsuttF; auto. eapply suttF_inv_tau_left; auto.
  - (* suttF_tau_left *)
    inv H2.
    + clear t1 t2. genobs t0 ot0.
      hinduction EQTAUS0 before CIH; intros; subst.
      * constructor; eauto. simpobs. constructor. eauto.
      * constructor; eauto. simpobs. constructor. intro x.
        apply CIH.
        -- exact (sutt_inv_vis _ _ _ _ _ EQTAUS x).
        -- unfold sutt. apply SUTTK.
      * constructor; eauto. simpobs. eapply IHEQTAUS0; eauto.
        rewrite (itree_eta' ot1). apply sutt_inv_tau_left. unfold sutt. exact EQTAUS.
      * constructor. apply CIH; auto. apply sutt_elim_tau_right; auto.
    + constructor. apply CIH; apply sutt_elim_tau_right; auto.
Qed.

Theorem eutt_sutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    eutt RR t1 t2 -> sutt RR t1 t2.
Proof.
  scoinduction c CIH. intros t1 t2 H.
  step in H.
  induction H.
  - constructor; auto.
  - constructor. constructor. apply CIH. exact REL.
  - constructor. intro. apply CIH. apply REL.
  - constructor. step. exact IHeqitF.
  - constructor. exact IHeqitF.
Qed.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma sutt_bind' {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    sutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> sutt SS (s1 r1) (s2 r2)) ->
                  @sutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Proof.
  scoinduction c CIH. intros t1 t2 H s1 s2 Hs.
  sstep in H. unfold observe; cbn.
  induction H; intros.
  - simpl. apply Hs in H. sstep in H.
    eapply suttF_mono; [|exact H].
    intros ?? ?. now apply (gfp_chain c).
  - simpl. econstructor. intros. apply CIH; eauto with itree.
  - constructor. eauto.
  - constructor.
    change (elem c (observe (ITree.bind t0 s1)) (observe (ITree.bind (go ot2) s2))).
    apply CIH; auto.
Qed.

(* todo: this could be made stronger with eutt rather than eq_itree
 *)
#[global] Instance Proper_sutt {E : Type -> Type} {R1 R2 : Type} r
: Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
       (@sutt E R1 R2 r).
Proof.
  repeat red. scoinduction c CIH. intros x y H x0 y0 H0 H1.
  step in H. step in H0. sstep in H1.
  revert x H x0 H0.
  induction H1; intros.
  - inv H1; try discriminate. inv H0; try discriminate. econstructor. eauto.
  - dependent destruction H; try discriminate.
    dependent destruction H0; try discriminate.
    simpobs.
    constructor. intros. eapply CIH. 
    apply REL. 
    apply REL0. apply SUTTK.  
  - dependent destruction H0; try discriminate.
    simpobs. constructor. 
    apply IHsuttF; auto. now step in REL. 
  - dependent destruction H; try discriminate.
    simpobs. constructor.
    rewrite (itree_eta' ot2) in *. eapply CIH. 
    apply REL. step; apply H0. apply EQTAUS. 
Qed.