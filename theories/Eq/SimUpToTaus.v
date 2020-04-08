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
Hint Constructors suttF: core.

Definition sutt (t1 : itree E R1) (t2 : itree E R2) :=
  paco2 suttF bot2 (observe t1) (observe t2).
Hint Unfold sutt: core.

End SUTT.

Hint Constructors suttF: core.
Hint Unfold sutt: core.

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
  intros. pstep. punfold H. simpl in *.
  inv H. auto_inj_pair2. subst. specialize (SUTTK x). pclearbot. punfold SUTTK.
Qed.

Lemma sutt_tau_right {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 ->
    sutt RR t1 (Tau t2).
Proof.
  intros. punfold H. pstep.
  repeat red. repeat red in H. constructor.
  auto.
Qed.

Lemma sutt_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 ->
    sutt RR (Tau t1) t2.
Proof.
  intros. punfold H. pstep.
  repeat red. repeat red in H. constructor.
  eauto with paco.
Qed.

Lemma sutt_elim_tau_right {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) (t2: itree E R2),
    sutt RR t1 (Tau t2) ->
    sutt RR t1 t2.
Proof.
  pcofix CIH. pstep. intros.
  punfold H0. repeat red in H0.
  inv H0.
  - eapply monotone_suttF; eauto using upaco2_mon_bot with paco.
  - constructor. pclearbot. eauto with paco.
Qed.

Lemma suttF_inv_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) ot2,
    suttF RR (upaco2 (suttF RR) bot2) (TauF t1) ot2 ->
    suttF RR (upaco2 (suttF RR) bot2) (observe t1) ot2.
Proof.
  intros.
  remember (TauF t1) as ott1.
  induction H; intros; subst; try dependent destruction Heqott1; eauto.
  pclearbot. punfold EQTAUS. 
Qed.

Lemma sutt_inv_tau_left {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1: itree E R1) (t2: itree E R2),
    sutt RR (Tau t1) t2 ->
    sutt RR t1 t2.
Proof.
  intros.
  punfold H. pstep. repeat red in H |- *.
  apply suttF_inv_tau_left; auto.
Qed.

Theorem sutt_eutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 -> sutt (flip RR) t2 t1 -> eutt RR t1 t2.
Proof.
  pcofix CIH. intros.
  punfold H0. punfold H1. pstep. red.
  induction H0; intros; subst; auto.
  - constructor. intro. right. eapply suttF_inv_vis in H1. pclearbot. eauto with paco.
  - constructor; eauto. eapply IHsuttF; auto. eapply suttF_inv_tau_left; auto.
  - (* doing induction when one of the trees is a tau doesn't work well *)
    inv H1; pclearbot.
    + clear t1 t2. genobs t0 ot0.
      hinduction EQTAUS0 before CIH; intros; subst; pclearbot.
      * constructor; eauto. simpobs. constructor. eauto.
      * constructor; eauto. simpobs. constructor. intros.
        right. apply CIH; auto. eapply sutt_inv_vis in EQTAUS; eauto.
      * constructor; eauto. simpobs. eapply IHEQTAUS0; eauto.
        rewrite (itree_eta' ot1). apply sutt_inv_tau_left; auto.
      * constructor. right. apply CIH; auto. apply sutt_elim_tau_right; auto.
    + constructor. right. apply CIH; apply sutt_elim_tau_right; auto.
Qed.

Theorem eutt_sutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    eutt RR t1 t2 -> sutt RR t1 t2.
Proof.
  pcofix CIH. pstep. intros.
  punfold H0. red in H0.
  induction H0; constructor; pclearbot; eauto 7 with paco.
Qed.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma sutt_bind' {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    sutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> sutt SS (s1 r1) (s2 r2)) ->
                  @sutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Proof.
  pcofix self. pstep. intros.
  punfold H0.
  rewrite 2 unfold_bind_.
  induction H0; intros.
  - simpl. apply H1 in H. punfold H. eapply monotone_suttF; eauto using upaco2_mon_bot.
  - simpl. pclearbot. econstructor. eauto.
  - constructor. eauto with paco.
  - constructor. pclearbot. rewrite (itree_eta' ot2), <- unfold_bind_. eauto.
Qed.

Require Import Coq.Relations.Relations.

(* todo: this could be made stronger with eutt rather than eq_itree
 *)
Instance Proper_sutt {E : Type -> Type} {R1 R2 : Type} r
: Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
       (@sutt E R1 R2 r).
Proof.
  repeat red. pcofix CIH; pstep. intros.
  punfold H0; punfold H1; punfold H2. red in H0, H1.
  (* rename H1 into H2, Hxy into H1.  *)
  hinduction H2 before CIH; subst; intros.
  - inv H0; try discriminate. inv H1; try discriminate. econstructor. eauto.
  - dependent destruction H0; try discriminate.
    dependent destruction H1; try discriminate.
    simpobs. pclearbot.
    constructor. intros. right. eauto 7 with paco.
  - dependent destruction H1; try discriminate.
    simpobs. pclearbot. punfold REL.
  - dependent destruction H0; try discriminate.
    simpobs. pclearbot. constructor.
    right. rewrite (itree_eta' ot2) in *. eauto.
Qed.
