(** * Equivalence up to taus: simple facts *)

(** This module proves simple facts about the [eutt] relation defined in
    [UpToTaus]:

    - Reflexivity, symmetry
    - Inversion lemmas
    - Pseudo-constructor lemmas
    - Unfold lemmas
 *)

(* begin hide *)
From Coq Require Import
     Program (* [revert_until] *)
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From Paco Require Import paco.

From ITree Require Import
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Shallow
     Eq.Eq
     Eq.UpToTaus.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

(** ** Reflexivity and symmetry *)

Section EUTT_homo.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Global Instance subrelation_eq_eutt0 eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt0 RR eutt).
Proof.
  gcofix CIH; gstep. intros.
  gunfold H0. repeat red in H0 |- *. inv H0; eauto 7 with paco.
Qed.

Global Instance subrelation_eq_eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt RR).
Proof.
  gstep. gcofix CIH'; gstep. intros.
  gunfold H0. repeat red in H0 |- *. inv H0; eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt0_param `{Reflexive _ RR} eutt
       (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (gcpn2 (eutt0_ RR eutt) r rg).
Proof.
  repeat intro.
  eapply gcpn2_mon with (r:=bot2) (rg:=bot2); eauto with paco; try contradiction.
  revert x. gcofix CIH; gstep. red; intros.
  destruct (observe x); eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt_param `{Reflexive _ RR}
       (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (gcpn2 (eutt0 RR) r rg).
Proof.
  repeat intro.
  eapply gcpn2_mon with (r:=bot2) (rg:=bot2); eauto with paco; try contradiction.
  revert x. gstep. gcofix CIH; gstep. intros. repeat red.
  destruct (observe x); eauto 7 with paco.
Qed.

End EUTT_homo.

Section EUTT_hetero.

Context {E : Type -> Type} {R1 R2 : Type} {RR : R1 -> R2 -> Prop}.

Lemma Symmetric_euttF_hetero (RR' : R2 -> R1 -> Prop)
      (r1 : _ -> _ -> Prop) (r2 : _ -> _ -> Prop) (r'1 : _ -> _ -> Prop) (r'2 : _ -> _ -> Prop)
      (SYM_RR : forall r1 r2, RR r1 r2 -> RR' r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i)
      (SYM_r' : forall i j, r'1 i j -> r'2 j i) :
  forall (ot1 : itree' E R1) (ot2 : itree' E R2),
    euttF RR r1 r'1 ot1 ot2 -> euttF RR' r2 r'2 ot2 ot1.
Proof.
  intros. induction H; eauto 7.
  econstructor; intros. edestruct EUTTK; eauto 7.
Qed.

Lemma Symmetric_eutt_hetero (RR' : R2 -> R1 -> Prop)
      (SYM_RR : forall r1 r2, RR r1 r2 -> RR' r2 r1) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    eutt RR t1 t2 -> eutt RR' t2 t1.
Proof.
  gstep. gcofix CIH; gstep. intros.
  do 2 gunfold H0.
  repeat red in H0 |- *.
  induction H0; eauto 7 with paco.
  econstructor; intros.
  edestruct EUTTK as [TMP | TMP]; [eauto 7 with paco|].
  right. gbase. apply CIH. gstep. eauto.
Qed.

(** ** Inversion lemmas *)

Lemma euttF_inv_tau_left r (t1: itree E R1) (t2: itree E R2)
    (REL : eutt0_ RR r (gcpn2 (eutt0_ RR r) bot2 bot2) (Tau t1) t2) :
  eutt0_ RR r (gcpn2 (eutt0_ RR r) bot2 bot2) t1 t2.  
Proof.
  repeat red in REL |- *. simpl in *.
  remember (TauF t1) as ott1.
  move REL before r. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott1; eauto.
  gunfold EQTAUS. eauto.
Qed.

Lemma euttF_inv_tau_right r (t1: itree E R1) (t2: itree E R2)
    (REL : eutt0_ RR r (gcpn2 (eutt0_ RR r) bot2 bot2) t1 (Tau t2)) :
  eutt0_ RR r (gcpn2 (eutt0_ RR r) bot2 bot2) t1 t2.
Proof.
  repeat red in REL |- *. simpl in *.
  remember (TauF t2) as ott2.
  move REL before r. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott2; eauto.
  gunfold EQTAUS. eauto.
Qed.

Lemma eutt_inv_vis {U} (e : E U) (k1 : U -> itree E R1) (k2 : U -> itree E R2)
  : eutt RR (Vis e k1) (Vis e k2) ->
    (forall u, eutt RR (k1 u) (k2 u)).
Proof.
  intros H x.
  gunfold H; gunfold H; inversion H; auto_inj_pair2; subst.
  edestruct EUTTK; eauto with paco.
Qed.

Lemma eutt_inv_ret r1 r2 :
  @eutt E R1 R2 RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros H. gunfold H; gunfold H; inversion H; auto.
Qed.

Definition isb_tau {E R} (ot: itree' E R) : bool :=
  match ot with | TauF _ => true | _ => false end.

Lemma eutt_ret x1 x2 :
  RR x1 x2 -> @eutt E R1 R2 RR (Ret x1) (Ret x2).
Proof.
  intros; gstep. gstep. econstructor. eauto.
Qed.

Lemma eutt_vis {U} (e: E U) k k' :
  (forall x: U, @eutt E R1 R2 RR (k x) (k' x)) ->
  eutt RR (Vis e k) (Vis e k').
Proof.
  intros. gstep. gstep. econstructor.
  intros. left. apply H.
Qed.

Lemma eutt_tau (t1 : itree E R1) (t2 : itree E R2) :
  eutt RR t1 t2 -> eutt RR (Tau t1) (Tau t2).
Proof.
  intros. gstep. gstep. econstructor. gunfold H. eauto.
Qed.

End EUTT_hetero.

Section EUTT_eq.

Context {E : Type -> Type} {R : Type}.

Local Notation eutt := (@eutt E R R eq).

Global Instance subrelation_observing_eutt:
  @subrelation (itree E R) (observing eq) eutt.
Proof.
  repeat intro. eapply subrelation_eq_eutt, observing_eq_itree_eq. eauto.
Qed.

Global Instance Reflexive_eutt: Reflexive eutt.
Proof. apply Reflexive_eutt_param; eauto. Qed.

Global Instance Symmetric_eutt: Symmetric eutt.
Proof.
  repeat intro. eapply Symmetric_eutt_hetero, H.
  intros; subst. eauto.
Qed.

Global Instance eutt_cong_go : Proper (going eutt ==> eutt) go.
Proof. intros ? ? []; eauto. Qed.

Global Instance eutt_cong_observe : Proper (eutt ==> going eutt) observe.
Proof.
  constructor. do 2 gstep. do 2 gunfold H. auto.
Qed.

Global Instance eutt_cong_tauF : Proper (eutt ==> going eutt) (@TauF _ _ _).
Proof.
  constructor. do 2 gstep. econstructor. gunfold H. eauto.
Qed.

Global Instance eutt_cong_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> going eutt) (VisF e).
Proof.
  constructor. gstep. gstep. econstructor.
  intros. specialize (H x0). gunfold H. eauto.
Qed.

End EUTT_eq.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt eq (ITree.map g (ITree.map f t))
          (ITree.map (fun x => g (f x)) t).
Proof.
  apply subrelation_eq_eutt, map_map.
Qed.

Lemma tau_eutt {E R} (t: itree E R) : Tau t ≈ t.
Proof.
  gstep. gstep. econstructor.
  destruct (observe t); eauto with paco.
  - constructor. apply reflexivity.
  - constructor. intros. left. apply reflexivity.
Qed.

(** ** Tactics *)

(** Remove all taus from the left hand side of the goal
    (assumed to be of the form [lhs ≈ rhs]). *)
Ltac tau_steps :=
  repeat (
      (* Only rewrite the LHS, even if it also occurs in the RHS *)
      rewrite itree_eta at 1;
      cbn;
      match goal with
      | [ |- go (observe _) ≈ _ ] =>
        (* Cancel [itree_eta] if no progress was made. *)
        fail 1
      | _ => try rewrite tau_eutt
      end).
