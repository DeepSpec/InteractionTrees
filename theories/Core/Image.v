(** * The image of an Interaction Tree *)

(* begin hide *)
From ITree Require Import
     ITree
     Eq.Eq.

From Paco Require Import paco.
From Coq Require Import Morphisms Basics Program.Equality.
Import ITree.
Import ITreeNotations.
(* end hide *)

(** ** Image of itrees *)

(** The [Image a t] predicate expresses that [t] admits a finite
    branch whose leaf carries value [a].

    We provide the elementary structural lemmas to work with this
    predicate, and one main useful result relying on [Image]: the
    up-to bind closure [eqit_bind_clo] can be refined such that
    continuations need only be related over the image of the
    computation.
    *)

Inductive Image {E} {A: Type} (a: A) : itree E A -> Prop :=
 | ImageRet: forall t,
   observe t = RetF a ->
   Image a t
 | ImageTau: forall t u,
   observe t = TauF u ->
   Image a u ->
   Image a t
 | ImageVis: forall {X} (e: E X) t k x,
   observe t = VisF e k ->
   Image a (k x) ->
   Image a t
.
#[global] Hint Constructors Image: core.

Module ImageNotations.
  Notation "a ∈ t" := (Image a t) (at level 70).
End ImageNotations.

Import ImageNotations.

(** Smart constructors *)

Lemma Image_Ret : forall E R a,
  a ∈ (Ret a : itree E R).
Proof.
  intros; econstructor; reflexivity.
Qed.

Lemma Image_Tau : forall E R a t,
  a ∈ (t : itree E R) ->
  a ∈ Tau t.
Proof.
  intros; econstructor; [reflexivity | eauto].
Qed.

Lemma Image_Vis : forall E X Y (e : E X) (k : _ -> itree E Y) b x,
  b ∈ (k x) ->
  b ∈ (Vis e k).
Proof.
  intros * IN; econstructor 3; [reflexivity | eauto].
Qed.

(** Inversion lemmas *)
Lemma Image_Ret_inv : forall E R a b,
  b ∈ (Ret a : itree E R) ->
  b = a.
Proof.
  intros * IN; inv IN; cbn in *; try congruence.
Qed.

Lemma Image_Tau_inv : forall E R u b,
  b ∈ (Tau u : itree E R) ->
  b ∈ u.
Proof.
  intros * IN; inv IN; cbn in *; try congruence.
Qed.

Lemma Image_Vis_inv : forall E X Y (e : E X) (k : _ -> itree E Y) b,
  b ∈ Vis e k ->
  exists x, b ∈ k x.
Proof.
  intros * IN *; inv IN; cbn in *; try congruence.
  revert x H0.
  refine (match H in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
  eauto.
Qed.

(** Closure under [eutt]

  General asymetric lemmas for [eutt R], where we naturally get
  a different point related by [R], and [Proper] instances for
  [eutt eq]. *)

Lemma Image_eutt_genlr {E A B R}:
  forall (t : itree E A) (u : itree E B) (a : A),
  eutt R t u ->
  a ∈ t ->
  exists b, b ∈ u /\ R a b.
Proof.
  intros * EQ FIN;
  revert u EQ.
  induction FIN; intros u2 EQ.
  - punfold EQ.
    red in EQ; rewrite H in EQ; clear H t.
    remember (RetF a); genobs u2 ou.
    hinduction EQ before R; intros; try now discriminate.
    inv Heqi; eauto.
    edestruct IHEQ as (b & IN & HR); eauto.
  -  punfold EQ; red in EQ; rewrite H in EQ; clear H t.
    remember (TauF u); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot; inv Heqi; eauto.
    edestruct IHFIN as (? & ? & ?); eauto.
    edestruct IHEQ as (? & ? & ?); eauto.
  -  punfold EQ; red in EQ; rewrite H in EQ; clear H t.
    remember (VisF e k); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot.
    + revert x FIN IHFIN.
      refine (match Heqi in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
      intros. edestruct IHFIN as (? & ? & ?); eauto.
    + edestruct IHEQ as (? & ? & ?); eauto.
Qed.

Lemma Image_eutt_genrl {E A B R}:
  forall (t : itree E A) (u : itree E B) (b : B),
  eutt R t u ->
  b ∈ u ->
  exists a, a ∈ t /\ R a b.
Proof.
  intros * EQ FIN.
  apply eqit_flip in EQ.
  revert EQ FIN.
  apply @Image_eutt_genlr.
Qed.

#[global] Instance Image_eutt {E A}:
  Proper (eq ==> eutt eq ==> iff) (@Image E A).
Proof.
  apply proper_sym_impl_iff_2; [ exact _ .. | ].
  unfold Proper, respectful, impl. intros; subst.
  edestruct @Image_eutt_genlr as [? []]; try eassumption; subst; assumption.
Qed.

(** Compatibility with [bind], forward and backward *)

Lemma Image_bind : forall {E R S}
  (t : itree E R) (k : R -> itree E S) a b,
  b ∈ t ->
  a ∈ k b ->
  a ∈ t >>= k.
Proof.
  intros * INt INk; induction INt.
  - rewrite (itree_eta t), H, bind_ret_l; auto.
  - rewrite (itree_eta t), H, tau_eutt; auto.
  - rewrite (itree_eta t), H, bind_vis.
    apply Image_Vis with x; auto.
Qed.

Lemma Image_bind_inv : forall {E R S}
  (t : itree E R) (k : R -> itree E S) a,
  a ∈ t >>= k ->
  exists b, b ∈ t /\ a ∈ k b.
Proof.
  intros * FIN;
  remember (ITree.bind t k) as u.
  revert t k Hequ.
  induction FIN; intros t' k' ->; rename t' into t.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence.
    eauto.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence; eauto.
    inversion H; clear H; symmetry in H1.
    edestruct IHFIN as (? & ? & ?).
    apply H1.
    eauto.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence; eauto.
    revert x FIN IHFIN.
    refine (match H in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
    intros.
    edestruct IHFIN as (? & ? & ?).
    reflexivity.
    eauto.
Qed.

(** Image-aware up-to bind closure
    This construction generalizes [eqit_bind_clo]: one can
    indeed provide an arbitrary cut at the relational
    predicate [RU] of one's choice, but the continuations
    are only required to be related pointwise at the intersection
    of [RU] with the respective images of the prefixes.
  *)
Section ImageBind.

  Context {E : Type -> Type} {R S : Type}.

  Local Open Scope itree.

  Inductive eqit_Image_bind_clo b1 b2 (r : itree E R -> itree E S -> Prop) :
    itree E R -> itree E S -> Prop :=
  | pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop)
                (t1 : itree E U1) (t2 : itree E U2)
                 (k1 : U1 -> itree E R) (k2 : U2 -> itree E S)
                (EQV: eqit RU b1 b2 t1 t2)
                (REL: forall u1 u2,
                      u1 ∈ t1 -> u2 ∈ t2 -> RU u1 u2 ->
                      r (k1 u1) (k2 u2))
      : eqit_Image_bind_clo b1 b2 r
            (ITree.bind t1 k1) (ITree.bind t2 k2)
    .
  Hint Constructors eqit_Image_bind_clo: core.

  Lemma eqit_Image_clo_bind  (RS : R -> S -> Prop) b1 b2 vclo
        (MON: monotone2 vclo)
        (CMP: compose (eqitC RS b1 b2) vclo <3= compose vclo (eqitC RS b1 b2))
        (ID: id <3= vclo):
    eqit_Image_bind_clo b1 b2 <3= gupaco2 (eqit_ RS b1 b2 vclo) (eqitC RS b1 b2).
  Proof.
    gcofix CIH. intros. destruct PR.
    guclo eqit_clo_trans.
    econstructor; auto_ctrans_eq; try (rewrite (itree_eta (x <- _;; _ x)), unfold_bind; reflexivity).
    punfold EQV. unfold_eqit.
    genobs t1 ot1.
    genobs t2 ot2.
    hinduction EQV before CIH; intros; pclearbot.
    - guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; try (rewrite <- !itree_eta; reflexivity).
      gbase; cbn.
      apply REL0; auto.
    - gstep. econstructor.
      gbase.
      apply CIH.
      econstructor; eauto.
    - gstep. econstructor.
      intros; apply ID; unfold id.
      gbase.
      apply CIH.
      econstructor; eauto.
    - destruct b1; try discriminate.
      guclo eqit_clo_trans.
      econstructor.
      3:{ eapply IHEQV; eauto. }
      3,4:auto_ctrans_eq.
      2: reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-itree_eta. reflexivity.
    - destruct b2; try discriminate.
      guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-itree_eta. reflexivity.
  Qed.

End ImageBind.

(** General cut rule for [eqit]
    This result generalizes [eqit_clo_bind].  *)
Lemma eqit_clo_bind_gen :
  forall {E} {R1 R2} (RR : R1 -> R2 -> Prop) {U1 U2} {UU : U1 -> U2 -> Prop}
          b1 b2
           (t1 : itree E U1) (t2 : itree E U2)
          (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2),
    eqit UU b1 b2 t1 t2 ->
    (forall (u1 : U1) (u2 : U2),
      u1 ∈ t1 -> u2 ∈ t2 -> UU u1 u2 ->
      eqit RR b1 b2 (k1 u1) (k2 u2)) ->
    eqit RR b1 b2 (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
    intros.
    ginit. guclo (@eqit_Image_clo_bind E R1 R2).
    econstructor; eauto.
    intros * IN1 IN2 HR.
    gfinal; right.
    apply H0; auto.
Qed.

(** Specialization of the cut rule to [eutt] *)
Lemma eutt_clo_bind_gen :
  forall {E} {R1 R2} (RR : R1 -> R2 -> Prop) {U1 U2} {UU : U1 -> U2 -> Prop}
           (t1 : itree E U1) (t2 : itree E U2)
          (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2),
    eutt UU t1 t2 ->
    (forall (u1 : U1) (u2 : U2),
      u1 ∈ t1 -> u2 ∈ t2 -> UU u1 u2 ->
      eutt RR (k1 u1) (k2 u2)) ->
    eutt RR (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
  intros *; apply eqit_clo_bind_gen.
Qed.

(** Often useful particular case of identical prefixes *)
Lemma eutt_eq_bind_gen {E R S T} (RS : R -> S -> Prop)
      (t: itree E T) (k1: T -> itree E R) (k2 : T -> itree E S) :
    (forall u, u ∈ t -> eutt RS (k1 u) (k2 u)) ->
    eutt RS (t >>= k1) (t >>= k2).
Proof.
  intros; eapply eutt_clo_bind_gen.
  reflexivity.
  intros * IN _ <-; eauto.
Qed.
