(** * Leaves of an Interaction Tree *)

(* begin hide *)
From ExtLib Require Import Data.Monads.StateMonad.

From ITree Require Import
     Basics.Utils
     Basics.HeterogeneousRelations
     ITree
     Eq.Shallow
     Eq.Eqit
     Interp.InterpFacts
     Events.State
     Events.StateFacts
     Props.HasPost.

From Paco Require Import paco.
From Coq Require Import Morphisms Basics Program.Equality.
Import ITree.
Import ITreeNotations.
(* end hide *)

(** ** Leaves of itrees *)

(** The [Leaf a t] predicate expresses that [t] has a [Ret] leaf with
    value [a].

    We provide the elementary structural lemmas to work with this
    predicate, and one main useful result relying on [Leaf]: the
    up-to bind closure [eqit_bind_clo] can be refined such that
    continuations need only be related over the leaves of the
    first operand of [bind].
    *)

Inductive Leaf {E} {A: Type} (a: A) : itree E A -> Prop :=
 | LeafRet: forall t,
   observe t = RetF a ->
   Leaf a t
 | LeafTau: forall t u,
   observe t = TauF u ->
   Leaf a u ->
   Leaf a t
 | LeafVis: forall {X} (e: E X) t k x,
   observe t = VisF e k ->
   Leaf a (k x) ->
   Leaf a t
.
#[global] Hint Constructors Leaf : itree.

Module LeafNotations.
  Notation "a ∈ t" := (Leaf a t) (at level 70).
End LeafNotations.

Import LeafNotations.

(** Smart constructors *)

Lemma Leaf_Ret : forall E R a,
  a ∈ (Ret a : itree E R).
Proof.
  intros; econstructor; reflexivity.
Qed.

Lemma Leaf_Tau : forall E R a t,
  a ∈ (t : itree E R) ->
  a ∈ Tau t.
Proof.
  intros; econstructor; [reflexivity | eauto].
Qed.

Lemma Leaf_Vis : forall E X Y (e : E X) (k : _ -> itree E Y) b x,
  b ∈ (k x) ->
  b ∈ (Vis e k).
Proof.
  intros * IN; econstructor 3; [reflexivity | eauto].
Qed.

(** Inversion lemmas *)
Lemma Leaf_Ret_inv : forall E R (a b : R),
  Leaf (E := E) b (Ret a) ->
  b = a.
Proof.
  intros * IN; inv IN; cbn in *; try congruence.
Qed.

Lemma Leaf_Tau_inv : forall E R (u : itree E R) b,
  b ∈ Tau u ->
  b ∈ u.
Proof.
  intros * IN; inv IN; cbn in *; try congruence.
Qed.

Lemma Leaf_Vis_inv : forall E X Y (e : E X) (k : _ -> itree E Y) b,
  b ∈ Vis e k ->
  exists x, b ∈ k x.
Proof.
  intros * IN *; inv IN; cbn in *; try congruence.
  revert x H0.
  refine (match H in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
  eauto.
Qed.

(** Closure under [eutt]

  General asymmetric lemmas for [eutt R], where we naturally get
  a different point related by [R], and [Proper] instances for
  [eutt eq]. *)

Lemma Leaf_eutt_l {E A B R}:
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
    + inv Heqi; eauto with itree.
    + edestruct IHEQ as (b & IN & HR); eauto with itree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H t.
    remember (TauF u); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot; inv Heqi.
    + edestruct IHFIN as (? & ? & ?); [ .. | eexists ]; eauto with itree.
    + eauto with itree.
    + edestruct IHEQ as (? & ? & ?); [ .. | eexists ]; eauto with itree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H t.
    remember (VisF e k); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot.
    + revert x FIN IHFIN.
      refine (match Heqi in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
      intros. edestruct IHFIN as (? & ? & ?); [ | eexists ]; eauto with itree.
    + edestruct IHEQ as (? & ? & ?); [.. | exists x0 ]; eauto with itree.
Qed.

Lemma Leaf_eutt_r {E A B R}:
  forall (t : itree E A) (u : itree E B) (b : B),
  eutt R t u ->
  b ∈ u ->
  exists a, a ∈ t /\ R a b.
Proof.
  intros * EQ FIN.
  apply eqit_flip in EQ.
  revert EQ FIN.
  apply @Leaf_eutt_l.
Qed.

#[global] Instance Leaf_eutt {E A}:
  Proper (eq ==> eutt eq ==> iff) (@Leaf E A).
Proof.
  apply proper_sym_impl_iff_2; [ exact _ .. | ].
  unfold Proper, respectful, impl. intros; subst.
  edestruct @Leaf_eutt_l as [? []]; try eassumption; subst; assumption.
Qed.

(** Compatibility with [bind], forward and backward *)

Lemma Leaf_bind : forall {E R S}
  (t : itree E R) (k : R -> itree E S) a b,
  b ∈ t ->
  a ∈ k b ->
  a ∈ t >>= k.
Proof.
  intros * INt INk; induction INt.
  - rewrite (itree_eta t), H, bind_ret_l; auto.
  - rewrite (itree_eta t), H, tau_eutt; auto.
  - rewrite (itree_eta t), H, bind_vis.
    apply Leaf_Vis with x; auto.
Qed.

Lemma Leaf_bind_inv : forall {E R S}
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
    exists r; auto with itree.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence; [ eexists; eauto with itree | ].
    inversion H; clear H; symmetry in H1.
    edestruct IHFIN as (? & ? & ?); [ eauto | eexists; eauto with itree ].
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence; [ eexists; eauto with itree | ].
    revert x FIN IHFIN.
    refine (match H in _ = u return match u with VisF e0 k0 => _ | RetF _ | TauF _ => False end with eq_refl => _ end).
    intros.
    edestruct IHFIN as (? & ? & ?); [ reflexivity | eexists; eauto with itree ].
Qed.

(** Leaf-aware up-to bind closure
    This construction generalizes [eqit_bind_clo]: one can
    indeed provide an arbitrary cut at the relational
    redicate [RU] of one's choice, but the continuations
    are only required to be related pointwise at the intersection
    of [RU] with the respective leaves of the prefixes.
  *)
Section LeafBind.

  Context {E : Type -> Type} {R S : Type}.

  Local Open Scope itree.

  Inductive eqit_Leaf_bind_clo b1 b2 (r : itree E R -> itree E S -> Prop) :
    itree E R -> itree E S -> Prop :=
  | pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop)
                (t1 : itree E U1) (t2 : itree E U2)
                 (k1 : U1 -> itree E R) (k2 : U2 -> itree E S)
                (EQV: eqit RU b1 b2 t1 t2)
                (REL: forall u1 u2,
                      u1 ∈ t1 -> u2 ∈ t2 -> RU u1 u2 ->
                      r (k1 u1) (k2 u2))
      : eqit_Leaf_bind_clo b1 b2 r
            (ITree.bind t1 k1) (ITree.bind t2 k2)
    .
  Hint Constructors eqit_Leaf_bind_clo : itree.

  Lemma eqit_Leaf_clo_bind  (RS : R -> S -> Prop) b1 b2 vclo
        (MON: monotone2 vclo)
        (CMP: compose (eqitC RS b1 b2) vclo <3= compose vclo (eqitC RS b1 b2))
        (ID: id <3= vclo):
    eqit_Leaf_bind_clo b1 b2 <3= gupaco2 (eqit_ RS b1 b2 vclo) (eqitC RS b1 b2).
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
      apply REL0; auto with itree.
    - gstep. econstructor.
      gbase.
      apply CIH.
      econstructor; eauto with itree.
    - gstep. econstructor.
      intros; apply ID; unfold id.
      gbase.
      apply CIH.
      econstructor; eauto with itree.
    - destruct b1; try discriminate.
      guclo eqit_clo_trans.
      econstructor.
      3:{ eapply IHEQV; eauto with itree. }
      3,4:auto_ctrans_eq.
      2: reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-itree_eta. reflexivity.
    - destruct b2; try discriminate.
      guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; eauto with itree; try reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-itree_eta. reflexivity.
  Qed.

End LeafBind.

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
    ginit. guclo (@eqit_Leaf_clo_bind E R1 R2).
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

Lemma eqit_bind_Leaf_inv {E} {R S T} (RS : R -> S -> Prop)
      (t : itree E T)  (k1: T -> itree E R) (k2 : T -> itree E S) :
  (eutt RS  (ITree.bind t k1) (ITree.bind t k2)) ->
  (forall r, Leaf r t -> eutt RS (k1 r) (k2 r)).
Proof.
  intros EQIT r HRET.
  revert k1 k2 EQIT.
  induction HRET; intros;
    rewrite 2 unfold_bind, H in EQIT.
  - assumption.
  - rewrite 2 tau_eutt in EQIT. auto.
  - apply IHHRET. eapply eqit_inv_Vis in EQIT; eauto.
Qed.

(** Correspondence with has_post *)

Lemma has_post_Leaf {E R} (t: itree E R) Q r:
  has_post t Q -> r ∈ t -> Q r.
Proof.
  intros Hcond Himage.
  rewrite has_post_post_strong in Hcond.
  destruct (Leaf_eutt_l t t r Hcond Himage).
  intuition; now subst.
Qed.

Lemma has_post_Leaf_equiv {E R} (t: itree E R) Q:
  has_post t Q <-> (forall r, r ∈ t -> Q r).
Proof.
  intuition. eapply has_post_Leaf; eauto.
  revert t H. pcofix CIH; intros t Hpost. pstep; red.
  setoid_rewrite (itree_eta t) in Hpost.
  desobs t Ht; clear t Ht.
  - constructor. apply Hpost, Leaf_Ret.
  - constructor. right; apply CIH. intros. apply Hpost, Leaf_Tau, H.
  - constructor. intros. right. apply CIH. intros. eapply Hpost, Leaf_Vis, H.
Qed.

(** Leaf-based inversion principles for iter *)

(* Inverts [r ∈ ITree.iter body entry] into any post-condition on r which is
   satisfied by terminating iterations of the body. *)
Lemma Leaf_iter_inv {E R I}:
  forall (body: I -> itree E (I + R)) (entry: I) (Inv: I -> Prop) (Q: R -> Prop),
  (forall i r, Inv i -> r ∈ body i -> sum_pred Inv Q r) ->
  Inv entry ->
  forall r, r ∈ (ITree.iter body entry) -> Q r.
Proof.
  intros * Hinv Hentry.
  rewrite <- has_post_Leaf_equiv.
  eapply has_post_iter_strong; eauto.
  setoid_rewrite has_post_Leaf_equiv. eauto.
Qed.

Lemma Leaf_interp_iter_inv {E F R I} (h: E ~> itree F):
  forall (body: I -> itree E (I + R)) (entry: I) (Inv: I -> Prop) (Q: R -> Prop),
  (forall i r, Inv i -> r ∈ interp h (body i) -> sum_pred Inv Q r) ->
  Inv entry ->
  forall r, r ∈ interp h (ITree.iter body entry) -> Q r.
Proof.
  intros * Hbody Hentry r Hr.
  apply (Leaf_iter_inv (fun i => interp h (body i)) entry Inv); auto.
  rewrite (interp_iter'  _ _ (fun i => interp h (body i))) in Hr.
  apply Hr. reflexivity.
Qed.

(* Inverts [sr' ∈ interp_state h (ITree.iter body i)] into a post-condition on
   both retun value and state, like Leaf_iter_inv. *)
Lemma Leaf_interp_state_iter_inv {E F S R I}:
  forall (h: E ~> stateT S (itree F)) (body: I -> itree E (I + R))
         (RS: S -> Prop) (RI: I -> Prop) (RR: R -> Prop) (s: S) (i: I),
  (forall s i, RS s -> RI i -> (forall sx', sx' ∈ runStateT (interp_state h (body i)) s ->
                    prod_pred (sum_pred RI RR) RS sx')) ->
  RS s -> RI i ->
  forall sr', sr' ∈ runStateT (interp_state h (ITree.iter body i)) s -> prod_pred RR RS sr'.
Proof.
  setoid_rewrite <- has_post_Leaf_equiv.
  setoid_rewrite has_post_post_strong.
  intros * Hinv Hentrys Hentryi.
  set (eRI := fun (i1 i2: I) => i1 = i2 /\ RI i1).
  set (eRR := fun (r1 r2: R) => r1 = r2 /\ RR r1).
  set (eRS := fun (s1 s2: S) => s1 = s2 /\ RS s1).

  set (R1 := (fun x y : R * S => x = y /\ prod_pred RR RS x)).
  set (R2 := (fun a b : R * S => eRR (fst a) (fst b) /\ eRS (snd a) (snd b))).
  assert (HR1R2: eq_rel R1 R2) by (compute; intuition; subst; now try destruct y).
  unfold has_post_strong; fold R1; rewrite (eutt_equiv _ _ HR1R2).

  unshelve eapply (eutt_interp_state_iter eRI eRR eRS h body body _ i i s s _ _);
  [| subst eRS; intuition | subst eRI; intuition].
  intros i1 ? s1 ? [<- Hs1] [<- Hi1].

  set (R3 := (fun x y : (I + R) * S => x = y /\ prod_pred (sum_pred RI RR) RS x)).
  set (R4 := (prod_rel (sum_rel eRI eRR) eRS)).
  assert (HR3R4: eq_rel R3 R4).
  { split; intros [[|] ?] [[|] ?]; compute.
    1-4: intros [[]]; dintuition; cbn; intuition.
    all: intros [HZ [[=->] ?]]; inversion HZ; intuition now subst. }

  rewrite <- (eutt_equiv _ _ HR3R4).
  now apply Hinv.
Qed.

(** Inversion of Leaf through interp.
    Since interp does not change leaves, we have [x ∈ interp h t -> x ∈ t].
    However this is not easy to see from the Leaf predicate; we must use t. *)

Module Subtree.

Inductive subtree {E R}: itree E R -> itree E R -> Prop :=
  | SubtreeRefl u t:
      u ≅ t -> subtree u t
  | SubtreeTau u t:
      subtree (Tau u) t -> subtree u t
  | SubtreeVis {T} u (e: E T) k x t:
      u ≅ k x -> subtree (Vis e k) t -> subtree u t.

#[global] Instance subtree_cong_eqitree {E R}:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl) (@subtree E R).
Proof.
  intros t t' Ht u u' Hu Hsub.
  revert t Ht u Hu; induction Hsub; intros.
  - apply SubtreeRefl. now rewrite Ht, Hu.
  - apply SubtreeTau, IHHsub; auto. apply eqit_Tau, Ht.
  - eapply SubtreeVis. now rewrite Ht, H. apply IHHsub; auto. reflexivity.
Qed.

Lemma subtree_image {E R} (t u: itree E R) x:
  subtree u t -> x ∈ u -> x ∈ t.
Proof.
  intros * Hsub. induction Hsub; intros.
  - intros. rewrite <- H; auto.
  - apply IHHsub, Leaf_Tau, H.
  - eapply IHHsub, Leaf_Vis. rewrite H in H0; eauto.
Qed.

Lemma Leaf_interp_subtree_inv {E F R} (h: E ~> itree F) (t u: itree E R):
  subtree u t -> has_post (interp h u) (fun x : R => x ∈ t).
Proof.
  revert t u. ginit. gcofix CIH; intros * Hsub.
  rewrite (itree_eta u) in Hsub.
  rewrite ! unfold_interp.
  desobs u Hu; clear u Hu; cbn.
  - gstep; red. constructor. eapply subtree_image; eauto. apply Leaf_Ret.
  - gstep; red. constructor. gfinal; left. apply CIH. apply SubtreeTau, Hsub.
  - guclo eqit_clo_bind; econstructor. reflexivity. intros u _ <-.
    gstep; red. constructor. gfinal; left. apply CIH. eapply SubtreeVis, Hsub.
    reflexivity.
Qed.

Lemma Leaf_interp_state_subtree_inv {E F S R} (h: E ~> stateT S (itree F))
  (t u: itree E R) (s: S):
  subtree u t -> has_post (runStateT (interp_state h u) s) (fun x => fst x ∈ t).
Proof.
  revert t u s. ginit. gcofix CIH; intros * Hsub.
  rewrite (itree_eta u) in Hsub.
  rewrite ! unfold_interp_state.
  desobs u Hu; clear u Hu; cbn.
  - gstep; red. constructor. eapply subtree_image; eauto. apply Leaf_Ret.
  - gstep; red. constructor. gfinal; left. apply CIH. apply SubtreeTau, Hsub.
  - guclo eqit_clo_bind; econstructor. reflexivity. intros [u1 u2] _ <-; cbn.
    gstep; red. constructor. gfinal; left. apply CIH. eapply SubtreeVis, Hsub.
    reflexivity.
Qed.

End Subtree.
Import Subtree.

Lemma Leaf_interp_inv {E F R} (h: E ~> itree F) (t: itree E R) x:
  x ∈ interp h t -> x ∈ t.
Proof.
  intros Hleaf. apply (has_post_Leaf (interp h t) (fun x => x ∈ t)); auto.
  apply Leaf_interp_subtree_inv. apply SubtreeRefl; reflexivity.
Qed.

Lemma Leaf_interp_state_inv {E F S R} (h: E ~> stateT S (itree F))
  (t: itree E R) s x:
  x ∈ runStateT (interp_state h t) s -> fst x ∈ t.
Proof.
  intros Hleaf.
  apply (has_post_Leaf (runStateT (interp_state h t) s) (fun x => fst x ∈ t)); auto.
  apply Leaf_interp_state_subtree_inv. apply SubtreeRefl; reflexivity.
Qed.

(** Inversion through translate. *)

Lemma Leaf_translate_inv {E F R} `{Inj: E -< F}: forall (t: itree E R) v,
  v ∈ translate (@subevent E F _) t -> v ∈ t.
Proof.
  intros. rewrite translate_to_interp in H.
  eapply Leaf_interp_inv; eauto.
Qed.
