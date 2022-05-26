(** * Finite Interaction Tree *)

(* begin hide *)
From ITree Require Import
     ITree
     Basics.Tacs
     Eq.Eqit
     Leaf.
From ITree.Events Require Import Nondeterminism Exception. (* For counterexamples *)

From Paco Require Import paco.
From Coq Require Import Morphisms Basics Program.Equality.
Import ITree.
Import ITreeNotations.
Import LeafNotations.
(* end hide *)

(** ** Finite computations as Interaction Trees

  We provide two predicates capturing finiteness of an [itree]:
  - [all_finite t] expresses that [t] is finite along all branches
  - [any_finite t] expresses that [t] admits a finite branch

  In each case, we prove:
  - Smart constructors and inversion lemmas
  - Closure under [eutt R] (in the case of [Leaf], we get another value related by R) and Proper instances for [eutt eq]
  - Forward and backward proof rules for [bind]s
  We additionally provide:
  - Particular cases of non-interactive computations and [spin]
  - Counterexamples to properties that could be expected at first glance
*)

(** Definitions *)

(** all_finite t
  The tree admits exclusively finite branches *)
Inductive all_finite {E} {A: Type} : itree E A -> Prop :=
 | all_finiteRet: forall a t,
    observe t = RetF a ->
   all_finite t
 | all_finiteTau: forall t u,
   observe t = TauF u ->
   all_finite u ->
   all_finite t
 | all_finiteVis: forall {X} (e: E X) t k,
   observe t = VisF e k ->
   (forall x, all_finite (k x)) ->
   all_finite t
.
#[global] Hint Constructors all_finite : itree.

(** any_finite t
  The tree admits at least one finite branch *)
Inductive any_finite {E} {A: Type} : itree E A -> Prop :=
 | any_finiteRet: forall a t,
    observe t = RetF a ->
   any_finite t
 | any_finiteTau: forall t u,
   observe t = TauF u ->
   any_finite u ->
   any_finite t
 | any_finiteVis: forall {X} (e: E X) t k x,
   observe t = VisF e k ->
   any_finite (k x) ->
   any_finite t
.
#[global] Hint Constructors any_finite : itree.

(** Smart constructors *)

(* all_finite *)
Lemma all_finite_Ret : forall E R a,
  @all_finite E R (Ret a).
Proof.
  intros; econstructor 1; reflexivity.
Qed.
#[global] Hint Resolve all_finite_Ret : itree.

Lemma all_finite_Tau : forall E R t,
  all_finite t ->
  @all_finite E R (Tau t).
Proof.
  intros; econstructor 2; [reflexivity | eauto].
Qed.
#[global] Hint Resolve all_finite_Tau : itree.

Lemma all_finite_Vis : forall E X R (e : E X) k,
  (forall x, all_finite (k x)) ->
  @all_finite E R (Vis e k).
Proof.
  intros; econstructor 3; [reflexivity | eauto].
Qed.
#[global] Hint Resolve all_finite_Vis : itree.

(* any_finite *)
Lemma any_finite_Ret : forall E R a,
  @any_finite E R (Ret a).
Proof.
  intros; econstructor 1; reflexivity.
Qed.
#[global] Hint Resolve any_finite_Ret : itree.

Lemma any_finite_Tau : forall E R t,
  any_finite t ->
  @any_finite E R (Tau t).
Proof.
  intros; econstructor 2; [reflexivity | eauto].
Qed.
#[global] Hint Resolve any_finite_Tau : itree.

Lemma any_finite_Vis : forall E X R (e : E X) k x,
  any_finite (k x) ->
  @any_finite E R (Vis e k).
Proof.
  intros; econstructor 3; [reflexivity | eauto].
Qed.
#[global] Hint Resolve any_finite_Vis : itree.

(** Inversion lemmas *)

(* all_finite *)
Lemma all_finite_Tau_inv : forall E R t,
  @all_finite E R (Tau t) ->
  all_finite t.
Proof.
  intros * FIN; inv FIN; cbn in *; congruence.
Qed.

Lemma all_finite_Vis_inv : forall E X R (e : E X) k,
  @all_finite E R (Vis e k) ->
  forall x, all_finite (k x).
Proof.
  intros * FIN x; inv FIN; cbn in *; try congruence.
  revert H0.
  refine (match H in _ = u return match u with VisF e0 k0 => _ | _ => False end with eq_refl => _ end).
  auto.
Qed.

(* any_finite *)
Lemma any_finite_Tau_inv : forall E R t,
  @any_finite E R (Tau t) ->
  any_finite t.
Proof.
  intros * FIN; inv FIN; cbn in *; congruence.
Qed.

Lemma any_finite_Vis_inv : forall E X R (e : E X) k,
  @any_finite E R (Vis e k) ->
  exists x, any_finite (k x).
Proof.
  intros * FIN; inv FIN; cbn in *; try congruence.
  revert x H0.
  refine (match H in _ = u return match u with VisF e0 k0 => _ | _ => False end with eq_refl => _ end).
  eauto.
Qed.

(** Closure under [eutt]

  General asymetric lemmas for [eutt R], and [Proper]
  instances for [eutt eq]. *)

(* all_finite *)
Lemma all_finite_eutt_l {E A B R}:
  forall (t : itree E A) (u : itree E B),
  eutt R t u ->
  all_finite t ->
  all_finite u.
Proof.
  intros * EQ FIN;
  revert u EQ.
  induction FIN; intros u2 EQ.
  - punfold EQ.
    red in EQ; rewrite H in EQ; clear H.
    remember (RetF a); genobs u2 ou.
    hinduction EQ before R; intros; try discriminate; eauto with itree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H.
    remember (TauF u); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot; inv Heqi; eauto with itree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H.
    remember (VisF e k); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot.
    + revert H0 H1.
      refine (match Heqi in _ = u return match u with VisF e0 k0 => _ | _ => False end with eq_refl => _ end).
      eauto with itree.
    + inv Heqi; eauto with itree.
Qed.

Lemma all_finite_eutt_r {E A B R}:
  forall (t : itree E A) (u : itree E B),
  eutt R t u ->
  all_finite u ->
  all_finite t.
Proof.
  intros * EQ. apply eqit_flip in EQ. revert EQ. apply all_finite_eutt_l.
Qed.

#[global] Instance all_finite_eutt {E A R}:
  Proper (eutt R ==> iff) (@all_finite E A).
Proof.
  repeat intro; split.
  - eapply all_finite_eutt_l; eauto.
  - eapply all_finite_eutt_r; eauto.
Qed.

(* any_finite *)
Lemma any_finite_eutt_l {E A B R}:
  forall (t : itree E A) (u : itree E B),
  eutt R t u ->
  any_finite t ->
  any_finite u.
Proof.
  intros * EQ FIN;
  revert u EQ.
  induction FIN; intros u2 EQ.
  - punfold EQ.
    red in EQ; rewrite H in EQ; clear H.
    remember (RetF a); genobs u2 ou.
    hinduction EQ before R; intros; try discriminate; eauto with itree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H.
    remember (TauF u); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot; inv Heqi; eauto with itree.
  - punfold EQ; red in EQ; rewrite H in EQ; clear H.
    remember (VisF e k); genobs u2 ou2.
    hinduction EQ before R; intros; try discriminate; pclearbot.
    + revert x FIN IHFIN.
      refine (match Heqi in _ = u return match u with VisF e0 k0 => _ | _ => False end with eq_refl => _ end).
      eauto with itree.
    + inv Heqi; eauto with itree.
Qed.

Lemma any_finite_eutt_r {E A B R}:
  forall (t : itree E A) (u : itree E B),
  eutt R t u ->
  any_finite u ->
  any_finite t.
Proof.
  intros * EQ. apply eqit_flip in EQ. revert EQ. apply any_finite_eutt_l.
Qed.

#[global] Instance any_finite_eutt {E A R}:
  Proper (eutt R ==> iff) (@any_finite E A).
Proof.
  split.
  eapply any_finite_eutt_l; eauto.
  eapply any_finite_eutt_r; eauto.
Qed.

(** Compatibility with [bind], forward and backward *)

(* all_finite *)

(* Only the reachable branches, as captured by the
    leaves in the image of the prefix, need to be
   finite in the continuation *)
Lemma all_finite_bind : forall {E R S}
  (t : itree E R) (k : R -> itree E S),
  all_finite t ->
  (forall x, x ∈ t -> all_finite (k x)) ->
  all_finite (t >>= k).
Proof.
  intros * FIN; induction FIN; intros FINs;
    rewrite unfold_bind, H; eauto with itree.
Qed.

Lemma all_finite_bind_weak : forall {E R S}
  (t : itree E R) (k : R -> itree E S),
  all_finite t ->
  (forall x, all_finite (k x)) ->
  all_finite (t >>= k).
Proof.
  intros; apply all_finite_bind; auto.
Qed.

(* We only get finiteness of the reachable branches *)
Lemma all_finite_bind_inv : forall {E R S}
  (t : itree E R) (k : R -> itree E S),
  all_finite (t >>= k) ->
  (all_finite t /\ forall x, x ∈ t -> all_finite (k x)).
Proof.
  intros E R S.
  cut (forall (u : itree E S), all_finite u ->
       forall (t : itree E R) k, u ≈ t >>= k ->
        (all_finite t /\ forall x, x ∈ t -> all_finite (k x))).
  intros LEM * FIN; eapply LEM; eauto; reflexivity.
  induction 1; intros * EQ.
  - rewrite (itree_eta t), H in EQ; clear H t.
    symmetry in EQ; apply eqit_inv_bind_ret in EQ as (? & EQt & EQk).
    rewrite EQt; split; auto with itree.
    intros z IN.
    rewrite EQt in IN; apply Leaf_Ret_inv in IN; subst.
    rewrite EQk; auto with itree.
  - rewrite (itree_eta t), H in EQ; clear H t.
    rewrite tau_eutt in EQ.
    eauto.
  - rewrite (itree_eta t), H in EQ; clear H t.
    symmetry in EQ; apply eutt_inv_bind_vis in EQ.
    destruct EQ as [(kca & EQ & EQk) | (?a & EQ & EQk)].
    + rewrite EQ.
      split.
      apply all_finite_Vis.
      intros ?; eapply H1; symmetry; eauto.
      intros x IN.
      rewrite EQ in IN.
      apply Leaf_Vis_inv in IN as (y & IN).
      edestruct H1 as (_ & H).
      symmetry in EQk; exact (EQk y).
      apply H, IN.
    + rewrite EQ; split; auto with itree.
      intros y IN.
      rewrite EQ in IN; apply Leaf_Ret_inv in IN; subst.
      rewrite EQk. eauto with itree.
Qed.

Lemma all_finite_bind_inv_left : forall {E R S}
  (t : itree E R) (k : R -> itree E S),
  all_finite (t >>= k) ->
  all_finite t.
Proof.
  intros; eapply all_finite_bind_inv; eauto.
Qed.

(* any_finite *)

(* For a [bind] to have a finite branch, we need to
   exhibit a finite branch in [t] that _continues_
   into a finite branch in [k]. We capture this
   continuity using [Leaf].
*)
Lemma any_finite_bind : forall {E R S}
  (t : itree E R) (k : R -> itree E S) x,
  x ∈ t ->
  any_finite (k x) ->
  any_finite (t >>= k).
Proof.
  intros * IN FIN; induction IN.
  - rewrite (itree_eta t), H, bind_ret_l; auto.
  - rewrite unfold_bind, H, tau_eutt; eauto.
  - rewrite unfold_bind, H.
    eapply any_finite_Vis; eauto.
Qed.

(* We get the additional guarantee that the
   finite branch in the continuation comes
   from a point in the image of the prefix.  *)
Lemma any_finite_bind_inv : forall {E R S}
  (t : itree E R) (k : R -> itree E S),
  any_finite (t >>= k) ->
  (any_finite t /\
   exists x, x ∈ t /\ any_finite (k x)).
Proof.
  intros * FIN;
  remember (ITree.bind t k) as u.
  revert t k Hequ.
  induction FIN; intros t' k' ->; rename t' into t.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence.
    split; eauto with itree.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence.
    split; eauto with itree.
    inversion H; clear H; symmetry in H1.
    edestruct IHFIN as (? & ? & ? & ?).
    apply H1.
    split; eauto with itree.
  - unfold observe in H; cbn in H.
    desobs t EQ; cbn in *; try congruence.
    split; eauto with itree.
    revert x FIN IHFIN.
    refine (match H in _ = u return match u with VisF e0 k0 => _ | _ => False end with eq_refl => _ end).
    intros.
    edestruct IHFIN as (? & ? & ? & ?); [ reflexivity | ].
    split; eauto with itree.
Qed.

Lemma any_finite_bind_inv_weak : forall {E R S}
  (t : itree E R) (k : R -> itree E S),
  any_finite (t >>= k) ->
  (any_finite t /\
   exists x, any_finite (k x)).
Proof.
  intros * FIN; apply any_finite_bind_inv in FIN as (?&?&?&?).
  split; eauto.
Qed.

Lemma any_finite_bind_inv_left : forall {E R S}
  (t : itree E R) (k : R -> itree E S),
  any_finite (t >>= k) ->
  any_finite t.
Proof.
  intros; eapply any_finite_bind_inv; eauto.
Qed.

(** * [any_finite] is non-empty [Leaf] *)
Lemma Leaf_finite : forall E R (t : itree E R) x,
  x ∈ t ->
  any_finite t.
Proof.
  intros * FIN; induction FIN; rewrite itree_eta, H; eauto with itree.
Qed.

Lemma finite_Leaf : forall E R (t : itree E R),
  any_finite t ->
  exists x, x ∈ t.
Proof.
  intros * FIN; induction FIN.
  1: exists a; rewrite itree_eta, H; eauto with itree.
  all: destruct IHFIN; eauto with itree.
Qed.

(** Degenerate case of non-interactive computations
  In the absence of interaction ([E = void1]), [all_finite] and [any_finite] collapse:
  we indeed both know that the computation is deterministic,
  and that it cannot fail, excluding hence any subtletly.
  The image is either empty, or a singleton.
*)

Lemma finite_non_interactive : forall X (t: itree void1 X),
  all_finite t <-> any_finite t.
Proof.
  split; induction 1; cbn in *; first [now destruct e | eauto with itree].
Qed.

Lemma finite_leaf_non_interactive : forall X (t: itree void1 X),
  all_finite t <-> (exists x, x ∈ t).
Proof.
  intros *.
  rewrite finite_non_interactive.
  split; [ eauto using finite_Leaf | intros []; eauto using Leaf_finite ].
Qed.

Lemma Leaf_non_interactive_singleton : forall X (t: itree void1 X) a b,
  a ∈ t -> b ∈ t -> a = b.
Proof.
  intros * IN; revert b; induction IN; intros * IN'.
  - rewrite itree_eta, H in IN'; apply Leaf_Ret_inv in IN'; auto.
  - rewrite itree_eta, H, tau_eutt in IN'; eauto.
  - inv e.
Qed.

(** [spin] is not finite, in any sense of the term *)
Lemma spin_not_all_finite: forall E X,
  ~ all_finite (@spin E X).
Proof.
  intros * FIN; remember spin as t; revert Heqt; induction FIN; intros ->;
  unfold observe in H; cbn in H; inv H; auto.
Qed.

Lemma spin_not_any_finite: forall E X,
  ~ any_finite (@spin E X).
Proof.
  intros * FIN; remember spin as t; revert Heqt; induction FIN; intros ->;
  unfold observe in H; cbn in H; inv H; auto.
Qed.

Lemma spin_empty_Leaf: forall E X x,
  ~ x ∈ (@spin E X).
Proof.
  intros * IN; apply Leaf_finite, spin_not_any_finite in IN; auto.
Qed.

Module Counterexamples.

(** * Counterexamples *)

(** Counterexamples to statements that could be expected to be true at firt glance. *)

(** [all_finite] does _not_ entail [any_finite].

  Indeed, [any_finite] guarantees that a finite branch exists,
  where [all_finite] enforces that no infinite branch exists.
  If the computation has no branch, [all_finite] can be satisfied
  while [any_finite] is not.
  The [fail] computation is the simplest counterexample *)

  Notation fail := (@throw unit (exceptE _) _ unit tt).

  Fact fail_all_finite: all_finite fail.
  Proof.
    unfold fail.
    apply all_finite_Vis; intros [].
  Qed.

  Fact fail_not_any_finite: ~ any_finite fail.
  Proof.
    unfold fail; intros FIN.
    apply any_finite_Vis_inv in FIN as ([] & ? & ?).
  Qed.

(** The [bind] proof rule for [any_finite] _must_ quantify
    on the [Leaf]
    It could be tempting to hope for a simpler lemma than
    [any_finite], simply ensure diamond on the prefix and
    at a point in the continuation:
    any_finite t ->
    any_finite (k x) ->
    any_finite (t >>= k)
    It is however primordial to ensure that the finite path exhibited by k
    is reachable for t, as illustrated in the following *)

  Definition t : itree nondetE bool :=
    or (Ret true) spin.

  Definition k : bool -> itree nondetE unit :=
    fun b => if b then spin else Ret tt.

  Lemma spin_not_any_finite: forall E X,
    ~ any_finite (@spin E X).
  Proof.
    intros * FIN; remember spin as t; revert Heqt; induction FIN; intros ->;
    unfold observe in H; cbn in H; inv H; auto.
  Qed.

  Fact DFt : any_finite t.
  Proof.
    apply any_finite_Vis with true; auto with itree.
  Qed.

  Fact DFk : any_finite (k false).
  Proof.
    cbn; auto with itree.
  Qed.

  Fact NotDFtk: ~ any_finite (t >>= k).
  Proof.
  intros abs.
  apply any_finite_bind_inv in abs as (FINt & b & IN & FINk).
  destruct b; cbn in *.
  - eapply spin_not_any_finite; eauto.
  - unfold t in IN.
    clear FINk FINt.
    inv IN; cbn in *; try congruence.
    dependent induction H.
    destruct x; cbn in *.
    apply Leaf_Ret_inv in H0; congruence.
    apply Leaf_finite in H0.
    eapply spin_not_any_finite; eauto.
  Qed.

End Counterexamples.
