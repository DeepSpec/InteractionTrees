(** * Theorems about the traced monoidal category of KTrees *)

(** More precisely, facts about the trace operator [loop].
    The coinductive reasoning is all done in [LoopFacts], and
    this package just repackages it into nice categorical equations.

    The monoidal category structure is verified in
    [ITree.Core.KTreeBasicFacts].
 *)

(* begin hide *)
Require Import Paco.paco.

From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.Function
     Basics.FunctionFacts
     Core.ITreeDefinition
     Core.KTree
     Eq.Eq
     Eq.UpToTaus.

From ITree Require Export
     Core.KTreeBasicFacts.

From ITree Require Export
     Core.LoopFacts.

Import ITreeNotations.
Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.
(* end hide *)

(** *** Traced monoidal categories *)

Section TraceLaws.

Local Opaque eqit loop ITree.bind'.

Context {E : Type -> Type}.

Local Open Scope cat.

(** *** [loop] lemmas *)

Global Instance eq_ktree_loop {I A B} :
  Proper (eq2 ==> eq2) (@loop E I A B).
Proof.
  repeat intro; apply eutt_loop; auto.
Qed.

(* Naturality of (loop_ktree I A B) in A *)
(* Or more diagrammatically:
[[
        +-----+
        | ### |
        +-###-+I
A----B----###----C
          ###

is equivalent to:

   +----------+
   |      ### |
   +------###-+I
A----B----###----C
          ###

]]
 *)

Lemma compose_loop {I A B C}
      (bc_: ktree E (I + B) (I + C)) (ab: ktree E A B) :
    loop (bimap (id_ _) ab >>> bc_)
  ⩯ ab >>> loop bc_.
Proof.
  intros a. cbv.
  rewrite bind_loop2.
  apply eutt_loop.
  clear a.
  intros [i | a']; cbn.
  - rewrite 2 bind_ret.
    reflexivity.
  - rewrite bind_bind. setoid_rewrite bind_ret.
    reflexivity.
Qed.

(* Naturality of (loop I A B) in B *)
(* Or more diagrammatically:
[[
   +-----+
   | ### |
   +-###-+I
A----###----B----C
     ###

is equivalent to:

   +----------+
   | ###      |
   +-###------+I
A----###----B----C
     ###

]]
 *)

Lemma loop_compose {I A B B'}
      (ab_: ktree E (I + A) (I + B)) (bc: ktree E B B') :
    loop (ab_ >>> bimap (id_ _) bc)
  ⩯ loop ab_ >>> bc.
Proof.
  intros a.
  cbv.
  rewrite bind_loop.
  apply eutt_loop.
  intros ia.
  einit. ebind. econstructor; try reflexivity.
  intros; subst. destruct u2.
  - rewrite bind_ret_; eauto with paco.
  - reflexivity.
Qed.

(* Dinaturality of (loop I A B) in I *)

Lemma loop_rename_internal {I J A B}
      (ab_: ktree E (I + A) (J + B)) (ji: ktree E J I) :
    loop (ab_ >>> bimap ji (id_ _))
  ⩯ loop (bimap ji (id_ _) >>> ab_).
Proof.
  assert (trans4: forall r s t u : ktree E A B,
             s ⩯ t -> r ⩯ s -> t ⩯ u -> r ⩯ u).
  { intros.
    do 2 (etransitivity; eauto). }
  eapply trans4.
  { intros a. erewrite (loop_bind ji ab_) at 1. reflexivity. }
  { apply eutt_loop; cbv; intros ia.
    einit. ebind. econstructor; try reflexivity.
    intros; subst. destruct u2.
    + rewrite tau_eutt. reflexivity.
    + rewrite bind_ret_. eauto with paco. }
  { apply eutt_loop. cbv. intros [].
    + einit. ebind. econstructor. 
      * eapply eqit_bind; try reflexivity.
        red; intros. rewrite tau_eutt. reflexivity.
      * intros; subst. reflexivity.
    + rewrite !bind_ret_; reflexivity. }
Qed.

(* Loop over the empty set can be erased *)
Lemma vanishing_ktree {A B: Type} (f: ktree E (void + A) (void + B)) :
  loop f ⩯ unit_l' >>> f >>> unit_l.
Proof.
  intros a.
  rewrite vanishing1_loop.
  cbv.
  rewrite bind_ret.
  einit. ebind. econstructor; try reflexivity.
  intros; subst. destruct u2; [contradiction|reflexivity]. 
Qed.

(* [loop_loop]:

These two loops:

[[
    n+----------+
    | +-----+  |
    | | ### |  |
    | +-###-+I |
    +---###----+J
  A-----###-------B
        ###
]]

... can be rewired as a single one:


[[
     +-------+
     |  ###  |
     +--###--+(I+J)
     +--###--+
  A-----###-----B
        ###
]]

 *)

Lemma loop_loop {I J A B} (ab__: ktree E (I + (J + A)) (I + (J + B))) :
    loop (loop ab__)
  ⩯ loop (assoc_r >>> ab__ >>> assoc_l).
Proof.
  intros a.
  rewrite vanishing2_loop.
  cbv.
  apply eutt_loop.
  intros [[]|]; cbn.
  all: rewrite !bind_bind.
  all: try rewrite !bind_ret_.
  all: einit; ebind; econstructor; try reflexivity.
  all: intros; subst; destruct u2; try rewrite bind_ret_; try reflexivity.
  all: destruct s; try rewrite bind_ret_; reflexivity.
Qed.

Lemma fold_map {R S}:
  forall (f: R -> S) (t: itree E R),
    (x <- t;; Ret (f x)) ≅ (ITree.map f t).
Proof.
  intros; reflexivity.
Qed.

Local Transparent loop.

Lemma bimap_ktree_loop {I A B C D}
      (ab : ktree E (I + A) (I + B)) (cd : ktree E C D) :
    bimap (loop ab) cd
  ⩯ loop (assoc_l >>> bimap ab cd >>> assoc_r).
Proof.
  rewrite assoc_l_ktree, assoc_r_ktree.
  rewrite lift_compose_ktree, compose_ktree_lift.
  remember @loop as l; cbv.
  intros []; subst l.
  - rewrite fold_map.
    rewrite (@superposing1_loop E A B I C D).
    apply eutt_loop.
    cbv; intros [|[]].
    all: symmetry. (* protect the existential. *)
    all: rewrite bind_bind.
    all: setoid_rewrite bind_ret at 1.
    all: reflexivity.
  - unfold loop.
    autorewrite with itree.
    einit. ebind. econstructor; try reflexivity.
    intros. subst.
    autorewrite with itree.
    rewrite unfold_aloop'_; cbn. reflexivity.
Qed.

(** Utility: lemma to ease working forward in an equational proof.
      Make it more convenient to rewrite subterm only on one side of the equation.
 *)
Fact fwd_eqn {a b : Type} (f g : ktree E a b) :
  (forall h, h ⩯ f -> h ⩯ g) -> f ⩯ g.
Proof.
  intro H; apply H; reflexivity.
Qed.

(** Utility: lemmas to ease forward reasoning *)
Fact cat_eq2_l {a b c : Type} (h : ktree E a b) (f g : ktree E b c) :
  f ⩯ g ->
  h >>> f ⩯ h >>> g.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Fact cat_eq2_r {a b c : Type} (h : ktree E b c) (f g : ktree E a b) :
  f ⩯ g ->
  f >>> h ⩯ g >>> h.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Fact local_rewrite1 {a b c : Type}:
  bimap (id_ a) (@swap _ (ktree E) _ _ b c) >>> assoc_l >>> swap
        ⩯ assoc_l >>> bimap swap (id_ c) >>> assoc_r.
Proof.
  symmetry.
  apply fwd_eqn; intros h Eq.
  do 2 apply (cat_eq2_l (bimap (id_ _) swap)) in Eq.
  rewrite <- cat_assoc, bimap_cat, swap_involutive, cat_id_l,
  bimap_id, cat_id_l in Eq.
  rewrite <- (cat_assoc _ _ _ assoc_r), <- (cat_assoc _ _ assoc_l _)
    in Eq.
  rewrite <- swap_assoc_l in Eq.
  rewrite (cat_assoc _ _ _ assoc_r) in Eq.
  rewrite assoc_l_mono in Eq.
  rewrite cat_id_r in Eq.
  rewrite cat_assoc.
  assumption.
  all: typeclasses eauto.
Qed.

Fact local_rewrite2 {a b c : Type}:
  swap >>> assoc_r >>> bimap (id_ _) swap
       ⩯ @assoc_l _ (ktree E) _ _ a b c >>> bimap swap (id_ _) >>> assoc_r.
Proof.
  symmetry.
  apply fwd_eqn; intros h Eq.
  do 2 apply (cat_eq2_r (bimap (id_ _) swap)) in Eq.
  rewrite cat_assoc, bimap_cat, swap_involutive, cat_id_l,
  bimap_id, cat_id_r in Eq.
  rewrite 2 (cat_assoc _ assoc_l) in Eq.
  rewrite <- swap_assoc_r in Eq.
  rewrite <- 2 (cat_assoc _ assoc_l) in Eq.
  rewrite assoc_l_mono, cat_id_l in Eq.
  assumption.
  all: try typeclasses eauto.
Qed.

Lemma loop_bimap_ktree {I A B C D}
      (ab : ktree E A B) (cd : ktree E (I + C) (I + D)) :
  bimap ab (loop cd)
        ⩯ loop (assoc_l >>> bimap swap (id_ _)
                        >>> assoc_r
                        >>> bimap ab cd
                        >>> assoc_l >>> bimap swap (id_ _) >>> assoc_r).
Proof.
  rewrite swap_bimap, bimap_ktree_loop.
  rewrite <- compose_loop, <- loop_compose.
  rewrite (swap_bimap _ _ cd ab).
  rewrite <- !cat_assoc.
  rewrite local_rewrite1.
  rewrite 2 cat_assoc.
  rewrite <- (cat_assoc _ swap assoc_r).
  rewrite local_rewrite2.
  rewrite <- !cat_assoc.
  reflexivity.
  all: typeclasses eauto.
Qed.

Lemma yanking_ktree {A: Type}:
  @loop E _ _ _ swap ⩯ id_ A.
Proof.
  intros ?; rewrite yanking_loop. rewrite tau_eutt. reflexivity.
Qed.

Lemma loop_rename_internal' {I J A B} (ij : ktree E I J) (ji: ktree E J I)
      (ab_: @ktree E (I + A) (I + B)) :
  (ij >>> ji) ⩯ id_ _ ->
    loop (bimap ji (id_ _) >>> ab_ >>> bimap ij (id_ _))
  ⩯ loop ab_.
Proof.
  intros Hij.
  rewrite loop_rename_internal.
  rewrite <- cat_assoc.
  rewrite bimap_cat.
  rewrite Hij.
  rewrite cat_id_l.
  rewrite bimap_id.
  rewrite cat_id_l.
  reflexivity.
  all: try typeclasses eauto.
Qed.

End TraceLaws.

Hint Rewrite @bimap_id_lift : lift_ktree.
Hint Rewrite @bimap_lift_id : lift_ktree.
Hint Rewrite @lift_case_sum : lift_ktree.

(* Here we show that we can implement [ITree.cat] using
   [bimap], [loop], and composition with the monoidal
   natural isomorphisms. *)

(* [cat_from_loop]:

      +-------------+
      |             |
      +---\/---ab---+
   -------/\---bc-------

is equivalent to

   ----ab---bc----
 *)
Theorem cat_from_loop {E A B C} (ab : ktree E A B) (bc : ktree E B C) :
  loop (swap >>> bimap ab bc) ⩯ ab >>> bc.
Proof with try typeclasses eauto.
(*
      +-------------+
      |             |
      +---\/---ab---+
   -------/\---bc-------
 *)

  rewrite bimap_slide...
  rewrite <- cat_assoc...
(*
      +----------------+
      |                |
      +---\/---ab------+
   -------/\------bc-------
 *)

  rewrite loop_compose...
(*
      +-------------+
      |             |
      +---\/---ab---+
   -------/\------------bc----
 *)

  rewrite swap_bimap...
  rewrite <- !cat_assoc...
(*
      +-------------------+
      |                   |
      +---\/--\/------\/--+
   -------/\--/\--ab--/\----bc----
 *)

  rewrite swap_involutive, cat_id_l...
(*
      +-------------------+
      |                   |
      +---------------\/--+
   ---------------ab--/\----bc----
 *)

  rewrite compose_loop...
(*
           +------+
           |      |
           +--\/--+
   ----ab-----/\-----bc----
 *)

  rewrite yanking_ktree...
  rewrite cat_id_r...
(*
   ----ab---bc----
 *)

  reflexivity.
Qed.
