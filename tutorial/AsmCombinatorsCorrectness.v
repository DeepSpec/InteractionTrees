Require Import Imp Asm AsmCombinators Label.

From Coq Require Import Morphisms.

From ITree Require Import
  SubKTree
  SubKTreeFacts
  ITree
  ITreeFacts.

Import CatNotations.
Local Open Scope cat_scope.

Section Correctness.

Section Category.

Ltac inl_left := rewrite <- (cat_assoc _ inl_).
Ltac inl_right := rewrite (cat_assoc _ inl_).
Ltac inr_left := rewrite <- (cat_assoc _ inr_).
Ltac inr_right := rewrite  (cat_assoc _ inr_).

Ltac run_in :=
  repeat (
      rewrite cat_id_l
    + rewrite <- (cat_assoc inl_ assoc_l), inl_assoc_l
    + rewrite <- (cat_assoc inl_ assoc_r), inl_assoc_r
    + rewrite <- (cat_assoc inr_ assoc_r), inr_assoc_r
    + rewrite <- (cat_assoc inr_ assoc_l), inr_assoc_l
    + rewrite <- (cat_assoc inl_ (bimap _ _)), inl_bimap
    + rewrite <- (cat_assoc inr_ (bimap _ _)), inr_bimap
    + rewrite <- (cat_assoc inl_ (case_ _ _)), case_inl
    + rewrite <- (cat_assoc inr_ (case_ _ _)), case_inr
    + rewrite <- (cat_assoc inl_ swap), inl_swap
    + rewrite <- (cat_assoc inr_ swap), inr_swap
    + rewrite <- (cat_assoc swap (case_ _ _)), swap_case
    + rewrite ?inl_assoc_l, ?inr_assoc_l, ?inl_assoc_r, ?inr_assoc_r,
      ?inl_bimap, ?inr_bimap, ?case_inl, ?case_inr
    ).

Context {obj : Type} {C : obj -> obj -> Type} {sum_ : obj -> obj -> obj}
  {Cat_C : Cat C} {Id_C : Id_ C}
  {Case_C : CoprodCase C sum_} {Inl_C : CoprodInl C sum_}
  {Inr_C : CoprodInr C sum_}
  {Eq2_C : Eq2 C}
  {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}
  {Category_C : Category C}
  {Coproduct_C : Coproduct C sum_}.

Local Infix "+" := sum_.

Local Lemma aux_app_asm_correct1 {i j a c : obj} :
    (assoc_r >>>
     bimap (id_ i) (assoc_l >>> bimap swap (id_ c) >>> assoc_r) >>>
     assoc_l)
  ⩯ bimap swap (id_ (a + c)) >>>
    (assoc_r >>>
    (bimap (id_ j) assoc_l >>>
    (assoc_l >>> (bimap swap (id_ c) >>> assoc_r)))).
Proof.
  autocat.
Qed.

Local Lemma aux_app_asm_correct2 {i j b d} :
    (assoc_r >>>
     bimap (id_ i) (assoc_l >>> bimap swap (id_ d) >>> assoc_r) >>>
     assoc_l)
  ⩯ assoc_l >>>
    (bimap swap (id_ d) >>>
    (assoc_r >>>
    (bimap (id_ j) assoc_r >>>
    (assoc_l >>> bimap swap (id_ (b + d)))))).
Proof.
  autocat.
Qed.

End Category.

Context {E : Type -> Type}.

Context {HasLocals : Locals -< E}.
Context {HasMemory : Memory -< E}.
Context {HasExit : Exit -< E}.

(** Correctness of the [app_asm] combinator.
    The resulting [asm] gets denoted to the bimap of its subcomponent.
    The proof is a bit more complicated. It makes a lot more sense if drawn.
 *)
Global Instance AppAsmCorrectProof : AppAsmCorrect.
Proof.
  red; intros.
  unfold denote_asm.
  (*
    On the left-hand-side, we have a [loop] of two [asm] mashed together.
    On the right-hand-side however we have two [loop]s combined together.
    The game is to massage them through successive rewriting until they
    line up.
   *)

  (* We first work on the rhs to reduce it to a single loop.
     The textual explanations are fairly cryptic. The key intuition comes
     by drawing the state of the circuit and using the rewiring laws
     the categorical structure provides, as represented for instance here:
     https://en.wikipedia.org/wiki/Traced_monoidal_category
     [bimap_ktree_loop] and [loop_bimap_ktree] are the _superposing_ laws.
     [compose_loop] and [loop_compose] are the _naturality_ in _X_ and _Y_.
     [loop_loop] is the second _vanishing_ law.
   *)
  match goal with | |- ?x ⩯ _ => set (lhs := x) end.
  rewrite loop_superposing.   (* a loop superposed atop another diagram can englob the latter *)
  rewrite loop_superposing_2. (* as well as if the loop is under... But it takes a bit more rewiring! *)
  rewrite loop_natural_right. (* a loop append to diagrams can swallow them... *)
  rewrite loop_natural_left.  (* ... from either side. *)
  rewrite loop_vanishing_2.   (* Finally, two nested loop can be combined. *)

  (* Remain now to relate the bodies of the loops on each side. *)
  (* First by some more equational reasoning. *)

  rewrite <- (loop_dinatural' swap swap) by apply swap_involutive.
  subst lhs.
  apply Proper_loop.
  rewrite !cat_assoc.
  repeat rewrite <- (cat_assoc _ _ (bimap (denote_b _) (denote_b _) >>> _)).
  cbn. rewrite relabel_bks_correct, app_bks_correct.

  rewrite <- aux_app_asm_correct1, <- aux_app_asm_correct2.

  rewrite <- !compose_lift_sktree.
  rewrite <- !bimap_id_slift.
  rewrite <- !compose_lift_sktree.
  rewrite <- !bimap_slift_id.
  rewrite <- !assoc_r_sktree, <- !assoc_l_sktree, !sym_sktree_unfold.
  reflexivity.
Qed.

End Correctness.
