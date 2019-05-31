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

Global Instance CatAssoc_iFun : CatAssoc iFun.
Proof.
  intros A B C D f g h.
  unfold cat, Cat_iFun.
  apply cat_Fun_assoc.
Qed.

Lemma bimap_inl
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif} {CaseInl_C : CaseInl C bif}:
  forall (a b c d : obj) (f : C a c) (g : C b d), inl_ >>> bimap f g ⩯ f >>> inl_.
Proof.
  intros; unfold bimap, Bimap_Coproduct.
  apply case_inl; typeclasses eauto.
Qed.

Lemma bimap_inr
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif} {CaseInr_C : CaseInr C bif}:
  forall (a b c d : obj) (f : C a c) (g : C b d), inr_ >>> bimap f g ⩯ g >>> inr_.
Proof.
  intros; unfold bimap, Bimap_Coproduct.
  apply case_inr; typeclasses eauto.
Qed.

Lemma assoc_r_inl
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
      {CaseInl_C : CaseInl C bif}:
  forall (a b c : obj), inl_ >>> @assoc_r _ _ _ _ a b c ⩯ case_ inl_ (inl_ >>> inr_).
Proof.
  intros; unfold assoc_r, AssocR_Coproduct; apply case_inl; typeclasses eauto.
Qed.

Lemma assoc_r_inr
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
      {CaseInr_C : CaseInr C bif}:
  forall (a b c : obj), inr_ >>> @assoc_r _ _ _ _ a b c ⩯ inr_ >>> inr_.
Proof.
  intros; unfold assoc_r, AssocR_Coproduct; apply case_inr; typeclasses eauto.
Qed.

Lemma assoc_l_inl
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
      {CaseInl_C : CaseInl C bif}:
  forall (a b c : obj), inl_ >>> @assoc_l _ _ _ _ a b c ⩯ inl_ >>> inl_.
Proof.
  intros; unfold assoc_l, AssocR_Coproduct; apply case_inl; typeclasses eauto.
Qed.

Lemma assoc_l_inr
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
      {CaseInr_C : CaseInr C bif}:
  forall (a b c : obj), inr_ >>> @assoc_l _ _ _ _ a b c ⩯ case_ (inr_ >>> inl_) inr_.
Proof.
  intros; unfold assoc_l, AssocR_Coproduct; apply case_inr; typeclasses eauto.
Qed.

Lemma swap_inl
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
      {CaseInl_C : CaseInl C bif}:
  forall (a b : obj), @inl_ _ _ _ _ a b >>> swap ⩯ inr_.
Proof.
  intros; unfold swap, Swap_Coproduct; apply case_inl; typeclasses eauto. 
Qed.

Lemma swap_inr
      {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
      {CaseInr_C : CaseInr C bif}:
  forall (a b : obj), @inr_ _ _ _ _ a b >>> swap ⩯ inl_.
Proof.
  intros; unfold swap, Swap_Coproduct; apply case_inr; typeclasses eauto. 
Qed.

Lemma swap_case
      {obj : Type} {C : obj -> obj -> Type}
      {Eq2_C : Eq2 C} {Eq2_Eq: forall a b : obj, @Equivalence (C a b) eq2}
      {Id_C : Id_ C} {Cat_C : Cat C}
      {Proper_cat : forall a b c, @Proper (C a b -> C b c -> C a c) (eq2 ==> eq2 ==> eq2) cat}
      {Category_C : Category C}
      {bif : obj -> obj -> obj}
      {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
      {Coproduct_C : Coproduct C bif}
      {CaseInr_C : CaseInr C bif}
      {Proper_case_ : forall a b c, @Proper (C a c -> C b c -> C _ c) (eq2 ==> eq2 ==> eq2) case_}:
  forall (a b c: obj) (f: C a c) (g: C b c), swap >>> case_ f g ⩯ case_ g f.
Proof.
  intros; unfold swap, Swap_Coproduct.
  rewrite cat_case, inr_case, inl_case.
  reflexivity.
Qed.

Ltac inl_left := rewrite <- (cat_assoc _ inl_).
Ltac inl_right := rewrite (cat_assoc _ inl_).
Ltac inr_left := rewrite <- (cat_assoc _ inr_).
Ltac inr_right := rewrite  (cat_assoc _ inr_).

Ltac run_in :=
  repeat (
      rewrite cat_id_l
    + rewrite <- (cat_assoc inl_ assoc_l), assoc_l_inl
    + rewrite <- (cat_assoc inl_ assoc_r), assoc_r_inl
    + rewrite <- (cat_assoc inr_ assoc_r), assoc_r_inr
    + rewrite <- (cat_assoc inr_ assoc_l), assoc_l_inr
    + rewrite <- (cat_assoc inl_ (bimap _ _)), bimap_inl
    + rewrite <- (cat_assoc inr_ (bimap _ _)), bimap_inr
    + rewrite <- (cat_assoc inl_ (case_ _ _)), case_inl
    + rewrite <- (cat_assoc inr_ (case_ _ _)), case_inr
    + rewrite <- (cat_assoc inl_ swap), swap_inl
    + rewrite <- (cat_assoc inr_ swap), swap_inr
    + rewrite <- (cat_assoc swap (case_ _ _)), swap_case
    + rewrite ?assoc_l_inl, ?assoc_l_inr, ?assoc_r_inl, ?assoc_r_inr,
      ?bimap_inl, ?bimap_inr, ?case_inl, ?case_inr
    ).

Context {E : Type -> Type}.

Local Lemma aux_app_asm_correct1 I J A C :
    (assoc_r >>>
     bimap (id_ I) (assoc_l >>> bimap swap (id_ C) >>> assoc_r) >>>
     assoc_l : sktree E ((I + J) + (A + C)) _)
  ⩯ bimap swap (id_ (A + C)) >>>
    (assoc_r >>>
    (bimap (id_ J) assoc_l >>>
    (assoc_l >>> (bimap swap (id_ C) >>> assoc_r)))).
Proof.
  rewrite cat_assoc.
  apply coprod_split.
  - run_in. symmetry. rewrite cat_assoc. run_in.
    (* TODO: [rewrite cat_assoc] seems to loop on one side, hence [symmetry]...
       this is what prevents us from just adding [rewrite !cat_assoc] to
       [run_in] *)
    apply coprod_split.
    + run_in. repeat (rewrite cat_assoc; run_in).
      reflexivity.
    + run_in. repeat (rewrite cat_assoc; run_in).
      reflexivity.
  - run_in. rewrite cat_assoc. symmetry.
    repeat (rewrite cat_assoc; run_in).
    apply coprod_split.
    + run_in. repeat (rewrite cat_assoc; run_in).
      reflexivity.
    + run_in. repeat (rewrite cat_assoc; run_in).
      reflexivity.
Qed.

Local Lemma aux_app_asm_correct2 I J B D :
    (assoc_r >>>
     bimap (id_ I) (assoc_l >>> bimap swap (id_ D) >>> assoc_r) >>>
     assoc_l : sktree E _ ((I + J) + (B + D)))
  ⩯ assoc_l >>>
    (bimap swap (id_ D) >>>
    (assoc_r >>>
    (bimap (id_ J) assoc_r >>>
    (assoc_l >>> bimap swap (id_ (B + D)))))).
Proof.
  simpl.
  rewrite cat_assoc.
  apply (coprod_split _ _).
  - run_in.
    symmetry. rewrite cat_assoc.
    run_in.
    rewrite cat_assoc.
    run_in.
    apply (coprod_split _ _).
    + repeat (rewrite cat_assoc; run_in).
      reflexivity.
    + repeat (rewrite cat_assoc; run_in).
      reflexivity.
  - run_in.
    rewrite cat_assoc. run_in.
    rewrite !cat_assoc; run_in.
    apply (coprod_split _ _).
    + run_in. repeat (rewrite !cat_assoc; run_in).
      reflexivity.
    + run_in. repeat (rewrite !cat_assoc; run_in).
      reflexivity.
Qed.

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
  rewrite loop_natural_left.  (* a loop append to diagrams can swallow them... *)
  rewrite loop_natural_right. (* ... from either side. *)
  rewrite loop_vanishing_2.   (* Finally, two nested loop can be combined. *)

  (* Remain now to relate the bodies of the loops on each side. *)
  (* First by some more equational reasoning. *)

  rewrite <- (loop_dinatural' swap swap) by apply swap_involutive.
  subst lhs.
  apply Proper_loop.
  rewrite !cat_assoc.
  repeat rewrite <- (cat_assoc _ _ (bimap (denote_b _) (denote_b _) >>> _)).
  cbn. rewrite relabel_bks_correct, app_bks_correct.
  rewrite cat_assoc.

  rewrite <- aux_app_asm_correct1, <- aux_app_asm_correct2.

  rewrite <- !compose_lift_sktree.
  rewrite <- !bimap_id_slift.
  rewrite <- !compose_lift_sktree.
  rewrite <- !bimap_slift_id.
  rewrite <- !assoc_r_sktree, <- !assoc_l_sktree, !sym_sktree_unfold.
  reflexivity.
Qed.

End Correctness.
