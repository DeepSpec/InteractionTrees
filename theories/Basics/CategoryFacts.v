(** * General facts about categories *)

(* begin hide *)
From Coq Require Import
     Setoid Morphisms.

From ITree.Basics Require Import
     CategoryOps CategoryTheory.

Import Carrier.
Import CatNotations.
Local Open Scope cat.
(* end hide *)

Create HintDb cat.

(* Unfold constructions derived from Coproduct. *)
Ltac unfold_coproduct :=
  unfold
    bimap, Bimap_Coproduct,
    assoc_r, AssocR_Coproduct,
    assoc_l, AssocL_Coproduct,
    unit_l, UnitL_Coproduct,
    unit_l', UnitL'_Coproduct,
    unit_r, UnitR_Coproduct,
    unit_r', UnitR'_Coproduct,
    swap, Swap_Coproduct.

(* Simplify expressions involving coproducts. *)
Ltac cat_auto_simpl :=
  match goal with
  | [ |- eq2 ?lhs ?rhs ] =>
    repeat (rewrite cat_id_l || rewrite cat_id_r
     || rewrite case_inl || rewrite <- (cat_assoc inl_ (case_ _ _)), case_inl
     || rewrite case_inr || rewrite <- (cat_assoc inr_ (case_ _ _)), case_inr
     || rewrite !cat_assoc);
    reflexivity || eauto with cat
  end.

(** ** Isomorphisms *)

Section IsoFacts.

Context {obj : Type} {C : Hom obj}.
Context {Eq2C : Eq2 C} {IdC : Id_ C} {CatC : Cat C}.

Context {CatIdL_C : CatIdL C}.

(** [id_] is an isomorphism. *)
Global Instance SemiIso_Id {a} : SemiIso C (id_ a) (id_ a).
Proof. apply cat_id_l. Qed.

Context {Equivalence_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Section IsoCat.

Context {CatAssoc_C : CatAssoc C}.
Context {Proper_Cat_C : forall a b c,
            @Proper (C a b -> C b c -> _) (eq2 ==> eq2 ==> eq2) cat}.

(** Isomorphisms are closed under [cat]. *)
Global Instance SemiIso_Cat {a b c}
       (f : C a b) {f' : C b a} {SemiIso_f : SemiIso C f f'}
       (g : C b c) {g' : C c b} {SemiIso_g : SemiIso C g g'}
  : SemiIso C (f >>> g) (g' >>> f').
Proof.
  red.
  rewrite cat_assoc, <- (cat_assoc g), (semi_iso g _), cat_id_l, (semi_iso f _).
  reflexivity.
Qed.

End IsoCat.

Section IsoBimap.

Context {bif : binop obj}.
Context {Bimap_bif : Bimap C bif}.
Context {BimapId_bif : BimapId C bif}.
Context {BimapCat_bif : BimapCat C bif}.
Context {Proper_Bimap_bif : forall a b c d,
            @Proper (C a b -> C c d -> _) (eq2 ==> eq2 ==> eq2) bimap}.

(** Isomorphisms are closed under [bimap]. *)
Global Instance SemiIso_Bimap {a b c d} (f : C a b) (g : C c d)
         {f' : C b a} {SemiIso_f : SemiIso C f f'}
         {g' : C d c} {SemiIso_g : SemiIso C g g'} :
  SemiIso C (bimap f g) (bimap f' g').
Proof.
  red.
  rewrite bimap_cat, (semi_iso f _), (semi_iso g _), bimap_id.
  reflexivity.
Qed.

End IsoBimap.

End IsoFacts.

(** ** Categories *)

Section CategoryFacts.

Context {obj : Type} {C : Hom obj}.

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.

Context {i : obj}.
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

(** The initial morphism is unique. *)
Lemma initial_unique :
  forall a (f g : C i a), f ⩯ g.
Proof.
  intros.
  rewrite (initial_object f), (initial_object g).
  reflexivity.
Qed.

End CategoryFacts.

Global Hint Resolve initial_unique : cat.

(** ** Bifunctors *)

Section BifunctorFacts.

Context {obj : Type} {C : Hom obj}.

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.

Context {Category_C : Category C}.

Context {bif : binop obj}.
Context {Bimap_bif : Bimap C bif}
        {Bifunctor_bif : Bifunctor C bif}.

Lemma bimap_slide {a b c d} (ac: C a c) (bd: C b d) :
  bimap ac bd ⩯ bimap ac (id_ _) >>> bimap (id_ _) bd.
Proof.
  rewrite bimap_cat, cat_id_l, cat_id_r.
  reflexivity.
Qed.

Lemma bimap_slide' {a b c d} (ac: C a c) (bd: C b d) :
  bimap ac bd ⩯ bimap (id_ _) bd >>> bimap ac (id_ _).
Proof.
  rewrite bimap_cat, cat_id_l, cat_id_r.
  reflexivity.
Qed.

End BifunctorFacts.

(** ** Coproducts *)

Section CoproductFacts.

Context {obj : Type} {C : Hom obj}.

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.

Context {Category_C : Category C}.

Context {bif : binop obj}.
Context {Case_C : Case C bif}
        {Inl_C : Inl C bif}
        {Inr_C : Inr C bif}.
Context {Coproduct_C : Coproduct C bif}.

Lemma case_inl' {a b c d} (ac : C a c) (bc : C b c) (cd : C c d)
  : inl_ >>> (case_ ac bc >>> cd) ⩯ ac >>> cd.
Proof.
  rewrite <- cat_assoc, case_inl; reflexivity.
Qed.

Lemma case_inr' {a b c d} (ac : C a c) (bc : C b c) (cd : C c d)
  : inr_ >>> (case_ ac bc >>> cd) ⩯ bc >>> cd.
Proof.
  rewrite <- cat_assoc, case_inr; reflexivity.
Qed.

(** Commute [cat] and [case_]. *)
Lemma cat_case
      {a b c d} (ac : C a c) (bc : C b c) (cd : C c d)
  : case_ ac bc >>> cd ⩯ case_ (ac >>> cd) (bc >>> cd).
Proof.
  apply case_universal; rewrite <- cat_assoc.
  - rewrite case_inl; reflexivity.
  - rewrite case_inr; reflexivity.
Qed.

(** Case analysis with projections is the identity. *)
Corollary case_eta {a b} : id_ (bif a b) ⩯ case_ inl_ inr_.
Proof.
  apply case_universal; rewrite cat_id_r; reflexivity.
Qed.

Lemma case_eta' {a b c} (f : C (bif a b) c) :
  f ⩯ case_ (inl_ >>> f) (inr_ >>> f).
Proof.
  eapply case_universal; reflexivity.
Qed.

(** We can prove the equivalence of morphisms on coproducts
    by case analysis. *)
Lemma coprod_split {a b c} (f g : C (bif a b) c) :
  (inl_ >>> f ⩯ inl_ >>> g) ->
  (inr_ >>> f ⩯ inr_ >>> g) ->
  f ⩯ g.
Proof.
  intros. rewrite (case_eta' g).
  apply case_universal; assumption.
Qed.

Ltac cat_auto :=
  unfold_coproduct;
  repeat progress (reflexivity || (try cat_auto_simpl); try apply coprod_split).

Ltac cat_auto' :=
  repeat intro;
  repeat match goal with
         | [ |- eq2 _ _ ] => fail 1
         | _ => red
         end;
  cat_auto.

Lemma swap_case (a b c: obj) (f: C a c) (g: C b c)
  : swap >>> case_ f g ⩯ case_ g f.
Proof.
  intros; unfold swap, Swap_Coproduct.
  rewrite cat_case, inr_case, inl_case.
  reflexivity.
Qed.

Lemma inr_swap {a b} : inr_ >>> swap_ a b ⩯ inl_.
Proof. apply case_inr. Qed.

Lemma inl_swap {a b} : inl_ >>> swap_ a b ⩯ inr_.
Proof. apply case_inl. Qed.

Lemma bimap_case_unfold {a b c d} (f : C a b) (g : C c d)
  : bimap f g ⩯ case_ (f >>> inl_) (g >>> inr_).
Proof. reflexivity. Qed.

Lemma inr_bimap {a b c d} (f : C a b) (g : C c d)
  : inr_ >>> bimap f g ⩯ g >>> inr_.
Proof. apply case_inr. Qed.

Lemma inl_bimap {a b c d} (f : C a b) (g : C c d)
  : inl_ >>> bimap f g ⩯ f >>> inl_.
Proof. apply case_inl. Qed.

Lemma bimap_case {a a' b b' c}
      (fa : C a a') (fb : C b b') (ga : C a' c) (gb : C b' c)
  : bimap fa fb >>> case_ ga gb ⩯ case_ (fa >>> ga) (fb >>> gb).
Proof. cat_auto'. Qed.

Lemma inl_assoc_r {a b c}
  : inl_ >>> assoc_r_ a b c ⩯ bimap (id_ a) inl_.
Proof. cat_auto'. Qed.

Lemma inl_assoc_l {a b c}
  : inl_ >>> assoc_l_ a b c ⩯ inl_ >>> inl_.
Proof. cat_auto'. Qed.

Lemma inr_assoc_l {a b c}
  : inr_ >>> assoc_l_ a b c ⩯ bimap inr_ (id_ c).
Proof. cat_auto'. Qed.

Lemma inr_assoc_r {a b c}
  : inr_ >>> assoc_r_ a b c ⩯ inr_ >>> inr_.
Proof. cat_auto'. Qed.

(** The coproduct is a bifunctor. *)

Global Instance Proper_Bimap_Coproduct {a b c d}:
  @Proper (C a b -> C c d -> _)
          (eq2 ==> eq2 ==> eq2) bimap.
Proof.
  intros ac ac' eqac bd bd' eqbd.
  unfold bimap, Bimap_Coproduct.
  rewrite eqac, eqbd; reflexivity.
Qed.

Global Instance BimapId_Coproduct : BimapId C bif.
Proof.
  intros A B.
  symmetry. unfold bimap, Bimap_Coproduct.
  rewrite 2 cat_id_l.
  apply case_eta.
Qed.

Global Instance BimapCat_Coproduct : BimapCat C bif.
Proof. cat_auto'. Qed.

Global Instance Bifunctor_Coproduct : Bifunctor C bif.
Proof.
  constructor; typeclasses eauto.
Qed.

(** The coproduct is commutative *)

Global Instance SwapInvolutive_Coproduct {a b : obj}
  : SemiIso C (swap_ a b) swap.
Proof. cat_auto'. Qed.

(** The coproduct is associative *)

Global Instance AssocRMono_Coproduct {a b c : obj}
  : SemiIso C (assoc_r_ a b c) assoc_l.
Proof. cat_auto'. Qed.

Global Instance AssocLMono_Coproduct {a b c : obj}
  : SemiIso C (assoc_l_ a b c) assoc_r.
Proof. cat_auto'. Qed.

Context (i : obj).
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

(** The coproduct has units. *)

Global Instance UnitLMono_Coproduct {a : obj}
  : SemiIso C (unit_l_ i a) unit_l'.
Proof. cat_auto'. Qed.

(* TODO: derive this by symmetry *)
Global Instance UnitRMono_Coproduct {a : obj}
  : SemiIso C (unit_r_ i a) unit_r'.
Proof. cat_auto'. Qed.

Global Instance UnitLEpi_Coproduct {a : obj}
  : SemiIso C (unit_l'_ i a) unit_l.
Proof. cat_auto'. Qed.

Global Instance UnitREpi_Coproduct {a : obj}
  : SemiIso C (unit_r'_ i a) unit_r.
Proof. cat_auto'. Qed.

Lemma inr_unit_l {a} : inr_ >>> unit_l ⩯ id_ a.
Proof. apply (semi_iso _ _). Qed.

Lemma inl_unit_r {a} : inl_ >>> unit_r ⩯ id_ a.
Proof. apply (semi_iso _ _). Qed.

Global Instance UnitLNatural_Coproduct : UnitLNatural C bif i.
Proof. cat_auto'. Qed.

Global Instance UnitL'Natural_Coproduct : UnitL'Natural C bif i.
Proof. cat_auto'. Qed.

(** The coproduct satisfies the monoidal coherence laws. *)

Global Instance AssocRUnit_Coproduct : AssocRUnit C bif i.
Proof. cat_auto'. Qed.

Global Instance AssocRAssocR_Coproduct : AssocRAssocR C bif.
Proof. cat_auto'. Qed.

Global Instance Monoidal_Coproduct : Monoidal C bif i.
Proof.
  constructor; idtac + constructor; typeclasses eauto.
Qed.

Global Instance AssocLAssocL_Coproduct : AssocLAssocL C bif.
Proof. cat_auto'. Qed.

(** The coproduct satisfies the symmetric monoidal laws. *)

Global Instance SwapUnitL_Coproduct : SwapUnitL C bif i.
Proof. cat_auto'. Qed.

Global Instance SwapAssocR_Coproduct : SwapAssocR C bif.
Proof. cat_auto'. Qed.

Global Instance SwapAssocL_Coproduct : SwapAssocL C bif.
Proof. cat_auto'. Qed.

Global Instance SymMonoidal_Coproduct : SymMonoidal C bif i.
Proof.
  constructor; typeclasses eauto.
Qed.

Lemma swap_bimap {a b c d} (ab : C a b) (cd : C c d) :
  bimap ab cd ⩯ (swap >>> bimap cd ab >>> swap).
Proof. cat_auto'. Qed.

(* Naturality of swap *)
Lemma swap_bimap' {a b c d} (ab : C a b) (cd : C c d) :
  swap >>> bimap ab cd ⩯ bimap cd ab >>> swap.
Proof. cat_auto'. Qed.

End CoproductFacts.

Ltac cat_auto_step :=
  repeat (apply category_proper_cat; [ reflexivity | ]);
  try apply iterative_proper_iter.

Ltac cat_auto :=
  unfold_coproduct;
  repeat progress (reflexivity || cat_auto_simpl; try apply coprod_split).

(** Iterative categories are traced. *)
Section TracedIterativeFacts.

Context {obj : Type} {C : Hom obj}.

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.
Context {Category_C : Category C}.

Context {bif : binop obj}.
Context {Case_C : Case C bif}
        {Inl_C : Inl C bif}
        {Inr_C : Inr C bif}.
Context {Coproduct_C : Coproduct C bif}.

Context {Iter_bif : Iter C bif}.
Context {Iterative_C : Iterative C bif}.

Global Instance Proper_loop {a b c}
  : @Proper (C (bif c a) (bif c b) -> C a b) (eq2 ==> eq2) loop.
Proof.
  repeat intro.
  unfold loop.
  rewrite H.
  reflexivity.
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
Lemma loop_natural_left {a a' b c} (f : C (bif c a) (bif c b)) (g : C a' a)
  : g >>> loop f
  ⩯ loop (bimap (id_ _) g >>> f).
Proof.
  unfold loop.
  transitivity (inr_ >>> iter (bimap (id_ c) g >>> inl_
                                     >>> case_ (f >>> bimap inl_ (id_ b)) inr_)).
  - rewrite iter_dinatural.
    cat_auto. do 2 cat_auto_step. cat_auto.
  - cat_auto.
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
Lemma loop_natural_right {a b b' c} (f : C (bif c a) (bif c b)) (g : C b b')
  : loop f >>> g
  ⩯ loop (f >>> bimap (id_ _) g).
Proof.
  unfold loop.
  rewrite cat_assoc. cat_auto_step.
  rewrite iter_natural. cat_auto_step.
  rewrite !cat_assoc, !bimap_cat, !cat_id_l, !cat_id_r.
  reflexivity.
Qed.

Lemma loop_dinatural {a b c c'} (f : C (bif c a) (bif c' b)) (g : C c' c)
  : loop (f >>> bimap g (id_ _))
  ⩯ loop (bimap g (id_ _) >>> f).
Proof.
  unfold loop.
  transitivity (inr_ >>> iter (bimap g (id_ a) >>> inl_
                                     >>> case_ (f >>> bimap inl_ (id_ b)) inr_)).
  - rewrite iter_dinatural.
    cat_auto. do 2 cat_auto_step. cat_auto.
  - cat_auto.
Qed.

Context {i : obj}.
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

Lemma loop_vanishing_1 {a b} (f : C (bif i a) (bif i b))
  : loop f
  ⩯ unit_l' >>> f >>> unit_l.
Proof.
  unfold loop.
  rewrite iter_unfold. cat_auto. cat_auto_step. cat_auto.
Qed.

(* Vanishing. These two loops:

[[
    +----------+
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

Lemma loop_vanishing_2 {a b c d} (f : C (bif d (bif c a)) (bif d (bif c b)))
  : loop (loop f)
  ⩯ loop (assoc_r >>> f >>> assoc_l).
Proof.
  unfold loop.
  transitivity (inr_ >>> inr_ >>> iter (iter (
                 f >>> bimap inl_ (bimap (inl_ >>> inr_) (id_ _))
               ))).
  - transitivity (inr_ >>> iter (inr_ >>> inl_ >>> case_ (iter (
                   f >>> bimap inl_ (bimap inl_ (id_ _))
                 )) inr_)).
    + cat_auto. do 2 cat_auto_step. rewrite iter_natural.
      cat_auto_step. rewrite cat_assoc. cat_auto_step.
      cat_auto.
    + rewrite iter_dinatural.
      rewrite cat_assoc, case_inl.
      rewrite iter_natural.
      cat_auto. do 3 cat_auto_step.
      cat_auto.

  - rewrite iter_codiagonal.
    rewrite (cat_assoc _ (bimap _ _)), bimap_case, cat_id_r.
    transitivity (inr_ >>> iter (
                   (assoc_r >>> inl_) >>>
                   case_ (f >>> assoc_l >>> bimap inl_ (id_ _)) inr_)).
    + rewrite iter_dinatural.
      cat_auto. do 2 cat_auto_step. cat_auto.
    + cat_auto.
Qed.

Lemma loop_superposing {a b c d e}
      (ab : C (bif e a) (bif e b)) (cd : C c d) :
    bimap (loop ab) cd
  ⩯ loop (assoc_l >>> bimap ab cd >>> assoc_r).
Proof.
  unfold loop.
  cat_auto.
  - transitivity (
        inr_ >>> iter (
          (inl_ >>> assoc_r >>> inl_)
            >>> case_ (assoc_l >>> bimap ab cd >>> assoc_r >>> bimap inl_ (id_ _))
                      inr_)).

    + rewrite cat_assoc, iter_natural.
      do 2 (cat_auto_step; cat_auto).
    + rewrite iter_dinatural.
      do 3 (cat_auto; cat_auto_step).

  - rewrite iter_unfold. cat_auto.
Qed.

Lemma loop_yanking {a} : loop swap ⩯ id_ a.
Proof.
  unfold loop. rewrite 2 iter_unfold. cat_auto.
Qed.

Lemma loop_dinatural' {a b c d} (cd : C c d) (dc: C d c)
      (ab_: C (bif c a) (bif c b))
  : (cd >>> dc) ⩯ id_ _ ->
    loop (bimap dc (id_ _) >>> ab_ >>> bimap cd (id_ _))
  ⩯ loop ab_.
Proof.
  intros Hij. rewrite loop_dinatural.
  rewrite <- cat_assoc.
  rewrite bimap_cat.
  rewrite Hij.
  rewrite cat_id_l.
  rewrite bimap_id.
  rewrite cat_id_l.
  reflexivity.
Qed.

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
Theorem cat_from_loop {a b c} (ab : C a b) (bc : C b c)
  : loop (swap >>> bimap ab bc) ⩯ ab >>> bc.
Proof.
(*
      +-------------+
      |             |
      +---\/---ab---+
   -------/\---bc-------
 *)

  rewrite bimap_slide.
  rewrite <- cat_assoc.
(*
      +----------------+
      |                |
      +---\/---ab------+
   -------/\------bc-------
 *)

  rewrite <- loop_natural_right.
(*
      +-------------+
      |             |
      +---\/---ab---+
   -------/\------------bc----
 *)

  rewrite swap_bimap.
  rewrite <- !cat_assoc.
(*
      +-------------------+
      |                   |
      +---\/--\/------\/--+
   -------/\--/\--ab--/\----bc----
 *)

  rewrite swap_involutive, cat_id_l.
(*
      +-------------------+
      |                   |
      +---------------\/--+
   ---------------ab--/\----bc----
 *)

  rewrite <- loop_natural_left.
(*
           +------+
           |      |
           +--\/--+
   ----ab-----/\-----bc----
 *)

  rewrite loop_yanking.
  rewrite cat_id_r.
(*
   ----ab---bc----
 *)

  reflexivity.
Qed.


(** Utility: lemma to ease working forward in an equational proof.
      Make it more convenient to rewrite subterm only on one side of the equation.
 *)
Fact fwd_eqn {a b} (f g : C a b) :
  (forall h, h ⩯ f -> h ⩯ g) -> f ⩯ g.
Proof.
  intro H; apply H; reflexivity.
Qed.

(** Utility: lemmas to ease forward reasoning *)
Fact cat_eq2_l {a b c} (h : C a b) (f g : C b c) :
  f ⩯ g ->
  h >>> f ⩯ h >>> g.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Fact cat_eq2_r {a b c} (h : C b c) (f g : C a b) :
  f ⩯ g ->
  f >>> h ⩯ g >>> h.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Fact local_rewrite1 {a b c}:
  bimap (id_ a) (swap_ b c) >>> assoc_l >>> swap
        ⩯ assoc_l >>> bimap swap (id_ c) >>> assoc_r.
Proof.
  symmetry.
  apply fwd_eqn; intros h Eq.
  do 2 apply (cat_eq2_l (bimap (id_ _) swap)) in Eq.
  rewrite <- cat_assoc, bimap_cat, swap_involutive, cat_id_l,
  bimap_id, cat_id_l in Eq.
  rewrite <- (cat_assoc _ _ assoc_r), <- (cat_assoc _ assoc_l _)
    in Eq.
  rewrite <- swap_assoc_l in Eq.
  rewrite (cat_assoc _ _ assoc_r) in Eq.
  rewrite assoc_l_mono in Eq.
  rewrite cat_id_r in Eq.
  rewrite cat_assoc.
  assumption.
Qed.

Fact local_rewrite2 {a b c}:
  swap >>> assoc_r >>> bimap (id_ _) swap
       ⩯ assoc_l_ a b c >>> bimap swap (id_ _) >>> assoc_r.
Proof.
  symmetry.
  apply fwd_eqn; intros h Eq.
  do 2 apply (cat_eq2_r (bimap (id_ _) swap)) in Eq.
  rewrite cat_assoc, bimap_cat, swap_involutive, cat_id_l,
  bimap_id, cat_id_r in Eq.
  rewrite 2 (cat_assoc assoc_l) in Eq.
  rewrite <- swap_assoc_r in Eq.
  rewrite <- 2 (cat_assoc assoc_l) in Eq.
  rewrite assoc_l_mono, cat_id_l in Eq.
  assumption.
Qed.

Lemma loop_superposing_2 {a b c d e}
      (ab : C a b) (cd : C (bif e c) (bif e d))
  : bimap ab (loop cd)
  ⩯ loop (assoc_l >>> bimap swap (id_ _)
                       >>> assoc_r
                       >>> bimap ab cd
                       >>> assoc_l >>> bimap swap (id_ _) >>> assoc_r).
Proof.
  rewrite swap_bimap, loop_superposing.
  rewrite loop_natural_left, loop_natural_right.
  rewrite (swap_bimap cd ab).
  rewrite <- !cat_assoc.
  rewrite local_rewrite1.
  rewrite 2 cat_assoc.
  rewrite <- (cat_assoc swap assoc_r).
  rewrite local_rewrite2.
  rewrite <- !cat_assoc.
  reflexivity.
Qed.

End TracedIterativeFacts.
