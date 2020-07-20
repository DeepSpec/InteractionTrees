(** Proofs that the Kleisli category of a monad is in fact a category. *)

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.Monad
     Basics.CategoryFunctor
     Basics.CategoryKleisli
     Basics.Function.

Import CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.


Section BasicFacts.

  Context {m : Type -> Type}.
  Context {Eq1 : Eq1 m}.
  Context {Mm : Monad m}.
  Context {Eq1P : @Eq1Equivalence m _ Eq1}.
  Context {ML : @MonadLawsE m Eq1 Mm}.
  
  Instance Proper_Kleisli_apply {a b} :
    Proper (eq2 ==> eq ==> eq1) (@Kleisli_apply m a b).
  Proof.
    cbv; intros; subst; auto.
  Qed.

  Lemma fold_Kleisli {a b} (f : Kleisli m a b) (x : a) : f x = Kleisli_apply f x.
  Proof. reflexivity. Qed.
  
  Global Instance Equivalence_Kleisli_eq2 {a b} : @Equivalence (Kleisli m a b) eq2.
  Proof.
    split; repeat intro.
    - reflexivity.
    - symmetry; auto.
    - etransitivity; eauto.
  Qed.

  Global Instance Functor_pure
    : Functor Fun (Kleisli m) (fun x => x) (@pure m _).
  Proof.
    constructor; intros.
    - reflexivity.
    - intros ?. unfold pure, cat, Cat_Kleisli. rewrite bind_ret_l.
      reflexivity.
    - intros ? ? ? ?. unfold pure. rewrite H. reflexivity.
  Qed.

(* This is subsumed by [category_proper_cat] and the [Category]
   instance for Kleisli.
   Adding this as an instance (i.e., marking this as [Global]) would confuse
   typeclass search, as it would often be picked for categories whose arrow
   types are definitionally equal to some [Kleisli m a b]
   (e.g., [sub (Kleisli m) f]), which puts the rest of the search in the wrong
   category.
 *)
Instance Proper_cat_Kleisli {a b c}
  : @Proper (Kleisli m a b -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) cat.
Proof.
  repeat intro.
  unfold cat, Cat_Kleisli.
  apply Proper_bind; auto.
Qed.

Local Opaque bind ret eq1.

Lemma pure_assoc_l {a b c : Type}
  : assoc_l (C := Kleisli m) (bif := sum)
  ⩯ pure (m := m) (a := a + (b + c))%type assoc_l.
Proof.
  cbv; intros x; destruct x as [ | []]; try setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma pure_assoc_r {a b c : Type} :
  (@assoc_r _ (Kleisli m) sum _ _ _ _) ⩯ (@pure m _ ((a + b) + c)%type _ assoc_r).
Proof.
  cbv; intros x; destruct x as [[] | ]; try setoid_rewrite bind_ret_l; reflexivity.
Qed.

Global Instance CatAssoc_Kleisli : CatAssoc (Kleisli m).
Proof.
  red. intros a b c d f g h. 
  unfold cat, Cat_Kleisli.
  cbv. intros x.
  setoid_rewrite bind_bind.
  reflexivity.
Qed.

(** *** [id_ktree] respect identity laws *)
Global Instance CatIdL_Kleisli : CatIdL (Kleisli m).
Proof.
  intros A B f a; unfold cat, Cat_Kleisli, id_, Id_Kleisli, pure.
  rewrite bind_ret_l. reflexivity.
Qed.

Global Instance CatIdR_Kleisli : CatIdR (Kleisli m).
Proof.
  intros A B f a; unfold cat, Cat_Kleisli, id_, Id_Kleisli, pure.
  rewrite bind_ret_r.
  reflexivity.
Qed.

Global Instance Category_Kleisli : Category (Kleisli m).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance InitialObject_Kleisli : InitialObject (Kleisli m) void.
Proof. intros A f []. Qed.



Global Instance Proper_case_Kleisli {a b c}
  : @Proper (Kleisli m a c -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro; destruct (_ : _ + _); cbn; auto.
Qed.

(** *** [pure] is well-behaved *)

(* SAZ: not sure about the naming conventions here. *)

Global Instance Proper_pure {A B} :
  Proper (eq2 ==> eq2) (@pure _ _ A B).
Proof.
  repeat intro.
  unfold pure.
  erewrite (H a); reflexivity.
Qed.

Lemma pure_id {A: Type}: (id_ A ⩯ @pure _ _ A A (id_ A))%cat.
Proof.
  reflexivity.
Qed.

Fact compose_pure {A B C} (ab : A -> B) (bc : B -> C) :
  (pure ab >>> pure bc ⩯ pure (ab >>> bc))%cat.
Proof.
  intros a.
  unfold pure, cat, Cat_Kleisli.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Fact compose_pure_l {A B C D} (f: A -> B) (g: B -> C) (k: Kleisli m C D) :
  (pure f >>> (pure g >>> k) ⩯ pure (g ∘ f) >>> k)%cat.
Proof.
  rewrite <- cat_assoc.
  rewrite compose_pure.
  reflexivity.
Qed.

Fact compose_pure_r {A B C D} (f: B -> C) (g: C -> D) (k: Kleisli m A B) :
  ((k >>> pure f) >>> pure g ⩯ k >>> pure (g ∘ f))%cat.
Proof.
  rewrite cat_assoc.
  rewrite compose_pure.
  reflexivity.
Qed.

Fact pure_cat {A B C}: forall (f:A -> B) (bc: Kleisli m B C),
    pure f >>> bc ⩯ fun a => bc (f a).
Proof.
  intros; intro a.
  unfold pure, pure, cat, Cat_Kleisli.
  rewrite bind_ret_l. reflexivity.
Qed.


Fact cat_pure {A B C}: forall (ab: Kleisli m A B) (g:B -> C),
    (ab >>> pure g)
  ⩯ (map g ab).
Proof.
  reflexivity.
Qed.

Lemma pure_swap {A B}:
  @pure _ _ (A+B) _ swap ⩯ swap.
Proof.
  intros []; reflexivity.
Qed.

Lemma pure_inl {A B}
  : pure (b := A + B) inl_ ⩯ inl_.
Proof. reflexivity. Qed.

Lemma pure_inr {A B}
  : pure (b := A + B) inr_ ⩯ inr_.
Proof. reflexivity. Qed.

Lemma case_pure {A B C} (ac : A -> C) (bc : B -> C) :
    case_ (pure ac) (pure bc)
  ⩯ pure (@case_ _ Fun _ _ _ _ _ ac bc).
Proof.
  intros []; reflexivity.
Qed.

(** *** [Unitors] lemmas *)

(* This is probably generalizable into [Basics.Category]. *)

Lemma unit_l_pure (A : Type) :
  unit_l ⩯ @pure _ _ (void + A) A unit_l.
Proof.
  intros [[]|]. reflexivity.
Qed.

Lemma unit_l'_pure (A : Type) :
  unit_l' ⩯ @pure _ _ A (void + A) unit_l'.
Proof.
  reflexivity.
Qed.

Lemma unit_r_pure (A : Type) :
  unit_r ⩯ @pure _ _ (A + void) A unit_r.
Proof.
  intros [|[]]. reflexivity.
Qed.

Lemma unit_r'_pure (A : Type) :
  unit_r' ⩯ @pure _ _ A (A + void) unit_r'.
Proof.
  reflexivity.
Qed.

(* SAZ: was named "case_l_ktree" *)
Lemma case_l {A B: Type} (ab: Kleisli m A (void + B)) :
  ab >>> unit_l ⩯ map unit_l ab.
Proof.
  rewrite unit_l_pure.
  reflexivity.
Qed.

(* SAZ: was named "case_l'_ktree" *)
Lemma case_l' {A B: Type} (f: Kleisli m (void + A) (void + B)) :
  unit_l' >>> f ⩯ fun a => f (inr a).
Proof.
  rewrite unit_l'_pure.
  intro. unfold cat, Cat_Kleisli, pure.
  rewrite bind_ret_l; reflexivity.
Qed.


Lemma case_r {A B: Type} (ab: Kleisli m A (B + void)) :
  ab >>> unit_r ⩯ map unit_r ab.
Proof.
  rewrite unit_r_pure.
  reflexivity.
Qed.

Lemma case_r' {A B: Type} (f: Kleisli m (A + void) (B + void)) :
  unit_r' >>> f ⩯ fun a => f (inl a).
Proof.
  rewrite unit_r'_pure.
  intro. unfold cat, Cat_Kleisli, pure.
  rewrite bind_ret_l; reflexivity.
Qed.


Fact bimap_id_pure {A B C} (f : B -> C) :
  bimap (id_ A) (pure f) ⩯ pure (bimap (id_ A) f).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l. rewrite <- !case_pure. rewrite <- !compose_pure. rewrite <- pure_id.
  rewrite !cat_id_l. 
  reflexivity.
Qed.

Fact bimap_pure_id {A B C} (f : A -> B) :
  bimap (pure f) (id_ C) ⩯ pure (bimap f id).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l, <- case_pure, <- compose_pure.
  reflexivity.
Qed.

Global Instance Coproduct_Kleisli : Coproduct (Kleisli m) sum.
Proof.
  constructor.
  - intros a b c f g.
    unfold inl_, Inl_Kleisli.
    rewrite pure_cat.
    reflexivity.
  - intros a b c f g.
    unfold inr_, Inr_Kleisli.
    rewrite pure_cat.
    reflexivity.
  - intros a b c f g fg Hf Hg [x | y].
    + unfold inl_, Inl_Kleisli in Hf.
      rewrite pure_cat in Hf.
      specialize (Hf x). simpl in Hf. rewrite Hf. reflexivity.
    + unfold inr_, Inr_Kleisli in Hg.
      rewrite pure_cat in Hg.
      specialize (Hg y). simpl in Hg. rewrite Hg. reflexivity.
  - typeclasses eauto.
Qed.

Global Instance bimap_id_kleisli : BimapId (Kleisli m) sum.
Proof.
  unfold BimapId, bimap, Bimap_Coproduct.
  intros.
  rewrite! cat_id_l.
  unfold inl_, inr_, Inl_Kleisli, Inr_Kleisli.
  rewrite case_pure.
  unfold pure, id_, case_, Case_Kleisli, case_sum, Id_Kleisli, pure.
  red. intro. destruct a0; reflexivity.
Qed.  

  Lemma map_inl_case_kleisli:
    forall (a1 b1 b2 c1 c2 : Type) (f1 : Kleisli m a1 b1) (g1 : Kleisli m b1 c1) (g2 : Kleisli m b2 c2),
      map inl f1 >>> case_ (map inl g1) (map inr g2) ⩯ map inl (f1 >>> g1).
  Proof.
    intros a1 b1 b2 c1 c2 f1 g1 g2.
    unfold cat, Cat_Kleisli, case_, Case_Kleisli, case_sum.
    unfold map. unfold cat, Cat_Kleisli.
    setoid_rewrite bind_bind.
    unfold pure. setoid_rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma map_inr_case_kleisli:
    forall (a2 b1 b2 c1 c2 : Type) (f2 : Kleisli m a2 b2) (g1 : Kleisli m b1 c1) (g2 : Kleisli m b2 c2),
      map inr f2 >>> case_ (map inl g1) (map inr g2) ⩯ map inr (f2 >>> g2).
  Proof.
    intros a2 b1 b2 c1 c2 f2 g1 g2.
    unfold cat, Cat_Kleisli, case_, Case_Kleisli, case_sum.
    unfold map. unfold cat, Cat_Kleisli.
    setoid_rewrite bind_bind.
    unfold pure. setoid_rewrite bind_ret_l. reflexivity.
  Qed.


Global Instance bimap_cat_kleisli : BimapCat (Kleisli m) sum.
Proof.
  unfold BimapCat, bimap, Bimap_Coproduct.
  intros.
  unfold inl_, inr_, Inl_Kleisli, Inr_Kleisli.
  rewrite! cat_pure. rewrite! cat_case.
  rewrite map_inl_case_kleisli.
  rewrite map_inr_case_kleisli.
  reflexivity.
Qed.

Global Instance proper_bimap_kleisli : forall a b c d,
    @Proper (Kleisli m a c -> Kleisli m b d -> Kleisli m _ _) (eq2 ==> eq2 ==> eq2) bimap.
Proof.
  intros.
  repeat intro.
  unfold bimap, Bimap_Coproduct.
  unfold case_, Case_Kleisli, case_sum.
  destruct a0.
  - unfold cat, Cat_Kleisli, inl_. rewrite H. reflexivity.
  - unfold cat, Cat_Kleisli, inl_. rewrite H0. reflexivity.
Qed.

Global Instance Bifunctor_Kleisli : Bifunctor (Kleisli m) sum.
constructor; typeclasses eauto.
Qed.

End BasicFacts.

Notation Proper_iter m a b :=
  (@Proper (Kleisli m a (sum a b)%type -> (Kleisli m a b))
           (pointwise_relation _ eq1 ==> pointwise_relation _ eq1)
           iter).
