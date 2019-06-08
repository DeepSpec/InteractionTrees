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
     Basics.CategoryKleisli
     Basics.Function.

Import CatNotations.
Open Scope cat_scope.
Open Scope kleisli_scope.

Section BasicFacts.

  Context {m : Type -> Type}.
  Context {EQM : EqM m}.
  Context `{Monad m}.
  Context `{@EqMEq m EQM}.

  Class MonadLaws :=
    {
      bind_ret :> forall a b (f : a -> m b) (x : a), bind (ret x) f ≈ f x
    ; ret_bind :> forall a (x : m a), bind x (fun y => ret y) ≈ x
    ; bind_bind :> forall a b c (x : m a) (f : a -> m b) (g : b -> m c), bind (bind x f) g ≈ bind x (fun y => bind (f y) g)
    }.                                             

  Class MonadProperOps :=
    { 
      Proper_bind :> forall a b,
          (@Proper (m a%type -> (a -> m b) -> m b)
           (eqm ==> pointwise_relation _ eqm ==> eqm)
           bind)
    }.
      
  Context `{MonadLaws}.
  Context `{MonadProperOps}.

  
Global Instance Equivalence_Kleisli_eq2 {a b} : @Equivalence (Kleisli m a b) eq2.
Proof.
  split; repeat intro.
  - reflexivity.
  - symmetry; auto.
  - etransitivity; eauto.
Qed.


Global Instance Proper_cat_Kleisli {a b c}
  : @Proper (Kleisli m a b -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) cat.
Proof.
  repeat intro.
  unfold cat, Cat_Kleisli.
  apply Proper_bind; auto.
Qed.


Lemma assoc_l_kleisli {a b c : Type} :
  (@assoc_l _ (Kleisli m) sum _ _ _ _) ⩯ (@pure m _ (a + (b + c))%type _ assoc_l).
Proof.
  cbv; intros x; destruct x as [ | []]; try rewrite bind_ret; reflexivity.  
Qed.
      
Lemma assoc_r_ktree {a b c : Type} :
  (@assoc_r _ (Kleisli m) sum _ _ _ _) ⩯ (@pure m _ ((a + b) + c)%type _ assoc_r).
Proof.
  cbv; intros x; destruct x as [[] | ]; try rewrite bind_ret; reflexivity.  
Qed.

Global Instance CatAssoc_Kleisli : CatAssoc (Kleisli m).
Proof.
  red. intros a b c d f g h. 
  unfold cat, Cat_Kleisli.
  cbv. intros x.
  rewrite bind_bind.
  reflexivity.
Qed.

(** *** [id_ktree] respect identity laws *)
Global Instance CatIdL_Kleisli : CatIdL (Kleisli m).
Proof.
  intros A B f a; unfold cat, Cat_Kleisli, id_, Id_Kleisli, pure.
  rewrite bind_ret. reflexivity.
Qed.

Global Instance CatIdR_Kleisli : CatIdR (Kleisli m).
Proof.
  intros A B f a; unfold cat, Cat_Kleisli, id_, Id_Kleisli, pure.
  rewrite ret_bind.
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

Global Instance eq_pure {A B} :
  Proper (eq2 ==> eq2) (@pure _ _ A B).
Proof.
  repeat intro.
  unfold pure, Monad.ret.
  erewrite (H3 a); reflexivity.
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
  rewrite bind_ret.
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
  unfold pure, pure, Monad.ret, cat, Cat_Kleisli.
  rewrite bind_ret. reflexivity.
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


Fact case_pure {A B C} (ac : A -> C) (bc : B -> C) :
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
  rewrite bind_ret; reflexivity.
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
  rewrite bind_ret; reflexivity.
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
    unfold inl_, CoprodInl_Kleisli.
    rewrite pure_cat.
    reflexivity.
  - intros a b c f g.
    unfold inr_, CoprodInr_Kleisli.
    rewrite pure_cat.
    reflexivity.
  - intros a b c f g fg Hf Hg [x | y].
    + unfold inl_, CoprodInl_Kleisli in Hf.
      rewrite pure_cat in Hf.
      specialize (Hf x). simpl in Hf. rewrite Hf. reflexivity.
    + unfold inr_, CoprodInr_Kleisli in Hg.
      rewrite pure_cat in Hg.
      specialize (Hg y). simpl in Hg. rewrite Hg. reflexivity.
  - typeclasses eauto.
Qed.


End BasicFacts.



Notation Proper_aloop m a b :=
  (@Proper ((a -> m (sum a b)%type) -> (a -> m b%type))
           (pointwise_relation _ eqm ==> pointwise_relation _ eqm)
           bind).

Instance Proper_iter_Kleisli m `{EqM m} `{Monad m} `{ALoop m}
         {a b}
  : @Proper (Kleisli m a (a + b) -> Kleisli m a b)
            (eq2 ==> eq2) iter.
Proof.
Admitted.
