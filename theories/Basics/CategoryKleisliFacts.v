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



Instance Proper_case_Kleisli {a b c}
  : @Proper (Kleisli m a c -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro; destruct (_ : _ + _); cbn; auto.
Qed.


(** *** [pure] is well-behaved *)

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

Fact pure_compose {A B C}: forall (f:A -> B) (bc: Kleisli m B C),
    pure f >>> bc ⩯ fun a => bc (f a).
Proof.
  intros; intro a.
  unfold pure, pure, Monad.ret, cat, Cat_Kleisli.
  rewrite bind_ret. reflexivity.
Qed.

(*
Fact compose_pure {A B C}: forall (ab: Kleisli m A B) (g:B -> C),
    (ab >>> pure g)
  ⩯ (fun a => ITree.map g (ab a)).
Proof.
  reflexivity.
Qed.
*)

Lemma sym_ktree_unfold {A B}:
  @pure _ _ (A+B) _ swap ⩯ swap.
Proof.
  intros []; reflexivity.
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
