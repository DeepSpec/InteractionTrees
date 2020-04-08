(** * Monad laws and associated typeclasses *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function.
(* end hide *)

Set Primitive Projections.
Set Universe Polymorphism.

Set Implicit Arguments.
Set Strict Implicit.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Class EqM (m:Type -> Type) : Type :=
  eqm : forall a, m a -> m a -> Prop.

Class EqMProps (m:Type -> Type) `{Monad m} `{EqM m} :=
      eqm_equiv :> forall a, Equivalence (eqm a).
Arguments EqMProps m {_ _}.
Arguments eqm {m _ _}.
Infix "≈" := eqm (at level 70) : monad_scope.

Section monadic.

  Definition liftM@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U : Type@{d}} (f : T -> U) : m T -> m U :=
    fun x => bind x (fun x => ret (f x)).

  Definition liftM2@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U V : Type@{d}} (f : T -> U -> V) : m T -> m U -> m V :=
    Eval cbv beta iota zeta delta [ liftM ] in
      fun x y => bind x (fun x => liftM (f x) y).

  Definition liftM3@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U V W : Type@{d}} (f : T -> U -> V -> W) : m T -> m U -> m V -> m W :=
    Eval cbv beta iota zeta delta [ liftM2 ] in
      fun x y z => bind x (fun x => liftM2 (f x) y z).

  Definition apM@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {A B : Type@{d}} (fM:m (A -> B)) (aM:m A) : m B :=
    bind fM (fun f => liftM f aM).

  (* Left-to-right composition of Kleisli arrows. *)
  Definition mcompose@{c d}
             {m:Type@{d}->Type@{c}}
             {M: Monad m}
             {T U V:Type@{d}}
             (f: T -> m U) (g: U -> m V): (T -> m V) :=
    fun x => bind (f x) g.

End monadic.

Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 61, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 61, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 61, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

End MonadNotation.

Section MonadLaws.

  Context (m : Type -> Type).
  Context {EqM : @EqM m}.
  Context {Mm : Monad m}.
  Context {EqMP : @EqMProps m _ EqM}.

  Local Open Scope monad_scope.

  Class MonadLaws :=
    { bind_ret_l : forall a b (f : a -> m b) (x : a), bind (ret x) f ≈ f x
    ; bind_ret_r : forall a (x : m a), bind x (fun y => ret y) ≈ x
    ; bind_bind : forall a b c (x : m a) (f : a -> m b) (g : b -> m c), bind (bind x f) g ≈ bind x (fun y => bind (f y) g)
    ; Proper_bind :> forall {a b},
        (@Proper (m a%type -> (a -> m b) -> m b)
         (eqm ==> pointwise_relation _ eqm ==> eqm)
         bind)
    }.

End MonadLaws.

Arguments MonadLaws m {_ _}.
Arguments bind_ret_l {m _ _ _}.
Arguments bind_ret_r {m _ _ _}.
Arguments bind_bind {m _ _ _}.
Arguments Proper_bind {m _ _ _}.

(** ** Loop operator *)

(** [iter]: A primitive for general recursion.
    Iterate a function updating an accumulator [I], until it produces
    an output [R].
 *)
Polymorphic Class MonadIter (M : Type -> Type) : Type :=
  iter : forall {R I: Type}, (I -> M (I + R)%type) -> I -> M R.

(* Its laws are defined by its [Kleisli] category forming an [Iterative] category *)

Section MonadHomomorphism.

  Local Open Scope monad_scope.

  Variable M M': Type -> Type.
  Context {MM: Monad M}.
  Context {MM': Monad M'}.
  Context {IM: MonadIter M}.
  Context {IM': MonadIter M'}.
  Context {EqMM': @EqM M'}.
  Variable F: M ~> M'.

  Class MonadHom: Prop :=
    {
      resp_ret : forall A (a: A), F (ret a) ≈ ret a;
      resp_bind: forall A B (m: M A) (k: A -> M B),
          F (bind m k) ≈ bind (F m) (fun x => F (k x))
    }.

  Class IterHom: Prop :=
    {
      resp_iter: forall (I R: Type) (body: I -> M (I + R)%type) i,
        F (iter body i) ≈ iter (fun x => F (body x)) i
    }.

End MonadHomomorphism.

Section MonadTriggerable.

  Local Open Scope monad_scope.

  Variable M M': Type -> Type.
  Context {MM: Monad M}.
  Context {MM': Monad M'}.
  Context {EqMM': @EqM M'}.
  Context {IM: MonadIter M}.
  Context {IM': MonadIter M'}.

  (**
     Monads that allow for the embedding of an effect as a minimal
     monadic effectful computation are dubbed "Triggerable".
   *)

  Class Triggerable (E: Type -> Type) := trigger: E ~> M.

  (* The correctness of this operation, i.e. its minimality, is expressed
     with respect to a notion of interpretation of monads.
     A monad [M] is said to be "Interpretable" into a monad [M'] if there
     is a family of monad monomorphisms for each handler [h: E ~> M'].
   *)

  Class Interpretable :=
    interp: forall (E: Type -> Type) (h: E ~> M'), M ~> M'.

  Class InterpCorrect E {InterpMM': Interpretable} {TrigM: Triggerable E}: Prop :=
    {
      interp_monad_hom h :> MonadHom (interp E h);
      interp_iter_hom  h :> IterHom (interp E h);
      interp_trigger h T (e: E T): interp E h (trigger _ e) ≈ h _ e
    }.

End MonadTriggerable.

Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope monad_scope.

Ltac rw_pointed_l H :=
  match goal with
    |- ?f ?x ≈ _ =>
    let tmp := fresh "H" in
    assert (tmp: f ⩯ f) by reflexivity;
    setoid_rewrite H in tmp at 1;
    specialize (tmp x);
    setoid_rewrite <- tmp
  end.

Ltac rw_pointed_r H :=
  match goal with
    |- _ ≈ ?f ?x =>
    let tmp := fresh "H" in
    assert (tmp: f ⩯ f) by reflexivity;
    setoid_rewrite H in tmp at 1;
    specialize (tmp x);
    setoid_rewrite <- tmp
  end.

