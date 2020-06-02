From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Basics.Typ_Class2
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
     Basics.Monad
     Basics.HeterogeneousRelations
.

Import CatNotations.
Open Scope cat_scope.


Definition PropM (X:typ) : typ := X ~~> prop_typ.

Definition ret_ (A:typ) (x:A) : PropM A := 
  fun (y:A) => equalE A x y.


Program Definition ret_PropM (A:typ) : A -=-> (PropM A) :=
  -=->! (ret_ A) _.
Next Obligation.
  unfold ret_.
  repeat red.
  intros; split; intros.
  - rewrite <- H. rewrite <- H0. assumption.
  - rewrite H. rewrite H0. assumption.
Qed.

Program Definition bind_ (A B : typ) (k : A -=-> PropM B) (ma : PropM A) :=
  (fun b:B =>
           exists (a:A), a ∈ A /\ ma a /\ (k a b)).

Program Definition bind_PropM (A B : typ) (k : A -=-> PropM B) : (PropM A) -=-> (PropM B) :=
  -=->! (bind_ A B k) _.
Next Obligation.
  unfold bind_.
  repeat red.
  intros.
  split; intros (a & IN & PA & KA).
  - exists a. split; auto. split.  rewrite <- H. apply PA. assumption. destruct k.
    cbn. cbn in KA. specialize (p _ _ IN). specialize (p _ _ H0). rewrite <- p. assumption.
  - exists a. split; auto. split.  rewrite H. apply PA. assumption. destruct k.
    cbn. cbn in KA. specialize (p _ _ IN). specialize (p _ _ H0). rewrite p. assumption.
Qed.
    
Instance MonadID : Monad typ_proper PropM.
split.
- exact ret_PropM.
- exact bind_PropM.
Defined.  

Definition eqmR_PropM {A B : typ} (R : relationH A B) (HP: Proper (equalE A ==> equalE B ==> iff) R) :
  relationH (PropM A) (PropM B) := 
  fun PA PB => forall (x:A) (y:B), R x y -> (PA x) <-> (PB y).

Program Instance EqmR_PropM : EqmR PropM :=
  {
  eqmR := @eqmR_PropM;
  }.

