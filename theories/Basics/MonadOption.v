(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Monad.

Import ITree.Basics.Basics.Monads.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.
(* end hide *)


Inductive option (A : Type) : Type :=
| None
| Some (x:A).

Arguments None {_}.
Arguments Some {_} _.

Definition eq_option {A:Type} (o1 o2 : option A) : Prop :=
  match o1, o2 with
  | None, None => True
  | None, Some _ => False
  | Some _, None  => False
  | Some x, Some y => x = y
  end.

Global Instance Eq1_option : Eq1 option := @eq_option.

Definition ret_option {A:Type} (x:A) : option A :=
  Some x.

Definition bind_option {A B:Type} (m : option A) (k : A -> option B) : option B :=
  match m with
  | None => None
  | Some x => k x
  end.


Global Instance Monad_option : Monad option :=
  Build_Monad option (@ret_option) (@bind_option).


Global Instance Eq1Equivalence_option : @Eq1Equivalence option _ Eq1_option.
Proof.
  constructor.
  - repeat intro.
    destruct x; reflexivity.
  - repeat intro.
    destruct x; destruct y; inversion H; try reflexivity.
  - repeat intro.
    destruct x; destruct y; destruct z; inversion H; inversion H0; try reflexivity.
Qed.

Global Instance MonadLawsE_option : @MonadLawsE option _ _.
Proof.
  constructor.
  - intros. reflexivity.
  - intros. cbn. destruct x; reflexivity.
  - intros. destruct x; reflexivity.
  - repeat intro.
    destruct x, y; inversion H. auto. cbn. subst.
    rewrite H0. reflexivity.
Qed.    
                                  
            
