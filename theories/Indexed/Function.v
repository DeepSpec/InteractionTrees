
From ITree Require Import
     Basics.Basics
     Basics.Category
     Indexed.Sum.


Definition IFun (E F : Type -> Type) : Type := E ~> F.

Definition applyIFun {E F} (f : IFun E F) : E ~> F := f.

Instance Eq2_IFun : Eq2 IFun :=
  fun E F f1 f2 => forall R (e : E R), f1 _ e = f2 _ e.

Instance Id_IFun : Id_ IFun :=
  fun E _ e => e.

Instance Cat_IFun : Cat IFun :=
  fun E F G f1 f2 R e => f2 _ (f1 _ e).

Instance Initial_void1 : Initial IFun void1 :=
  fun _ _ v => match v : void1 _ with end.

Definition case_sum1 {A B C : Type -> Type} (f : A ~> C) (g : B ~> C)
  : A +' B ~> C
  := fun _ ab =>
       match ab with
       | inl1 a => f _ a
       | inr1 b => g _ b
       end.

Instance Elim_sum1 : CoprodElim IFun sum1 := @case_sum1.
Instance Inl_sum1 : CoprodInl IFun sum1 := @inl1.
Instance Inr_sum1 : CoprodInr IFun sum1 := @inr1.
