(** * Kleisli category *)

(** The category of "effectful functions", of type [a -> m b],
  for some monad [m]. *)

(** Note that this is not quite a Kleisli category over the
  category [Fun], as the notion of morphism equivalence is
  different. The category [Fun] uses pointwise equality,
  [eq ==> eq], while [Kleisli m] uses pointwise equivalence,
  [eq ==> eq1], for an equivalence relation [eq1] associated
  with the monad [m]. The right underlying category for [Kleisli]
  would be a category of setoids and respectful functions, but
  this seems awkward to program with. Investigating this
  question further is future work.
 *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function.
(* end hide *)

Implicit Types m : Type -> Type.
Implicit Types a b c : Type.

Definition Kleisli m a b : Type := a -> m b.

(* SAZ: We need to show how these are intended to be used. *)
(** A trick to allow rewriting in pointful contexts. *)
Definition Kleisli_arrow {m a b} : (a -> m b) -> Kleisli m a b := fun f => f.
Definition Kleisli_apply {m a b} : Kleisli m a b -> (a -> m b) := fun f => f.


Definition pure {m} `{MRet m} {a b} (f : a -> b) : Kleisli m a b :=
  fun x => mret (f x).

Section Instances.
  Context {m : Type -> Type}.
  Context `{MRet m, MBind m}.
  Context `{Eq1 m}.

  #[global] Instance Eq2_Kleisli : Eq2 (Kleisli m) :=
    fun _ _ => pointwise_relation _ eq1.

  #[global] Instance Cat_Kleisli : Cat (Kleisli m) :=
    fun _ _ _ u v x =>
      u x ≫= (fun y => v y).

  Definition map {a b c} (g:b -> c) (ab : Kleisli m a b) : Kleisli m a c :=
     cat ab (pure g).

  #[global] Instance Initial_Kleisli : Initial (Kleisli m) void :=
    fun _ v => match v : void with end.

  #[global] Instance Id_Kleisli : Id_ (Kleisli m) :=
    fun _ => pure id.

  #[global] Instance Case_Kleisli : Case (Kleisli m) sum :=
    fun _ _ _ l r => case_sum _ _ _ l r.

  #[global] Instance Inl_Kleisli : Inl (Kleisli m) sum :=
    fun _ _ => pure inl.

  #[global] Instance Inr_Kleisli : Inr (Kleisli m) sum :=
    fun _ _ => pure inr.

  #[global] Instance Iter_Kleisli `{MonadIter m} : Iter (Kleisli m) sum :=
    fun a b => Basics.iter.

End Instances.
