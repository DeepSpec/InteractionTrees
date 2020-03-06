From ExtLib Require Import
     Structures.Monad.
From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Monad.

Module Foo.

  (* Variable (crazy: forall (A: Type), A -> A -> Prop). *)
  Definition PropM: Type -> Type := fun A => A -> Prop.

  Definition ret: forall A, A -> PropM A := fun _ a b => a = b.

  Definition eqm: forall A, PropM A -> PropM A -> Prop :=
    fun _ P Q => forall a, P a <-> Q a.

  Definition bind {A B} (PA: PropM A) (K: A -> PropM B) : PropM B :=
    fun b => exists a, PA a /\ K a b.

End Foo.

(* See [PropT.v] in the Vellvm repo for the exact framework to follow with respect to typeclasses, as well as a proof of most monad laws for [PropTM (itree E)] *)
Section Transformer.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.
  Context {ITERM : MonadIter m}.

  Definition PropTM : Type -> Type :=
    fun A => m A -> Prop.

  Definition closed_eqm {A} (P: m A -> Prop) := forall a a', eqm a a' -> P a -> P a'.

  (* Design choice 1: closed or not by construction? *)
  Definition PropTM' : Type -> Type :=
    fun A => {P: m A -> Prop | closed_eqm P}.

  (* Design choice 2: (ma = ret a) or eqm ma (ret a)? *)
  Definition ret : forall A, A -> PropTM A :=
    fun A (a: A) (ma: m A) => eqm ma (ret a).

  Definition eqm': forall A, PropTM A -> PropTM A -> Prop :=
    fun _ P Q => forall a, P a <-> Q a.

  Definition eqm: forall A, PropTM A -> PropTM A -> Prop :=
    fun _ P Q => (forall a, P a -> exists a', eqm a a' /\ Q a) /\
              (forall a, Q a -> exists a', eqm a a' /\ P a).

  (* bind {ret 1} (fun n => if n = 0 then empty set else {ret n})
     = empty_set
     ma = ret 1
     What will be my kb?
     kb := fun n =>if n = 0 then ret 0 else (ret n)) for instance
     But no matter the choice, with the following definition, we get the empty_set for the bind where we kinda would like {ret 1;; ret 1 ~~ ret 1}
     It feels like a solution would be to check membership to K only over values a that "ma can return". What is this notion over a monad in general?
   *)

  Definition bind {A B} (PA: PropTM A) (K: A -> PropTM B) : PropTM B :=
    fun mb => exists (ma: m A) (kb: A -> m B),
        PA ma /\
        (forall a, K a (kb a)) /\
        Monad.eqm mb (bind ma kb).

  Definition MonadIter_Prop : MonadIter PropTM :=
    fun R I step i r =>
      exists (step': I -> m (I + R)%type),
        (forall j, step j (step' j)) /\ CategoryOps.iter step' i = r.

  (* What is the connection (precisely) with this continuation monad? *)
  Definition ContM: Type -> Type := fun A => (A -> Prop) -> Prop.

End Transformer.
