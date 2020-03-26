(** * Exception event *)

(* begin hide *)

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.FunctionalExtensionality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
     Dijkstra.StateSpecT
   (*  Simple *)
.

(* end hide *)

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** Throw exceptions of type [Err]. *)
Variant exceptE (Err : Type) : Type -> Type :=
| Throw : Err -> exceptE Err void.

(** Since the output type of [Throw] is [void], we can make it an action
    with any return type. *)
Definition throw {Err : Type} {E : Type -> Type} `{exceptE Err -< E} {X}
           (e : Err)
  : itree E X
  := vis (Throw _ e) (fun v : void => match v with end).

Section Exception.
  
  Context (E : Type).
  
  Section ExcT.
    
    Context (M : Type -> Type).
    Context {EqMM : EqM M}.
    Context {MonadM : Monad M}.
    Context {MonadLawsM : MonadLaws M}.
    Context {EquivRel : forall A, Equivalence (EqMM A) }.
    Context {MonadIterM : MonadIter M}.


    Definition Exc (A : Type) := M (E + A).

    Definition ret_exc (A : Type) (a : A) : Exc A := ret (inr a).

    Definition bind_exc (A B : Type) (m : M (E + A) ) (f : A -> Exc B) :=
      bind m (fun x  => match x with | inl e => ret (inl e) | inr a => f a end).

    Global Instance MonadExc : Monad Exc :=
      {
        ret := ret_exc ;
        bind := bind_exc;
      }.

    Global Instance EqExc : EqM Exc := fun _ m1 m2 =>
           EqMM _ m1 m2.

    Global Instance MonadLawsExc : MonadLaws Exc.
    Proof.
      destruct MonadLawsM.
      constructor.
      - intros A B f a. cbn. apply bind_ret.
      - intros A m. cbn. specialize (ret_bind (E +A)%type m).
        unfold bind_exc, ret_exc. Admitted.
   End ExcT.
End Exception.
