From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
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
     Core.Divergence
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Definition envF (E : Type -> Type) (env : Type) : Type :=
  forall (R : Type), E R -> (R * env).

CoInductive env (E : Type -> Type) := go { _observe : envF E (env E) }.

Definition use {E R} (en : env E) (e : E R): (R * (env E)) :=
  match en with
  | {| _observe := f |} => f R e
end.


Definition interp_env {E : Type -> Type} {R : Type} : env E -> itree E R -> Delay R :=
  cofix interp_ (env : env E) (t : itree E R) : Delay R := 
  match (observe t) with
  | RetF r => Ret r
  | TauF t' => Tau (interp_ env t')
  | VisF e k => let '(a, env') := use env e in
               Tau (interp_ env' (k a)) end.
(*
(*problem, the result of this interpretation is just Delay, when there are more general
  monadic effects going on to keep track of *)
Lemma interp_env_morph : forall (E : Type -> Type) (R : Type) (env : env E) (t : itree E A) (f : A -> itree E B),
    interp_env env (t >>= f) ≈ (interp_env)
*)
Section State.

Context (S : Type).

Inductive stateE : Type -> Type :=
  | Get : stateE S
  | Put (s : S) : stateE unit .


CoFixpoint stateEnv (s : S) : env stateE :=
  {|
    _observe := fun (R : Type) (ev : stateE R) =>
                  match ev in stateE T  return (T * env stateE) with
                  | Get => (s, stateEnv s)
                  | Put s' => (tt, stateEnv s') end
  |}.

End State.

Lemma


(*should be able to prove equivalent to a typical state event thing*)
     
