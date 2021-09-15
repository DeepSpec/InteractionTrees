From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

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
     Events.Exception
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
     Secure.SecurityImpExc.SecurityImp
.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.


Definition handle_state_io {E} : forall A, (stateE +' IOE) A -> stateT map (itree (E +' IOE)) A :=
  fun _ e => match e with
          | inl1 el => handleState _ el
          | inr1 er => fun s => r <- ITree.trigger (inr1 er);; Ret (s, r) end. 

Definition handle_exc :forall A, exceptE sensitivity A -> stateT map  (itree ((exceptE (sensitivity * map))  +' IOE) ) A :=
  fun _ e => match e with
            | Throw _ l => fun s => r <- ITree.trigger (inl1 (Throw _ (l, s) ) );; Ret (s, r) end.

Program Definition handle_imp_exc : forall A, ((exceptE sensitivity) +' stateE +' IOE) A -> stateT map (itree ((exceptE (sensitivity * map))  +' IOE) ) A :=
  fun _ e => match e with
          | inl1 exc => handle_exc _ exc
          | inr1 er => handle_state_io _ er end.

Definition interp_imp {R} (t : itree (impExcE +' stateE +' IOE) R ) : stateT map (itree (exceptE (sensitivity * map) +' IOE)) R :=
  interp_state handle_imp_exc t. 
