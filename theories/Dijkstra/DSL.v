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
     Dijkstra.ITrace
     Dijkstra.ITraceBind
     Dijkstra.EuttDiv
     Dijkstra.ITracePreds
     Dijkstra.ITraceBindTrigger
     Dijkstra.TracesIT
     Dijkstra.StateSpecT
     Dijkstra.StateIOTrace
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* begin hide *)
From ITree Require Import
     Events.MapDefault.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.


Inductive aexp : Set := .

Inductive bexp : Set :=.

Inductive com : Set :=.



(*Should there be a never constructor?*)
(*how should these interact with *)
Variant trace_propF (E : Type -> Type ) (R : Type) (F : Type) : Type := 
  | topF
  | immEF (PE : forall A, EvAns E A -> Prop) (tl : F) 
  | evEF (PE : forall A, EvAns E A -> Prop) (tl : F)
  | immRetF (PR : R -> Prop)
  | evRetF (PR : R -> Prop)
  | extlF {A : Type} (Pex : A -> F)
  | foralltlF {A : Type} (Pforall : A -> F)
.

Arguments topF {E} {R} {F}.
Arguments immEF {E} {R} {F}.
Arguments evEF {E} {R} {F}.
Arguments immRetF {E} {R} {F}.


Arguments evRetF {E} {R} {F}.
Arguments extlF {E} {R} {F} {A}.
Arguments foralltlF {E} {R} {F} {A}.

CoInductive trace_prop E R :=
  gotl { _observetl : trace_propF E R (trace_prop E R) }.

Notation top := ( {| _observetl := topF |} ).
Notation immE PE tl := ({| _observetl := immEF PE tl |}).
Notation immRet PR := ({| _observetl := immRetF PR |}).
Notation evRet PR := ({| _observetl := evRetF PR |}).
Notation evE PE tl := ({| _observetl := evEF PE tl |}).

Notation extlf Pex := ({| _observetl :=  extlF Pex |} ).
Notation foralllf Pex := ({| _observetl :=  foralltlF Pex |} ). 

Notation trace_prop' E R := (trace_propF E R (trace_prop E R)).
Definition observetl {E} {R} (tp : trace_prop E R) : trace_prop' E R:=
  _observetl _ _ tp.

Inductive trace_sat_trace_prop E R (F : trace_prop E R -> itrace E R -> Prop) :
  trace_prop' E R -> itrace' E R -> Prop := 
  | tstp_top ot : trace_sat_trace_prop E R F topF ot
  | tsto_immEF {A : Type} (e : EvAns E A) (k : A -> itrace E R) 
               (PE : forall A, EvAns E A -> Prop) (tl : trace_prop E R) :
      PE A e -> (forall a : A, F tl (k a) ) ->
      trace_sat_trace_prop E R F (immEF PE tl) (VisF e k) 
  | tsto_immRetF (PR : R -> Prop) r : PR r -> trace_sat_trace_prop E R F (immRetF PR) (RetF r)
  | tsto_extllF {A : Type} (a : A) (Pex : A -> trace_prop E R) (tr : itrace E R) : 
      F (Pex a) tr -> trace_sat_trace_prop E R F (extlF Pex) (observe tr)
  | tsto_foralltl {A : Type} (Pforall : A -> trace_prop E R) (tr : itrace E R) :
      (forall a : A, F (Pforall a) tr) -> trace_sat_trace_prop E R F (foralltlF Pforall) (observe tr)
.

Variant reads_n (n : nat) : forall A, EvAns IO A -> Prop :=
  | rn : reads_n n unit (evans nat Read n).
Variant writes_n (n : nat) : forall A, EvAns IO A -> Prop :=
  | wn : writes_n n unit (evans unit (Write n) tt ).
Definition topl {E} {R} : trace_prop E R := top.

Definition mults_n_prop {R} n: trace_prop IO R :=
  (cofix mnp m := immE (writes_n m) (mnp (n + m) )) 0.
Definition read_n_to_mults_n : trace_prop IO unit :=
           extlf 
             (fun n : nat => immE (reads_n n) (mults_n_prop n) ).
(*
this rule seems like it only works for divergent loops
seems to have the good property of keeping P as an invariant
F is a closed term 
          {{ P a' }} body a' {{ extlf a'', evRet (fun a''' => a'' = a''' /\ P a'') /\ 
            F (fun _ => halt) a'   }}
---------------------------------------------------------------------------
          {{ P a }}  iter body a {{ (cofix inv a' := F inv a') a }}
*)

(*

  {{ P a' }} body a' {{ }}
------------------------------------------------------
  {{ P a  }} iter body a {{ iter Pb a }}

*)


(* {{ P }} t1 {{ P ++ Q }} {{ R }} t2 {{ S }} 
----------------------------------------------
            t1;; t2

*)

(*
CoFixpoint eutt_to {E} {R} (otr : itrace' E R) : trace_prop E R :=
  match otr with
  | RetF r => immRet (fun r' => r = r')
  | VisF (evans _ e a) k =>  immE (fun _ ) (eutt_to (observe (k tt)) )
  | _ => top end.
*)
(*should I wrap up the cofix?*)
