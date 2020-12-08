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

Module TraceWithPredAndEv.

Variant SpecEv (E : Type -> Type) : Type -> Type :=
  | top : SpecEv E void
  | immEv (PE : forall A, EvAns E A -> Prop) : SpecEv E unit
  (* handle in a different way | immRet *)
  (* The continuation k is the φ so Vis (exEv A) (fun a => k a) 
     exists a : A, φ(a)
     same for forall
 *)
  | exEv (A : Type) : SpecEv E A
  | forallEv (A : Type) : SpecEv E A
  (* eventually predicates*)
  | evEv (PE : forall A, EvAns E A -> Prop) : SpecEv E unit

  (* eventually ret cannot be continued*)
  | evRet {R : Type} (PR : R -> Prop) : SpecEv E void


 .
Arguments top {E}.
Arguments immEv {E}.
Arguments evEv {E}.
Arguments evRet {E} {R}.
Arguments exEv {E}.
Arguments forallEv {E}.

Definition itree_spec E A := itree (SpecEv E) (A -> Prop).
Definition itree_spec' E A := itree' (SpecEv E) (A -> Prop).

Inductive satisfiesF {E R} (F : itrace E R -> itree_spec E R -> Prop) : 
  itrace' E R -> itree_spec' E R -> Prop :=
  (* Basic ITree nodes*)
  | satisfies_ret (r : R) (PR : R -> Prop) : PR r -> satisfiesF F (RetF r) (RetF PR)
  | satisfies_tau tr phi : F tr phi -> satisfiesF F (TauF tr) (TauF phi)
  | satisfies_taur otr1 tr2 : satisfiesF F otr1 (observe tr2) -> satisfiesF F otr1 (TauF tr2)
  | satisfies_taul tr1 otr2 : satisfiesF F (observe tr1) otr2 -> satisfiesF F (TauF tr1) otr2
  (* inductive tau cases *)
  (* trivial spec events*)
  | satisfies_top tr (kphi : void -> itree_spec E R) : satisfiesF F (observe tr) (VisF top kphi)
  (* immediate spec events*)
  | satisfies_immEv (A : Type) (e : EvAns E A) (PE : forall A, EvAns E A -> Prop) 
                    (ktr : A -> itrace E R) kphi : 
      (forall a : A, F (ktr a) (kphi tt)) -> (PE A e) -> satisfiesF F (VisF e ktr) (VisF (immEv PE) kphi) 
  (* eventual spec events*)
  | satisfies_evEv_pass  (e : EvAns E unit) (PE : forall A, EvAns E A -> Prop) 
                    (ktr : unit -> itrace E R) kphi :
      satisfiesF F (observe (ktr tt)) (VisF (evEv PE) kphi )  -> satisfiesF F (VisF e ktr) (VisF (evEv PE) kphi )
  | satisfies_evEv (A : Type) (e : EvAns E A) (PE : forall A, EvAns E A -> Prop) 
                    (ktr : A -> itrace E R) kphi :
      (forall a : A, F (ktr a) (kphi tt) ) -> (PE A e) -> satisfiesF F (VisF e ktr) (VisF (evEv PE) kphi) 
  | satisfies_evRet_pass (e : EvAns E unit) (PR : R -> Prop) (ktr : unit -> itrace E R) (kphi : void -> itree_spec E R) :
    satisfiesF F (observe (ktr tt) ) (VisF (evRet PR) kphi ) -> satisfiesF F (VisF e ktr) (VisF (evRet PR) kphi)
  | satisfies_evRet (r : R) (PR : R -> Prop) (kphi : void -> itree_spec E R) :
      PR r -> satisfiesF F (RetF r) (VisF (evRet PR) kphi)
  (* quantifiers*)
  (* currently coinductive constructors, so forall a, forall b, forall c, ... is a trivially true spec
     this seems harmless but worth keeping an eye on
*)
  | satisfies_exEv (A : Type) (a : A) tr kphi :
    F tr (kphi a) -> satisfiesF F (observe tr) (VisF (exEv A) kphi )
  | satisfies_forallEv (A : Type) tr kphi :
      (forall a : A, F tr (kphi a) ) -> satisfiesF F (observe tr) (VisF (forallEv A) kphi)
    
.

Hint Constructors satisfiesF.
Definition satisfies_ {E R} (F : itrace E R -> itree_spec E R -> Prop) (tr : itrace E R) (phi : itree_spec E R) := 
  satisfiesF F (observe tr) (observe phi).
Hint Unfold satisfies_.

Lemma monot_satisfies {E R} : monotone2 (@satisfies_ E R).
Proof.
  red. intros. red. red in IN. induction IN; eauto.
Qed.
Hint Resolve monot_satisfies : paco.

Definition satisfies {E R} (tr : itrace E R) (phi : itree_spec E R) : Prop := paco2 satisfies_ bot2 tr phi.

Definition and_spec {E R} (phi psi : itree_spec E R) := Vis (forallEv bool) (fun b => if b : bool then phi else psi). 
Definition or_spec {E R} (phi psi : itree_spec E R) := Vis (exEv bool) (fun b => if b : bool then phi else psi). 

Definition lift_left {E A B}: (A -> itree E B) -> (A + B) -> itree E B :=
  fun f x => 
    match x with
    | inl a' => f a'
    | inr b => Ret b end.

Instance itrace_monad {E} : Monad (itrace E) := Monad_itree.

Section LoopInvar.
  Context (E : Type -> Type).
  Context (A B : Type).
  Context (corec : (A -> itree E B) -> A -> itree E B).

  Context (body : A -> itree E (A + B) ).
  Context (a : A).

  Context (inv : A -> Prop).
  (*coind functor so the target is cofix G a := Tau (F G a) *)
  Context (F : (A -> itree_spec E B) -> A -> itree_spec E B ).
  Context (R : itrace E B -> Prop).
  Context (Hresp_eutt : forall tr tr', (tr ≈ tr')%itree -> R tr -> R tr').
  (*R respects eutt*)



  Definition parametric_pres : Prop :=
    forall (ktr : A -> itrace E B), (forall a, inv a -> R (ktr a) ) -> forall a', inv a -> 
          forall (tr : itrace E (A + B)), tr ⊑ (body a') ->  R (tr >>= (lift_left ktr) ).

  Definition loop_invar_goal : Prop := forall tr, tr ⊑ iter body a -> R tr.

  Definition loop_invar := parametric_pres -> loop_invar_goal.
  (* Not confident this is enough *)





  (* Check cofix G a := Tau (F G a). *)
  

End LoopInvar.

End TraceWithPredAndEv.

Module TraceBareBones.

Variant SpecEv (E : Type -> Type) : Type -> Type :=
  | Spec_Vis {A : Type} (e : EvAns E A) : SpecEv E A
  | Spec_forall { A : Type} : SpecEv E A
  | Spec_exists {A : Type} : SpecEv E A
  | Spec_empty {A : Type} : SpecEv E ( A -> void)
.
Arguments Spec_forall {E} {A}.
Arguments Spec_exists {E} {A}.
Arguments Spec_Vis {E} {A}.
Arguments Spec_empty {E} {A}.


Definition itree_spec E R := itree (SpecEv E) R.
Definition itree_spec' E R := itree' (SpecEv E ) R.


Inductive satisfiesF {E R} (F : itree_spec E R -> itrace E R -> Prop) : 
  itree_spec' E R -> itrace' E R -> Prop :=
  | satisfies_Ret (r : R) : satisfiesF F (RetF r) (RetF r)
  | satisfies_TauLR (phi : itree_spec E R) (tr : itrace E R) :
      F phi tr -> satisfiesF F (TauF phi) (TauF tr)
  | satisfies_TauL phi otr :
      satisfiesF F (observe phi) otr -> satisfiesF F (TauF phi) otr
  | satisfies_TauR ophi tr :
      satisfiesF F ophi (observe tr) -> satisfiesF F ophi (TauF tr)
  | satisfies_Spec_Vis A (e : EvAns E A) kphi ktr :
      (forall a : A, F (kphi a) (ktr a) ) -> satisfiesF F (VisF (Spec_Vis e ) kphi) (VisF e ktr)
  | satisfies_Spec_empty A (H : A -> void) (kphi : (A -> void) -> itree_spec E R)  tr :
      satisfiesF F (VisF Spec_empty kphi) (observe tr)
  | satisfies_forall A kphi tr :
      (forall a : A, F (kphi a) tr) -> satisfiesF F (VisF Spec_forall kphi) (observe tr)
  | satisfies_exists A (a : A) kphi tr :
      F (kphi a) tr -> satisfiesF  F (VisF Spec_exists kphi) (observe tr)
.

Definition and_spec {E R} (phi psi : itree_spec E R) :=
  Vis Spec_forall (fun b : bool => if b then phi else psi).

Definition or_spec {E R} (phi psi : itree_spec E R) :=
  Vis Spec_exists (fun b : bool => if b then phi else psi).

Definition empty_cont {A : Type} (v : void) : A :=
  match v with end.

Definition top {E R} : itree_spec E R :=
  Vis Spec_forall empty_cont.

Definition bot E R : itree_spec E R :=
  Vis Spec_exists empty_cont.



Definition forall_non_empty {E A R} (kphi : A -> itree_spec E R) : itree_spec E R :=
  and_spec (Vis Spec_forall kphi) (Vis Spec_exists (fun _ : A => top) ).

CoFixpoint obs_ {E R} (ot : itree' E R) : itree_spec E R :=
  match ot with 
  | RetF r => Ret r
  | TauF t => Tau ( obs_ (observe t) )
  | VisF e k => 
    or_spec
      (Vis Spec_forall (fun a => Vis (Spec_Vis (evans _ e a)) (fun _ => (obs_ (observe (k a))  ) ) ) )
      (Vis Spec_empty (fun H => Vis (Spec_Vis (evempty _ H e) ) empty_cont) )


  end.

Definition obs {E R} (t : itree E R) :=
  obs_ (observe t).


CoFixpoint obs_trace_ {E R} (otr : itrace' E R) : itree_spec E R :=
  match otr with
  | RetF r => Ret r
  | TauF t => Tau (obs_trace_ (observe t))
  | VisF (evans _ e a) k => 
    Vis (Spec_Vis (evans _ e a)) (fun _ => obs_trace_ (observe (k tt) ) ) 
  | VisF (evempty _ H e) k => 
    Vis (Spec_Vis (evempty _ H e) ) (empty_cont)
  end.

Definition obs_trace {E R} (tr : itrace E R) :=
  obs_trace_ (observe tr).

End TraceBareBones.
