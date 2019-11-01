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
     Dijkstra.DijkstraMonadExamples
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive Void : Type -> Type := .

Section PureItree.

  (*how to deal with nonterminsim*)
  (* partial correctness itrees   *)
  (* match t with Ret a => p (inl a)  *)
  
  Definition PureItree A := itree Void A.

  (* can interpretation deal with infinite taus*)

  Definition _PureItreeSpec A := (itree Void A-> Prop) -> Prop.

  Definition _retpi A (a : A) : _PureItreeSpec A := fun p => p (ret a).

  (*I will axiomatize into existence two functions on itrees and talk to steve about if they are 
   feasible*)
  

  Definition monotonici A (w : _PureItreeSpec A) :=
    forall (p p' : itree Void A -> Prop), (forall i', p i' -> p' i') -> w p -> w p'. 

 (* is is_val a decidable prop   *)
  Inductive is_val A (a : A) : itree Void A -> Prop :=
    | base (t : itree Void A ) :  t = ret a ->  is_val A a t
    | tau (t : itree Void A) : is_val A a (Tau t) .

  Definition _bindpi A B (m : _PureItreeSpec A ) (f : A -> _PureItreeSpec B) : _PureItreeSpec B :=
    fun (p : itree Void B -> Prop) => 
      m (fun (i : itree Void A) => forall a, is_val A a i -> f a p).

  Lemma bindpi_monot : forall A B (w : _PureItreeSpec A) (f : A -> _PureItreeSpec B), 
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B (_bindpi A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *. intros.
    remember (fun i : itree Void A => forall a : A, is_val A a i -> f a p) as fp.
    remember (fun i : itree Void A => forall a : A, is_val A a i -> f a p') as fp'.
    enough (forall i, fp i -> fp' i).
    - apply H with (p := fp); auto.
    - subst. intros. apply H0 with (p := p); auto.
  Qed.

  (* does this satisfy the monad laws? is it unique in some sense, if not what are the implications of
   this choice*)
  
  (* maybe could parameterize bind on a predicate is_val A a itree -> Prop, and that predicate
     determines how nonterminism is handled, that shouldn't be hard, my proof of monot
     didn't seem to rely on the def of is_val, likely bad choices would break monad laws?
     *)
                       

(* is this monotonic?   *)

End PureItree.

Section StateItree.
  Context (S : Type).
  
  Definition StateItree A := itree (stateE S) A.

  Definition _StateItreeSpec A := (itree Void (A * S) -> Prop) -> S -> Prop.

  Definition _interpStateSpec : (stateE S) ~> (_StateSpec S) :=
    fun _ (ev : stateE S _) =>
      match ev with
        | Get _ => fun p s => p (s,s)
        | Put _ s => fun p s' => p (tt,s) end.

  Lemma monot_interpStateSpec : forall A ev, monotonic S (_interpStateSpec A ev).
    Proof.
      unfold monotonic. intros. cbv. destruct ev; auto.
    Qed.

  Definition monotonicis A (w : _StateItreeSpec A) := 
    forall (p p' : itree Void (A * S) -> Prop ) s, (forall i s', p (ret (i,s')) -> p' (ret (i,s')))
                                                                      -> w p s -> w p' s.

  Definition _retis A (a : A) : _StateItreeSpec A :=
    fun p s => p (ret (a,s)).

  Lemma retis_monot : forall A a, monotonicis A (_retis A a).
  Proof.
    unfold monotonicis. intros. unfold _retis in *. auto.
  Qed.
(* bind I think needs some coinduction, I'll leave it out for now
  Definition _bindis A B (m : _StateItreeSpec A) (f : A -> _StateItreeSpec B) :=
    fun p s => m (fun '(i,s') =>  ) s

    if i = tau ^ ω then p (i,s') since i has either type _StateItreeSpec A or _StateItreeSpec B
    else i = tau ^* (Ret a) then p (ret (a,s'))

    problem is the first case doesn't terminate, need more info on coinduction from Steve maybe?
*)



  Definition StateItreeSpec A := {w : _StateItreeSpec A | monotonicis _ w}.

  Definition interpStateSpecCore : forall A, (stateE S A) -> (itree Void (StateSpec S A)) :=
    fun A ev => 
    ret (exist _ (_interpStateSpec A ev) (monot_interpStateSpec A ev)).

  Definition StateSpecT (M : Type -> Type) (A : Type) := (M (A * S)%type -> Prop) -> S -> Prop.

(*
  Global Instance StateSpecIter : Monad

  Definition interpStateSpec (A : Type) (t : itree (stateE S) A) : 
    StateSpecT  (itree Void) A := interp interpStateSpecCore t.

  *)
(*
  Definition _retsis A (a: A) : _StateItreeSpec A := fun p s => p (Itree.ret _ (a,s)).

  Definition _stateH A (ev : stateE S) :=
    match ev with
    | Get => fun 


  

  CoInductive t :=.
*)
