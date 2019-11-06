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

Section PureITree.

  (*how to deal with nonterminsim*)
  (* partial correctness itrees   *)
  (* match t with Ret a => p (inl a)  *)
  
  Definition PureITree A := itree Void A.

  (* can interpretation deal with infinite taus*)

  Definition _PureITreeSpec A := (itree Void A-> Prop) -> Prop.

  Definition _retpi A (a : A) : _PureITreeSpec A := fun p => p (ret a).

  (*I will axiomatize into existence two functions on itrees and talk to steve about if they are 
   feasible*)
  
  Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).
 
  Definition monotonici A (w : _PureITreeSpec A) :=
    forall (p p' : itree Void A -> Prop), (forall i', p i' -> p' i') -> w p -> w p'. 

  Definition PureITreeSpec A := {w : _PureITreeSpec A | monotonici A w}.

  Lemma retpi_monot : forall A (a : A), monotonici A (_retpi A a).
  Proof.
    unfold monotonici. intuition. unfold _retpi in *. auto.
  Qed.

 (* is is_val a decidable prop   *)
  Inductive is_val A (a : A) : itree Void A -> Prop :=
    | base :  is_val A a (ITreeDefinition.Ret a)
    | tau (t : itree Void A): is_val A a t -> is_val A a (Tau t) .


  Lemma is_val_tau_invar : forall A (a : A), tau_invar Void A (is_val A a).
  Proof.
    intros. unfold tau_invar. split; intros.
    - constructor. auto.
    - inversion H. auto.
  Qed.

  (* maybe specifications only take tau invariant propositions  *)


  Definition _bindpi A B (m : _PureITreeSpec A ) (f : A -> _PureITreeSpec B) : _PureITreeSpec B :=
    fun (p : itree Void B -> Prop) => 
      m (fun (i : itree Void A) => forall a, is_val A a i -> f a p).

  Lemma bindpi_monot : forall A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B), 
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B (_bindpi A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *. intros.
    remember (fun i : itree Void A => forall a : A, is_val A a i -> f a p) as fp.
    remember (fun i : itree Void A => forall a : A, is_val A a i -> f a p') as fp'.
    enough (forall i, fp i -> fp' i).
    - apply H with (p := fp); auto.
    - subst. intros. apply H0 with (p := p); auto.
  Qed.

  Definition retpi A (a : A) : PureITreeSpec A :=
    exist _ (_retpi A a) (retpi_monot A a).

  Definition bindpi A B (w : PureITreeSpec A) (f : A -> PureITreeSpec B) :=
    let '(exist _ w' Hw') := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist _ (_bindpi A B w' f') (bindpi_monot A B w' f' Hw' Hf').

  Global Instance PureItreeSpecMonad : Monad PureITreeSpec :=
    {
      ret := retpi;
      bind := bindpi
    }.

  Global Instance PureItreeSpecEq : EqM PureITreeSpec :=
    fun A w1 w2 => forall (p : itree Void A -> Prop), proj1_sig w1 p <-> proj1_sig w2 p.

  Lemma bindpi_retpi : forall A B (f : A -> PureITreeSpec B) (a : A), 
      bind (ret a) f ≈ f a.
    Proof.
      intros. split.
      - cbn. unfold _bindpi. unfold _retpi. intros. apply H. constructor. 
      - cbv. intros. inversion H0. subst. auto.
    Qed.

  Lemma retpi_bindpi : forall A (w : PureITreeSpec A), bind w (fun x => ret x) ≈ w.
  Proof.
    intros. destruct w as [ w Hw]. split.
    - intros. simpl in *. unfold _bindpi in H.
      unfold _retpi in H. cbv in H.
      unfold monotonici in *. eapply Hw.
      2: apply H. intros. simpl in H0. admit.
      (*forall i : PureItree, exists a, is_val a i \/ inf_tau i  *)
      (*forall t t', inf_tau t -> inf_tau t' -> forall P, P t <-> P t'  *)
    - simpl. cbv. intros. unfold monotonici in Hw. apply Hw with (p := p); auto.
      intros. induction H1; auto. (* need a notion of Tau invariant predicates, or need to rethink this  *)
      
   Admitted.    

  Lemma bindpi_bindpi : forall (A B C : Type) (w : PureITreeSpec A) 
                               (f : A -> PureITreeSpec B) (g : B -> PureITreeSpec C),
      bind (bind w f) g ≈ bind w (fun a => bind (f a) g).

  Admitted.

  Global Instance PureItreeSpecLaws : MonadLaws PureITreeSpec.
  Proof.
    constructor.
    - intros A B f a. cbv. intros. destruct (f a) as [w Hw] eqn : Heq. split; intros.
      + unfold monotonici in *. eapply Hw.
        * intros. admit.
        * Abort.

  (* does this satisfy the monad laws? is it unique in some sense, if not what are the implications of
   this choice*)
  
  (* maybe could parameterize bind on a predicate is_val A a itree -> Prop, and that predicate
     determines how nonterminism is handled, that shouldn't be hard, my proof of monot
     didn't seem to rely on the def of is_val, likely bad choices would break monad laws?
     *)
                       

(* is this monotonic?   *)

End PureITree.

Section StateITree.
  Context (S : Type).
  
  Definition StateITree A := itree (stateE S) A.

  Definition _StateITreeSpec A := (itree Void (A * S) -> Prop) -> S -> Prop.

  Definition _interpStateSpec : (stateE S) ~> (_StateSpec S) :=
    fun _ (ev : stateE S _) =>
      match ev with
        | Get _ => fun p s => p (s,s)
        | Put _ s => fun p s' => p (tt,s) end.

  Lemma monot_interpStateSpec : forall A ev, monotonic S (_interpStateSpec A ev).
    Proof.
      unfold monotonic. intros. cbv. destruct ev; auto.
    Qed.

  Definition monotonicis A (w : _StateITreeSpec A) := 
    forall (p p' : itree Void (A * S) -> Prop ) s, (forall i s', p (ret (i,s')) -> p' (ret (i,s')))
                                                                      -> w p s -> w p' s.

  Definition _retis A (a : A) : _StateITreeSpec A :=
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



  Definition StateITreeSpec A := {w : _StateITreeSpec A | monotonicis _ w}.

  Definition interpStateSpecCore : forall A, (stateE S A) -> (itree Void (StateSpec S A)) :=
    fun A ev => 
    ret (exist _ (_interpStateSpec A ev) (monot_interpStateSpec A ev)).

  Definition StateSpecT (M : Type -> Type) (A : Type) := (M (A * S)%type -> Prop) -> S -> Prop.
End StateITree. 
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
