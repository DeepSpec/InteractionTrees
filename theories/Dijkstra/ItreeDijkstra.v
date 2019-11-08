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
Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).


Section PureItree.

  (*how to deal with nonterminsim*)
  (* partial correctness itrees   *)
  (* match t with Ret a => p (inl a)  *)
  
  Definition PureItree A := itree Void A.

  (* can interpretation deal with infinite taus*)

  Definition _PureItreeSpec A := forall (p : itree Void A -> Prop), (tau_invar Void A p) -> Prop.

  Definition _retpi A (a : A) : _PureItreeSpec A := fun p _ => p (ret a).

  (*I will axiomatize into existence two functions on itrees and talk to steve about if they are 
   feasible*)
  
  
 
  Definition monotonici A (w : _PureItreeSpec A) :=
    forall (p p' : itree Void A -> Prop) (Hp : tau_invar Void A p) (Hp' :tau_invar Void A p'),
                                          (forall i', p i' -> p' i') -> w p Hp -> w p' Hp'. 
(* need the fact that bind preserves this tau invariance condition*) 

  Definition PureItreeSpec A := {w : _PureItreeSpec A | monotonici A w}.

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

  Lemma bind_pred_tau_invar : forall A B (f : A -> _PureItreeSpec B) 
                                     (p : itree Void B -> Prop) (Hp : tau_invar Void B p), 
      tau_invar Void A (fun (i : itree Void A) => forall a, is_val A a i -> f a p Hp).
  Proof.
    intros. unfold tau_invar in *. split; intros;
    apply H; specialize (is_val_tau_invar A a t) as Ht; tauto.
  Qed.


  Definition _bindpi A B (m : _PureItreeSpec A ) (f : A -> _PureItreeSpec B) : _PureItreeSpec B :=
    fun (p : itree Void B -> Prop) (Hp : tau_invar Void B p) => 
      m (fun (i : itree Void A) => forall a, is_val A a i -> f a p Hp) (bind_pred_tau_invar A B f p Hp).

  Lemma bindpi_monot : forall A B (w : _PureItreeSpec A) (f : A -> _PureItreeSpec B), 
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B (_bindpi A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *. 
    (*specialize H with (p := (fun i : itree Void A => forall a : A, is_val A a i -> f a p Hp)) as H'.
    enough () *)
    set (fun i  p0 Hp0 => forall a : A, is_val A a i -> f a p0 Hp0) as fp.
    (*remember (fun p Hp => bind_pred_tau_invar A B f p Hp) as fHp. *)
    enough (forall i, fp i p Hp -> fp i p' Hp').
    - eapply H with (p := fun i => fp i p Hp).
      + intros. subst. apply H3 with (i := i'); auto.
      + subst. cbn. apply H2.
    - unfold fp. intros.eapply H0; eauto.
  Qed.

  Definition retpi A (a : A) : PureItreeSpec A :=
    exist _ (_retpi A a) (retpi_monot A a).

  Definition bindpi A B (w : PureItreeSpec A) (f : A -> PureItreeSpec B) :=
    let '(exist _ w' Hw') := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist _ (_bindpi A B w' f') (bindpi_monot A B w' f' Hw' Hf').

  Global Instance PureItreeSpecMonad : Monad PureItreeSpec :=
    {
      ret := retpi;
      bind := bindpi
    }.

  Global Instance PureItreeSpecEq : EqM PureItreeSpec :=
    fun A w1 w2 => forall (p : itree Void A -> Prop) (Hp : tau_invar Void A p), proj1_sig w1 p Hp <-> proj1_sig w2 p Hp.

  Lemma bindpi_retpi : forall A B (f : A -> PureItreeSpec B) (a : A), 
      bind (ret a) f ≈ f a.
    Proof.
      intros. split.
      - cbn. unfold _bindpi. unfold _retpi. intros. apply H. constructor. 
      - cbv. intros. inversion H0. subst. auto.
    Qed.

  Lemma retpi_bindpi : forall A (w : PureItreeSpec A), bind w (fun x => ret x) ≈ w.
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

  Lemma bindpi_bindpi : forall (A B C : Type) (w : PureItreeSpec A) 
                               (f : A -> PureItreeSpec B) (g : B -> PureItreeSpec C),
      bind (bind w f) g ≈ bind w (fun a => bind (f a) g).

  Admitted.

  Global Instance PureItreeSpecLaws : MonadLaws PureItreeSpec.
  Proof.
    constructor.
    - intros A B f a. cbv. intros. destruct (f a) as [w Hw] eqn : Heq. split; intros.
      + unfold monotonici in *. eapply Hw.
        * intros. admit.
        *

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
