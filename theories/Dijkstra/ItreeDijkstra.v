From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
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
     Dijkstra.DijkstraMonadExamples
     Core.Divergence
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive Void : Type -> Type := .
Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).


Section PureITree.

  (*how to deal with nonterminsim*)
  (* partial correctness itrees   *)
  (* match t with Ret a => p (inl a)  *)
  
  Definition PureITree A := itree Void A.

  (* can interpretation deal with infinite taus*)

  Definition _PureITreeSpec A := forall (p : itree Void A -> Prop), (tau_invar Void A p) -> Prop.

  Definition _retpi A (a : A) : _PureITreeSpec A := fun p _ => p (ret a).

  (*I will axiomatize into existence two functions on itrees and talk to steve about if they are 
   feasible*)
  
  

  Definition monotonici A (w : _PureITreeSpec A) :=
    forall (p p' : itree Void A -> Prop) (Hp : tau_invar Void A p) (Hp' :tau_invar Void A p'),
                                          (forall i', p i' -> p' i') -> w p Hp -> w p' Hp'. 
(* need the fact that bind preserves this tau invariance condition*) 


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

  Lemma tau_invar_prop_subst_aux : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), tau_invar Void A p ->
                               is_val A a t /\ is_val A a t' -> (p t -> p t').
  Proof.
    intros. destruct H0 as [Ht Ht'].
    induction  Ht'; induction Ht; auto.
    - apply H in H1. auto.
    - apply H in IHHt'. auto.
    - apply IHHt. apply H. auto.
  Qed.

  Lemma tau_invar_prop_subst : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), tau_invar Void A p ->
                               is_val A a t /\ is_val A a t' -> (p t <-> p t').
    Proof.
      split; intros; eapply tau_invar_prop_subst_aux; eauto.
      destruct H0. split; eauto.
    Qed.


  Lemma divergence_tau_invar : forall A, tau_invar Void A divergence.
  Proof.
    intros. split; intros.
    - pfold. left. constructor. auto.
    - pinversion H. subst. auto.
  Qed.

  Lemma is_val_div : forall A (t : itree Void A), ~(exists a, is_val A a t) -> divergence t.
    Proof.
      intros. pcofix CIH. pfold.      -
      destruct (observe t).
      Admitted.

  Lemma is_val_or_div : forall A (t : itree Void A), (exists a, is_val A a t) \/ divergence t.
    Proof.
      intros.
      destruct (classic (exists a, is_val A a t)); auto.
      right. apply is_val_div. auto.
    Qed.

  (* maybe specifications only take tau invariant propositions  *)

  Hint Constructors is_val.
(*fails some monad laws if w does not admit any finite trees, some of these variables might have the wrong
  scope *)
  (* fun t => (exists a, is_val A a t /\ w t /\ f a p Hp) \/ (divergence t /\ w divergence)  *)
(* should bind preserve infiniteness? *)
  CoFixpoint spin {A : Type} : itree Void A := Tau spin.

  Lemma bind_pred_tau_invar : forall A B (f : A -> _PureITreeSpec B) 
                                     (p : itree Void B -> Prop) (Hp : tau_invar Void B p), 
      tau_invar Void A (fun (t : itree Void A) => (exists a, is_val A a t /\ f a p Hp) \/ 
                                                  (divergence t /\ p spin)).
  Proof.
    intros. unfold tau_invar in *. split; intros.
    - destruct H.
      + left. destruct H as [a [Hvala Hfa] ]. exists a; split; auto.
      + destruct H. right. split; auto. apply divergence_tau_invar in H. auto.
    - destruct H.
      + left. destruct H as [a [Hvala Hfa] ]. exists a; split; auto. inv Hvala. auto.
      + destruct H. apply divergence_tau_invar in H. tauto.
  Qed.

  
  (*intuitively, you have two choices, prove the tree evaluates to a and prove f a p,
    or prove t is infinite and prove that the infinite predicate is in w*)
  Definition _bindpi A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B) :=
    fun (p : itree Void B -> Prop) (Hp : tau_invar Void B p) =>
      w (fun (t : itree Void A) => (exists a, is_val A a t /\ f a p Hp) \/ 
                                   (divergence t /\  p spin ))
  (bind_pred_tau_invar A B f p Hp).
(* replace   *)


  Lemma bindpi_monot : forall A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B),
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B (_bindpi A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *.
    set (fun t p0 Hp0 => (exists a, is_val A a t /\ f a p0 Hp0)\/ (divergence t /\ p spin))  as fp.
    enough (forall t, fp t p Hp -> fp t p' Hp').
    - eapply H with (p := fun t => fp t p Hp).
      + intros. subst. apply H3 in H4. 
        unfold fp in H4. destruct H4; auto.
        destruct H4. right. split; auto.
   + apply H2.
    - unfold fp. intros. destruct H3; auto. left.
      intros. destruct H3 as [a [Hvala Hfa] ].
      exists a. split; auto.
      eapply H0; eauto.
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


  Global Instance PureITreeSpecEq : EqM PureITreeSpec :=
    fun A w1 w2 => forall (p : itree Void A -> Prop) (Hp : tau_invar Void A p), proj1_sig w1 p Hp <-> proj1_sig w2 p Hp.


  Lemma ret_not_div : forall (A : Type) (E : Type -> Type) (a : A), ~ (@divergence E A (ret a)).
    Proof.
      intros. intro Hcontra. pinversion Hcontra.
    Qed.

  Lemma bindpi_retpi : forall A B (f : A -> PureITreeSpec B) (a : A), 
      bind (ret a) f ≈ f a.
    Proof.
      intros. split.
      - cbn. unfold _bindpi. unfold _retpi. intros. 
        destruct H.
        + destruct H as [a0 [Hvala0 Hfa0] ]. inversion Hvala0. subst. auto.
        + exfalso. destruct H. eapply ret_not_div. eauto. 
      - simpl. destruct (f a) as [fa Hfa] eqn : Heq. simpl. intros.
        left. exists a. split; auto.
        + constructor.
        + rewrite Heq. auto.
    Qed.

    
  Lemma retpi_bindpi : forall A (w : PureITreeSpec A), bind w (fun x => ret x) ≈ w.
  Proof.
    intros. destruct w as [ w Hw]. split.
    - intros. simpl in *. unfold _bindpi in H.
      unfold _retpi in H. simpl in H.
      eapply Hw.
      2: apply H.
      intros. destruct H0.
      + destruct H0 as [a [ Hvala Hpa]  ].
        induction Hvala; auto. apply Hp in IHHvala. auto.
      + destruct H0. (* this is proven by inf taus being obs equivalent, that should be provable  *) admit.
    - simpl. intros. unfold _bindpi.
      eapply Hw. 2: apply H. intros.
      destruct (is_val_or_div A i').
      + left. destruct H1 as [ a Ha ]. exists a. split; auto.
        unfold _retpi. eapply tau_invar_prop_subst; eauto.
        split. constructor. auto.
      + right. split; auto. (* same as the other unsolved case*)
   Admitted.    

  Lemma bindpi_bindpi : forall (A B C : Type) (w : PureITreeSpec A) 
                               (f : A -> PureITreeSpec B) (g : B -> PureITreeSpec C),
      bind (bind w f) g ≈ bind w (fun a => bind (f a) g).
    Proof.
      intros. destruct w as [w Hw]. split; simpl.
      - intros. eapply Hw; try apply H.
        intros. destruct H0; try destruct H0.
        + destruct H0. simpl in *.
          left. exists x. split; auto. unfold bindpi. destruct (f x) as [fx Hfx].
          simpl in *. unfold _bindpi.
          
          eapply Hfx; try apply H1.
          intros. destruct H2.
          * destruct H2 as [b [Hvalb Hgb ] ].
            left. exists b. auto.
          * destruct H2. right. split; auto.
        + unfold _bindpi in H.(* eapply Hw.

          destruct H1. simpl in *.
          * 
      *)

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
