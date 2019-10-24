From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Data.Monads.StateMonad
     Data.Monads.ReaderMonad
     Data.Monads.OptionMonad
     Data.Monads.EitherMonad
     .
From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function
     Basics.MonadTheory
.


Import MonadNotation.
Local Open Scope monad.
Axiom proof_irrel : forall (P : Prop) (H1 H2 : P), H1 = H2.

Class OrderM (M : Type -> Type) :=
  lem : forall A, M A -> M A -> Prop.

Section OrderedMonad.
  Context (W : Type -> Type).
  Context (Eq : EqM W).
  Context {MonadW : Monad W}.
  Context {MonadLawsW : MonadLaws W}.
  Context {OrderM : OrderM W}.

   
  Class OrderedMonad :=
    monot : forall A B w1 w2 f1 f2, lem A w1 w2 -> (forall a, lem B (f1 a) (f2 a) ) ->
                              lem B (bind w1 f1) (bind w2 f2).

End OrderedMonad.

Section Pure_Spec_Instance.
  
  Definition _Pure_Spec (A : Type) := (A -> Prop) -> Prop.
  
  Definition monotonicp {A} (w : _Pure_Spec A) :=
    forall (p p' : A -> Prop), (forall a, p a -> p' a) -> w p -> w p'.

  Definition Pure_Spec (A : Type) := 
    { w : _Pure_Spec A | monotonicp w }.

  Definition eqwp {A : Type} (w1 w2 : Pure_Spec A) :=
    forall p, proj1_sig w1 p <-> proj1_sig w2 p.

  Instance Pure_SpecEq : EqM Pure_Spec := @eqwp.

  Hint Unfold eqwp.

  Lemma eqwp_refl : forall A (w : Pure_Spec A), eqwp w w.
    Proof.
      destruct w. intuition.
    Qed.

  Lemma eqwp_sym : forall A (w1 w2 : Pure_Spec A), eqwp w1 w2 -> eqwp w2 w1.
    Proof.
      destruct w1. destruct w2. unfold eqwp in *. simpl. intuition; apply H; auto.
    Qed.

End Pure_Spec_Instance.

Section State_Spec_Instance.
  Context (S : Type).

  Definition monotonic {A} (w : ((A * S) -> Prop) -> S -> Prop):= 
    forall (p p' : (A * S) -> Prop) s,
    (forall a s', p (a,s') -> p' (a,s')) -> w p s -> w p' s.

  Definition _State_Spec (A : Type) := ((A * S) -> Prop) -> (S -> Prop).

  Definition State_Spec (A : Type) :=
    { w : _State_Spec A | monotonic w }.

  Definition eqw {A : Type} (w1 w2 : State_Spec A) :=
    forall p s, proj1_sig w1 p s <-> proj1_sig w2 p s. 

  Instance State_SpecEq : EqM State_Spec := @eqw.

  Hint Unfold eqw.

  Lemma eqw_refl : forall A (w : State_Spec A), eqw w w.
  Proof.
    destruct w. intuition.
  Qed.

  Lemma eqw_sym : forall A (w1 w2 : State_Spec A), eqw w1 w2 -> eqw w2 w1.
  Proof.
    destruct w1. destruct w2. intuition. unfold eqw in *. simpl in *. intuition; apply H; auto.
  Qed.

  Lemma eqw_trans : forall A (w1 w2 w3 : State_Spec A), eqw w1 w2 -> eqw w2 w3 -> eqw w1 w3.
  Proof.
    destruct w1. destruct w2. destruct w3. intuition. unfold eqw in *; intuition.
    - apply H0. apply H. auto.
    - apply H. apply H0. auto.
  Qed.

  Definition _ret (A : Type) (a : A) : _State_Spec A := fun p s => p (a,s).

  Lemma monot_ret : forall A (a: A), monotonic (_ret A a).
  Proof.
    intros. unfold monotonic, _ret. intros. apply H. auto.
  Qed.

  Definition ret {A : Type} (a : A) := exist (@monotonic A) (_ret A a) (monot_ret A a).

  Definition _bind (A B : Type) (w : _State_Spec A) (f : A -> _State_Spec B) : _State_Spec B :=
    fun p s => w (fun '(a,s') => f a p s') s.

  Lemma monot_bind : forall A B (f : A -> _State_Spec B) (w : _State_Spec A) 
          (Hw : monotonic w) (Hf : forall a, monotonic (f a) ), monotonic  (_bind A B w f).
  Proof.
    intros. unfold monotonic, _bind in *. intuition. apply Hw with (p := (fun '(a,s') => f a p s')); auto.
    intros. apply Hf with (p := p); auto.
  Qed.

  Definition bind {A B : Type} (w : State_Spec A) (f : A -> State_Spec B) : State_Spec B :=
    let '(exist _ w' Hw' ) := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' : forall a, monotonic (f' a) := fun a => proj2_sig (f a) in
    exist (@monotonic B) (_bind A B w' f') (monot_bind A B f' w' Hw' Hf').

  Instance State_SpecM : Monad State_Spec :=
    {
      ret := @ret;
      bind := @bind;
    }.

  Lemma bind_ret : forall A B (f: A -> State_Spec B) (a : A), bind (ret a) f ≈ f a.
  Proof. 
    unfold eqm, State_SpecEq. intuition. 
  Qed.

  Hint Unfold _ret.
  Hint Unfold _bind.

  Lemma ret_bind : forall A (w : State_Spec A), bind w ret ≈ w.
  Proof.
    destruct w as [w' Hw'].
    unfold eqw. simpl. intros. split; intuition.
    -  simpl in *. unfold monotonic in Hw'. unfold _ret, _bind in H.
       auto. apply Hw' with (p := fun '(a,s') => p (a,s')); auto.
    - unfold _ret, _bind. apply Hw' with (p := p); auto.
  Qed.

  Lemma bind_bind : forall A B C (w : State_Spec A) (f : A -> State_Spec B) (g : B -> State_Spec C),
      bind (bind w f) g ≈ bind w (fun a => bind (f a) g).
  Proof.
    destruct w as [w' Hw']. unfold eqw. simpl. intros; split; intuition.
    - unfold _ret, _bind in *. unfold monotonic in Hw'. eapply Hw'.
      2: apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *.
      unfold _bind. auto.
    - unfold _ret, _bind in *. unfold monotonic in Hw'. eapply Hw'.
      2: apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *.
      unfold _bind in H0. auto.
  Qed.

  Instance State_SpecMLaws : MonadLaws State_Spec:=
    {
      bind_ret := bind_ret;
      ret_bind := ret_bind;
      bind_bind := bind_bind
   }.
    

  Definition lemSt {A : Type} (w1 w2 : State_Spec A) : Prop :=
    forall p s, proj1_sig w2 p s -> proj1_sig w1 p s.

  Instance State_SpecOrderM : OrderM State_Spec := @lemSt.

  Instance State_SpecOrder : OrderedMonad State_Spec.
  Proof. 
    unfold OrderedMonad.
    intros A B w1 w2 f1 f2 Hw Hf. unfold lem in *. unfold State_SpecOrderM, lemSt in *.
    destruct w1 as [w1' Hw1']. destruct w2 as [w2' Hw2']. simpl in *. 
    intuition. apply Hw. 
    cbv in H. unfold monotonic in Hw2'. eapply Hw2'; eauto; auto.
  Qed.

End State_Spec_Instance.



