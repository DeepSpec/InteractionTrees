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
     Dijkstra.DijkstraMonad
.

Import MonadNotation.
Local Open Scope monad.

Section Pure_Spec_Instance.
  
  Definition _Pure_Spec (A : Type) := (A -> Prop) -> Prop.
  
  Definition monotonicp {A} (w : _Pure_Spec A) :=
    forall (p p' : A -> Prop), (forall a, p a -> p' a) -> w p -> w p'.

  Definition Pure_Spec (A : Type) := 
    { w : _Pure_Spec A | monotonicp w }.

  Definition eqwp {A : Type} (w1 w2 : Pure_Spec A) :=
    forall p, proj1_sig w1 p <-> proj1_sig w2 p.

  Global Instance Pure_SpecEq : EqM Pure_Spec := @eqwp.

  Hint Unfold eqwp.

  Lemma eqwp_refl : forall A (w : Pure_Spec A), eqwp w w.
    Proof.
      destruct w. intuition.
    Qed.

  Lemma eqwp_sym : forall A (w1 w2 : Pure_Spec A), eqwp w1 w2 -> eqwp w2 w1.
    Proof.
      destruct w1. destruct w2. unfold eqwp in *. simpl. intuition; apply H; auto.
    Qed.

  Lemma eqwp_trans : forall A (w1 w2 w3 : Pure_Spec A), eqwp w1 w2 -> eqwp w2 w3 -> eqwp w1 w3.
    Proof.
      destruct w1. destruct w2. destruct w3. unfold eqwp in *. intuition.
      - apply H0. apply H. auto.
      - apply H. apply H0. auto.
    Qed.

  Definition _retp (A : Type) (a : A) := fun (p : A -> Prop) => p a.

  Hint Unfold _retp.
  Hint Unfold monotonicp.

  Lemma monot_retp : forall A (a : A), monotonicp (_retp A a).
    Proof.
      intuition.
    Qed.

  Definition _bindp (A B : Type) (w : _Pure_Spec A) (f : A -> _Pure_Spec B) :=
    fun p => w (fun a => f a p).

  Lemma monot_bindp : forall A B (w : _Pure_Spec A) (f : A -> _Pure_Spec B),
      monotonicp w -> (forall a, monotonicp (f a)) -> monotonicp (_bindp A B w f).
  Proof.
    unfold monotonicp in *. intuition. unfold _bindp in *. apply H with (p := (fun a => f a p) ); auto.
    intuition. apply H0 with (p := p); auto.
  Qed.

  Definition retp {A : Type} (a : A) : Pure_Spec A :=
    exist (@monotonicp A) (_retp A a) (monot_retp A a).

  Definition bindp {A B : Type} (w : Pure_Spec A) (f : A -> Pure_Spec B) : Pure_Spec B :=
    let '(exist _ w' Hw' ) := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist (@monotonicp B) (_bindp A B w' f') (monot_bindp A B w' f' Hw' Hf').

  Global Instance Pure_SpecM : Monad Pure_Spec :=
    {
      ret := @retp;
      bind := @bindp;
    }.

  Lemma bind_retp : forall A B (f : A -> Pure_Spec B) (a : A), 
      bindp (retp a) f ≈ f a.
  Proof.
    unfold eqm, Pure_SpecEq. intuition.
  Qed.

  Lemma ret_bindp : forall A (w : Pure_Spec A), bindp w retp ≈ w.
  Proof.
    destruct w as [w' Hw']. unfold eqm, Pure_SpecEq. simpl. split; intuition.
  Qed.

  Lemma bind_bindp : forall A B C (w : Pure_Spec A) (f : A -> Pure_Spec B) (g : B -> Pure_Spec C),
      bindp (bindp w f) g ≈ bindp w (fun a => bindp (f a) g).
  Proof.
    destruct w as [w' Hw']. unfold eqm, Pure_SpecEq, eqwp. simpl. intros; split; intuition.
    - unfold _retp, _bindp in *. unfold monotonicp in Hw'. eapply Hw'.
      2: apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *. unfold _bindp. auto.
    - unfold _retp, _bindp in *. eapply Hw'.
      2 : apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *. unfold _bindp in *.
      auto.
  Qed.

  Global Instance Pure_SpecLaws : MonadLaws Pure_Spec :=
    {
      bind_ret := bind_retp;
      ret_bind := ret_bindp;
      bind_bind := bind_bindp
    }.

  Definition lemPure {A : Type} (w1 w2 : Pure_Spec A) : Prop :=
    forall p, proj1_sig w2 p -> proj1_sig w1 p.

  Global Instance Pure_SpecOrderM : OrderM Pure_Spec := @lemPure.

  Global Instance Pure_SpecOrder : OrderedMonad Pure_Spec.
  Proof.
    unfold OrderedMonad. intros. unfold lem, Pure_SpecOrderM, lemPure in *.
    destruct w1 as [w1' Hw1']. destruct w2 as [w2' Hw2']. simpl in *. unfold _bindp in *.
    intuition. apply H. unfold monotonicp in Hw2'. eapply Hw2'; eauto; auto.
  Qed.


End Pure_Spec_Instance.

Section Pure_Spec_Obs.
  
  Definition Id (A : Type) := A.

  Definition retid {A : Type} a : A:= a.

  Definition bindid {A B : Type} (m : Id A) (f : A -> Id B) := f m.

  Instance IdMonad : Monad Id :=
    {
      ret := @retid;
      bind := @bindid;
    }.
  
  Instance EqId : EqM Id := fun A (a b : A) => a = b.
  Hint Unfold eqm.
  Hint Unfold EqId.
  Lemma bind_retid : forall A B (f : A -> Id B) (a : Id A), bindid a f ≈ f a.
    Proof.  auto. Qed.
  
  Lemma ret_bindid : forall A (a : Id A), bindid a retid ≈ a.
    Proof. auto. Qed.

  Lemma bind_bindid : forall A B C (a : Id A) (f : A -> Id B) (g : B -> Id C),
        bindid (bindid a f) g ≈ bindid a (fun a => bindid (f a) g).
    Proof. auto. Qed.

  Instance IdMonadLaws : MonadLaws Id :=
    {
      bind_ret := bind_retid;
      ret_bind := ret_bindid;
      bind_bind := bind_bindid;
    }.


  Definition _obsp (A : Type) (m : Id A) : _Pure_Spec A :=
    fun p => p m.

  Hint Unfold monotonicp.
  Hint Unfold _obsp.
  Lemma obsp_monot : forall A (m : Id A), monotonicp (_obsp A m).
    Proof. auto. Qed.

  Definition obsp (A : Type) (m : Id A) : Pure_Spec A :=
    exist _ (_obsp A m) (obsp_monot A m).

  Instance Id_EffectObs : EffectObs Id Pure_Spec := obsp.

  Lemma obsp_pres_ret : forall A (a : A), obs A (ret a) ≈ ret a.
    Proof.
      unfold eqm, Pure_SpecEq, eqwp. simpl. split; intuition.
    Qed.

  Lemma obsp_pres_bind : forall A B (m : Id A) (f : A -> Id B),
        obs B (bind m f) ≈ bind (obs A m) (fun a => obs B (f a)).
    Proof.
      unfold eqm, Pure_SpecEq, eqwp. simpl; split; intuition.
    Qed.

  (*Must be on some weird case, figure out later, for now just directly write hte lemmas*)
  Program Instance Pure_MonadMorph : 
    MonadMorphism Id Pure_Spec Id_EffectObs :=
    {
      ret_pres := obsp_pres_ret;
      bind_pres := obsp_pres_bind
    }.
  
  


End Pure_Spec_Obs.

Section State.
  Context (S : Type).
Section State_Spec_Instance.
  

  Definition monotonic {A} (w : ((A * S) -> Prop) -> S -> Prop):= 
    forall (p p' : (A * S) -> Prop) s,
    (forall a s', p (a,s') -> p' (a,s')) -> w p s -> w p' s.

  Definition _State_Spec (A : Type) := ((A * S) -> Prop) -> (S -> Prop).

  Definition State_Spec (A : Type) :=
    { w : _State_Spec A | monotonic w }.

  Definition eqw {A : Type} (w1 w2 : State_Spec A) :=
    forall p s, proj1_sig w1 p s <-> proj1_sig w2 p s. 

  Global Instance State_SpecEq : EqM State_Spec := @eqw.

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

  Definition _retst (A : Type) (a : A) : _State_Spec A := fun p s => p (a,s).

  Lemma monot_retst : forall A (a: A), monotonic (_retst A a).
  Proof.
    intros. unfold monotonic, _retst. intros. apply H. auto.
  Qed.

  Definition retst {A : Type} (a : A) := exist (@monotonic A) (_retst A a) (monot_retst A a).

  Definition _bindst (A B : Type) (w : _State_Spec A) (f : A -> _State_Spec B) : _State_Spec B :=
    fun p s => w (fun '(a,s') => f a p s') s.

  Lemma monot_bindst : forall A B (f : A -> _State_Spec B) (w : _State_Spec A) 
          (Hw : monotonic w) (Hf : forall a, monotonic (f a) ), monotonic  (_bindst A B w f).
  Proof.
    intros. unfold monotonic, _bindst in *. intuition. 
    eapply Hw; eauto. intros. apply Hf with (p := p); auto.
  Qed.

  Definition bindst {A B : Type} (w : State_Spec A) (f : A -> State_Spec B) : State_Spec B :=
    let '(exist _ w' Hw' ) := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' : forall a, monotonic (f' a) := fun a => proj2_sig (f a) in
    exist (@monotonic B) (_bindst A B w' f') (monot_bindst A B f' w' Hw' Hf').

  Global Instance State_SpecM : Monad State_Spec :=
    {
      ret := @retst;
      bind := @bindst;
    }.

  Lemma bind_retst : forall A B (f: A -> State_Spec B) (a : A), bindst (retst a) f ≈ f a.
  Proof. 
    unfold eqm, State_SpecEq. intuition. 
  Qed.

  Hint Unfold _retst.
  Hint Unfold _bindst.

  Lemma ret_bindst : forall A (w : State_Spec A), bindst w retst ≈ w.
  Proof.
    destruct w as [w' Hw'].
    unfold eqw. simpl. intros. split; intuition.
    -  simpl in *. unfold monotonic in Hw'. unfold _retst, _bindst in H.
       auto. apply Hw' with (p := fun '(a,s') => p (a,s')); auto.
    - unfold _retst, _bindst. apply Hw' with (p := p); auto.
  Qed.

  Lemma bind_bindst : forall A B C (w : State_Spec A) (f : A -> State_Spec B) (g : B -> State_Spec C),
      bindst (bindst w f) g ≈ bindst w (fun a => bindst (f a) g).
  Proof.
    destruct w as [w' Hw']. unfold eqw. simpl. intros; split; intuition.
    - unfold _retst, _bindst in *. unfold monotonic in Hw'. eapply Hw'.
      2: apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *.
      unfold _bindst. auto.
    - unfold _retst, _bindst in *. unfold monotonic in Hw'. eapply Hw'.
      2: apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *.
      unfold _bindst in H0. auto.
  Qed.

  Global Instance State_SpecMLaws : MonadLaws State_Spec:=
    {
      bind_ret := bind_retst;
      ret_bind := ret_bindst;
      bind_bind := bind_bindst
   }.
    

  Definition lemSt {A : Type} (w1 w2 : State_Spec A) : Prop :=
    forall p s, proj1_sig w2 p s -> proj1_sig w1 p s.

  Global Instance State_SpecOrderM : OrderM State_Spec := @lemSt.

  Global Instance State_SpecOrder : OrderedMonad State_Spec.
  Proof. 
    unfold OrderedMonad.
    intros A B w1 w2 f1 f2 Hw Hf. unfold lem in *. unfold State_SpecOrderM, lemSt in *.
    destruct w1 as [w1' Hw1']. destruct w2 as [w2' Hw2']. simpl in *. 
    intuition. apply Hw. 
    cbv in H. unfold monotonic in Hw2'. eapply Hw2'; eauto; auto.
  Qed.

End State_Spec_Instance.

Section State_Monad.

  Definition State A := S -> (A * S).
  
  Definition retstm (A : Type) (a : A) : State A:= fun s => (a,s).

  Definition bindstm (A B : Type) (m : State A) (f : A -> State B) :=
    fun s => let '(a,s') := (m s) in
             f a s'.

  Hint Unfold retstm.
  Hint Unfold bindstm.

  Global Instance StateM : Monad State :=
    {
      ret := retstm;
      bind := bindstm;
    }.

  Global Instance StateEq : EqM State :=
    fun (A : Type) (m1 m2 : State A) =>
      forall s, m1 s = m2 s.

  Global Program Instance StateM_Laws : MonadLaws State.
  Next Obligation.
    Proof.
      unfold retstm, bindstm, eqm, StateEq. auto.
    Qed.
  Next Obligation.
    Proof.
      unfold bindstm, eqm, StateEq. intuition.
      destruct (x s). auto.
    Qed.
  Next Obligation.
    Proof.
      unfold bindstm, eqm, StateEq. intuition.
      destruct (x s). auto.
    Qed.

End State_Monad.

Section State_Spec_Obs.

  Definition _obsst (A : Type) (m : State A ) : _State_Spec A :=
    fun p s => p (m s).

  Hint Unfold _obsst.

  Lemma obsst_monot : forall A (m : State A),
      monotonic ( _obsst A m).
    Proof.
      unfold monotonic, _obsst. intuition. destruct (m s).
      eapply H; auto.
    Qed.

  Definition obsst (A : Type) (m : State A) : State_Spec A :=
    exist _ (_obsst A m) (obsst_monot A m).

  Global Instance State_Effect_Obs : EffectObs State State_Spec := obsst.

  Lemma obsst_pres_ret : forall A (a : A), obsst A (ret a) ≈ ret a.
    Proof.
      unfold eqm, State_SpecEq, eqw. simpl. intuition.
    Qed.

  Lemma obsst_pres_bind : forall A B (m : State A) (f : A -> State B), 
        obsst B (bind m f) ≈ bind (obsst A m) (fun a => obsst B (f a)).
    Proof.
      unfold eqm, State_SpecEq, eqw. simpl. intuition.
      - unfold _bindst, _obsst in *. unfold bindstm in *. destruct (m s). auto.
      - unfold _bindst, _obsst in *. unfold bindstm. destruct (m s). auto.
    Qed.


  Global Instance StateMonadMorph : MonadMorphism State State_Spec State_Effect_Obs :=
    {
      ret_pres := obsst_pres_ret;
      bind_pres := obsst_pres_bind
    }.
  

End State_Spec_Obs.

End State.
