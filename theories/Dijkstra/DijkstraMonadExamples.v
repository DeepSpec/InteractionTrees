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
     Events.State
.

Import MonadNotation.
Local Open Scope monad.


(** * Pure Specification Monad *)

(**   A specification monad on the identity monad.   

      Also commonly denoted as W^{Pure}.
*)

Section PureSpecInstance.

  (** ** Monotonic predicate transformers 

      Due to the *ordered* nature of specification monads, we focus on 
      ordered specifications. *)

  Definition _PureSpec (A : Type) := (A -> Prop) -> Prop.
  
  Definition monotonicp {A} (w : _PureSpec A) :=
    forall (p p' : A -> Prop), (forall a, p a -> p' a) -> w p -> w p'.

  Definition PureSpec (A : Type) := 
    { w : _PureSpec A | monotonicp w }.


  (** ** Equivalent Specifications

      Two specifications are equivalent iff the underlying predicates
      imply each other. *)
  
  Definition eqwp {A : Type} (w1 w2 : PureSpec A) :=
    forall p, proj1_sig w1 p <-> proj1_sig w2 p.

  Global Instance PureSpecEq : EqM PureSpec := @eqwp.

  Hint Unfold eqwp.

  Lemma eqwp_refl : forall A (w : PureSpec A), eqwp w w.
    Proof.
      destruct w. intuition.
    Qed.

  Lemma eqwp_sym : forall A (w1 w2 : PureSpec A), eqwp w1 w2 -> eqwp w2 w1.
    Proof.
      destruct w1. destruct w2. unfold eqwp in *. simpl. intuition; apply H; auto.
    Qed.

  Lemma eqwp_trans : forall A (w1 w2 w3 : PureSpec A), eqwp w1 w2 -> eqwp w2 w3 -> eqwp w1 w3.
    Proof.
      destruct w1. destruct w2. destruct w3. unfold eqwp in *. intuition.
      - apply H0. apply H. auto.
      - apply H. apply H0. auto.
    Qed.

  (** ** Specification Monad 
      
      This is a specification monad, i.e. we can define their 
      monotonic return and bind. *)
   
  Definition _retp (A : Type) (a : A) := fun (p : A -> Prop) => p a.

  Hint Unfold _retp.
  Hint Unfold monotonicp.

  Lemma monot_retp : forall A (a : A), monotonicp (_retp A a).
    Proof.
      intuition.
    Qed.

  Definition _bindp (A B : Type) (w : _PureSpec A) (f : A -> _PureSpec B) :=
    fun p => w (fun a => f a p).

  Lemma monot_bindp : forall A B (w : _PureSpec A) (f : A -> _PureSpec B),
      monotonicp w -> (forall a, monotonicp (f a)) -> monotonicp (_bindp A B w f).
  Proof.
    unfold monotonicp in *. intuition. unfold _bindp in *. apply H with (p := (fun a => f a p) ); auto.
    intuition. apply H0 with (p := p); auto.
  Qed.

  Definition retp {A : Type} (a : A) : PureSpec A :=
    exist (@monotonicp A) (_retp A a) (monot_retp A a).

  Definition bindp {A B : Type} (w : PureSpec A) (f : A -> PureSpec B) : PureSpec B :=
    let '(exist _ w' Hw' ) := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist (@monotonicp B) (_bindp A B w' f') (monot_bindp A B w' f' Hw' Hf').

  Global Instance PureSpecM : Monad PureSpec :=
    {
      ret := @retp;
      bind := @bindp;
    }.

  (** ** Monad Laws *)

  Lemma bind_retp : forall A B (f : A -> PureSpec B) (a : A), 
      bindp (retp a) f ≈ f a.
  Proof.
    unfold eqm, PureSpecEq. intuition.
  Qed.

  Lemma ret_bindp : forall A (w : PureSpec A), bindp w retp ≈ w.
  Proof.
    destruct w as [w' Hw']. unfold eqm, PureSpecEq. simpl. split; intuition.
  Qed.

  Lemma bind_bindp : forall A B C (w : PureSpec A) (f : A -> PureSpec B) (g : B -> PureSpec C),
      bindp (bindp w f) g ≈ bindp w (fun a => bindp (f a) g).
  Proof.
    destruct w as [w' Hw']. unfold eqm, PureSpecEq, eqwp. simpl. intros; split; intuition.
    - unfold _retp, _bindp in *. unfold monotonicp in Hw'. eapply Hw'.
      2: apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *. unfold _bindp. auto.
    - unfold _retp, _bindp in *. eapply Hw'.
      2 : apply H. intuition. destruct (f a) as [fa Hfa]. simpl in *. unfold _bindp in *.
      auto.
  Qed.

  (** ** Ordered Monad

      A specification monad W is *ordered*, where W A is equipped with a preorder
      for each type A, and the bind is monotonic in both arguments. *)

  Global Instance PureSpecLaws : MonadLaws PureSpec :=
    {
      bind_ret := bind_retp;
      ret_bind := ret_bindp;
      bind_bind := bind_bindp
    }.

  Definition lemPure {A : Type} (w1 w2 : PureSpec A) : Prop :=
    forall p, proj1_sig w2 p -> proj1_sig w1 p.

  Global Instance Pure_SpecOrderM : OrderM PureSpec := @lemPure.

  Global Instance Pure_SpecOrder : OrderedMonad PureSpec.
  Proof.
    unfold OrderedMonad. intros. unfold lem, Pure_SpecOrderM, lemPure in *.
    destruct w1 as [w1' Hw1']. destruct w2 as [w2' Hw2']. simpl in *. unfold _bindp in *.
    intuition. apply H. unfold monotonicp in Hw2'. eapply Hw2'; eauto; auto.
  Qed.

End PureSpecInstance.


(** * Effect Observation *)


(** ** Effect Observation on the Identity Monad *)

Section PureSpecObs.

  (** ** Identity monad *)

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

  (** ** Effect Observation *)
  
  Definition _obsp (A : Type) (m : Id A) : _PureSpec A :=
    fun p => p m.

  Hint Unfold monotonicp.
  Hint Unfold _obsp.
  Lemma obsp_monot : forall A (m : Id A), monotonicp (_obsp A m).
    Proof. auto. Qed.

  Definition obsp (A : Type) (m : Id A) : PureSpec A :=
    exist _ (_obsp A m) (obsp_monot A m).

  Instance IdEffectObs : EffectObs Id PureSpec := obsp.

  Lemma obsp_pres_ret : forall A (a : A), obs A (ret a) ≈ ret a.
    Proof.
      unfold eqm, PureSpecEq, eqwp. simpl. split; intuition.
    Qed.

  Lemma obsp_pres_bind : forall A B (m : Id A) (f : A -> Id B),
        obs B (bind m f) ≈ bind (obs A m) (fun a => obs B (f a)).
    Proof.
      unfold eqm, PureSpecEq, eqwp. simpl; split; intuition.
    Qed.

  Program Instance PureMonadMorph : 
    MonadMorphism Id PureSpec IdEffectObs :=
    {
      ret_pres := obsp_pres_ret;
      bind_pres := obsp_pres_bind
    }.
  
End PureSpecObs.


(** * Monad Transformers 

    For T(Id), a monad obtained by the application of a monad transformer 
    to the identity monad, we can build a canonical specification monad and 
    a canonical effect observation on it. 
 *)

Section PureTSpecObs.

  (**  T(Id). *)

  Definition idT (m: Type -> Type) : Type -> Type :=
    m.

 Instance Monad_idT {m} {Fm: Monad m} : Monad (idT m)
    := {|
      ret  := @ret m _   
    ; bind c k := @bind m _ c k
    |}.
  
End PureTSpecObs.  


(** * Specification of State *)

Section State.
  Context (S : Type).
Section StateSpecInstance.

  Definition monotonic {A} (w : ((A * S) -> Prop) -> S -> Prop):= 
    forall (p p' : (A * S) -> Prop) s,
    (forall a s', p (a,s') -> p' (a,s')) -> w p s -> w p' s.

  Definition _StateSpec (A : Type) := ((A * S) -> Prop) -> (S -> Prop).

  Definition StateSpec (A : Type) :=
    { w : _StateSpec A | monotonic w }.

  Definition eqw {A : Type} (w1 w2 : StateSpec A) :=
    forall p s, proj1_sig w1 p s <-> proj1_sig w2 p s. 

  Global Instance StateSpecEq : EqM StateSpec := @eqw.

  Hint Unfold eqw.

  Lemma eqw_refl : forall A (w : StateSpec A), eqw w w.
  Proof.
    destruct w. intuition.
  Qed.

  Lemma eqw_sym : forall A (w1 w2 : StateSpec A), eqw w1 w2 -> eqw w2 w1.
  Proof.
    destruct w1. destruct w2. intuition. unfold eqw in *. simpl in *. intuition; apply H; auto.
  Qed.

  Lemma eqw_trans : forall A (w1 w2 w3 : StateSpec A), eqw w1 w2 -> eqw w2 w3 -> eqw w1 w3.
  Proof.
    destruct w1. destruct w2. destruct w3. intuition. unfold eqw in *; intuition.
    - apply H0. apply H. auto.
    - apply H. apply H0. auto.
  Qed.

  Definition _retst (A : Type) (a : A) : _StateSpec A := fun p s => p (a,s).

  Lemma monot_retst : forall A (a: A), monotonic (_retst A a).
  Proof.
    intros. unfold monotonic, _retst. intros. apply H. auto.
  Qed.

  Definition retst {A : Type} (a : A) := exist (@monotonic A) (_retst A a) (monot_retst A a).

  Definition _bindst (A B : Type) (w : _StateSpec A) (f : A -> _StateSpec B) : _StateSpec B :=
    fun p s => w (fun '(a,s') => f a p s') s.

  Lemma monot_bindst : forall A B (f : A -> _StateSpec B) (w : _StateSpec A) 
          (Hw : monotonic w) (Hf : forall a, monotonic (f a) ), monotonic  (_bindst A B w f).
  Proof.
    intros. unfold monotonic, _bindst in *. intuition. 
    eapply Hw; eauto. intros. apply Hf with (p := p); auto.
  Qed.

  Definition bindst {A B : Type} (w : StateSpec A) (f : A -> StateSpec B) : StateSpec B :=
    let '(exist _ w' Hw' ) := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' : forall a, monotonic (f' a) := fun a => proj2_sig (f a) in
    exist (@monotonic B) (_bindst A B w' f') (monot_bindst A B f' w' Hw' Hf').

  Global Instance StateSpecM : Monad StateSpec :=
    {
      ret := @retst;
      bind := @bindst;
    }.

  Lemma bind_retst : forall A B (f: A -> StateSpec B) (a : A), bindst (retst a) f ≈ f a.
  Proof. 
    unfold eqm, StateSpecEq. intuition. 
  Qed.

  Hint Unfold _retst.
  Hint Unfold _bindst.

  Lemma ret_bindst : forall A (w : StateSpec A), bindst w retst ≈ w.
  Proof.
    destruct w as [w' Hw'].
    unfold eqw. simpl. intros. split; intuition.
    -  simpl in *. unfold monotonic in Hw'. unfold _retst, _bindst in H.
       auto. apply Hw' with (p := fun '(a,s') => p (a,s')); auto.
    - unfold _retst, _bindst. apply Hw' with (p := p); auto.
  Qed.

  Lemma bind_bindst : forall A B C (w : StateSpec A) (f : A -> StateSpec B) (g : B -> StateSpec C),
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

  Global Instance StateSpecMLaws : MonadLaws StateSpec:=
    {
      bind_ret := bind_retst;
      ret_bind := ret_bindst;
      bind_bind := bind_bindst
   }.
    
  Definition lemSt {A : Type} (w1 w2 : StateSpec A) : Prop :=
    forall p s, proj1_sig w2 p s -> proj1_sig w1 p s.

  Global Instance StateSpecOrderM : OrderM StateSpec := @lemSt.

  Global Instance StateSpecOrder : OrderedMonad StateSpec.
  Proof. 
    unfold OrderedMonad.
    intros A B w1 w2 f1 f2 Hw Hf. unfold lem in *. unfold StateSpecOrderM, lemSt in *.
    destruct w1 as [w1' Hw1']. destruct w2 as [w2' Hw2']. simpl in *. 
    intuition. apply Hw. 
    cbv in H. unfold monotonic in Hw2'. eapply Hw2'; eauto; auto.
  Qed.

  Definition _encode A (post : A * S -> Prop) (pre : S -> Prop) : _StateSpec A :=
    fun p s => pre s /\ forall r, post r -> p r.

  Lemma encode_monot : forall A post pre, monotonic (_encode A post pre).
    Proof.
      unfold monotonic, _encode. intros. destruct H0. split; auto. intros.
      destruct r. apply H. auto.
    Qed.

  Definition encode A (post : A * S -> Prop) (pre : S -> Prop) : StateSpec A :=
    exist _ (_encode A post pre) (encode_monot A post pre).

End StateSpecInstance.


(** * Simple State Monad *)

Section StateMonad.

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

  Global Program Instance StateMLaws : MonadLaws State.
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

   Definition get : State S := fun s => (s,s).

   Definition put (s : S) : State unit := fun s' => (tt,s).

End StateMonad.


(** * State Effect Observation *)

Section StateSpecObs.

  Definition _obsst (A : Type) (m : State A ) : _StateSpec A :=
    fun p s => p (m s).

  Hint Unfold _obsst.

  Lemma obsst_monot : forall A (m : State A),
      monotonic ( _obsst A m).
    Proof.
      unfold monotonic, _obsst. intuition. destruct (m s).
      eapply H; auto.
    Qed.

  Definition obsst (A : Type) (m : State A) : StateSpec A :=
    exist _ (_obsst A m) (obsst_monot A m).

  Global Instance StateEffectObs : EffectObs State StateSpec := obsst.

  Lemma obsst_pres_ret : forall A (a : A), obsst A (ret a) ≈ ret a.
    Proof.
      unfold eqm, StateSpecEq, eqw. simpl. intuition.
    Qed.

  Lemma obsst_pres_bind : forall A B (m : State A) (f : A -> State B), 
        obsst B (bind m f) ≈ bind (obsst A m) (fun a => obsst B (f a)).
    Proof.
      unfold eqm, StateSpecEq, eqw. simpl. intuition.
      - unfold _bindst, _obsst in *. unfold bindstm in *. destruct (m s). auto.
      - unfold _bindst, _obsst in *. unfold bindstm. destruct (m s). auto.
    Qed.


  Global Instance StateMonadMorph : MonadMorphism State StateSpec StateEffectObs :=
    {
      ret_pres := obsst_pres_ret;
      bind_pres := obsst_pres_bind
    }.
  
  Definition ST (A : Type) (w : StateSpec A) := DijkstraMonad State StateSpec StateEffectObs A w.

  Definition STProp (A : Type) (w : StateSpec A) := DijkstraProp State StateSpec StateEffectObs A w.

End StateSpecObs.

End State.


(** * State Example *)

Section StateExample.
  Definition StateNat A := State nat A.

  Definition inc : State nat unit := bind (get nat) (fun n => put _ (S n)).

  Definition winc := encode _ unit (fun '(p,s) => s > 0) (fun s => True).

  Lemma ex : STProp nat unit winc inc.
    Proof.
      cbv. intros. destruct H as [ _ H]. apply H. induction s; auto.
    Qed.
End StateExample.


(** * Free Monad *)

Section Free.

  Inductive Free (E : Type -> Type) (A : Type) :=
    | Ret (a : A)
    | Vis {B} (ev : E B) (k : B -> Free E A).


 Definition refr := Ret.

 Definition bindfr (E : Type -> Type) (A B : Type) (m : Free E A) (f : A -> Free E B) : (Free E B) :=
   (fix _bind m :=
   match m with
     | Ret _ _ a => f a
     | Vis _ _ ev k => Vis _  _ ev (fun b => _bind (k b) ) end ) m.

 Global Instance FreeMonad E: Monad (Free E) :=
   {
     ret := refr E;
     bind := bindfr E;
   }.

 Definition interpfr (E : Type -> Type) (M : Type -> Type) {mon : Monad M } (A : Type) (i : E ~> M) :
  Free E A ->  M A :=
   fix _interp m :=
     match m with
       | Ret _ _ a => ret a
       | Vis _ _ ev k => bind (i _ ev) (fun b => _interp (k b)) end.

 Definition StateHSpec S : (stateE S) ~> StateSpec S :=
   fun _ ev =>
     match ev with
       | Get _ => obs _ (get S)
       | Put _ s => obs _ (put S s) end.

 Definition stateH S : (stateE S) ~> State S :=
   fun _ ev =>
     match ev with
       | Get _ => get S
       | Put _ s => put S s end.



 (** * Examples of Effect Observations *)

 (** ** Nondeterminism *) 
       
 Inductive NondetE : Type -> Type :=
   | Choose : NondetE nat.

 (* Angelic determinism *)
 Definition _chooseA (S : Type) : _StateSpec S nat :=
   fun p s => forall (n : nat), p (n,s) .

 (* Demonic determinism *)
 Definition _chooseD (S : Type) : _StateSpec S nat :=
   fun p s => exists (n : nat), p (n, s) . 

 Lemma chooseA_monot : forall S, monotonic S (_chooseA S).
 Proof.
   unfold monotonic. intros. cbv. intros. unfold _chooseA in *. auto.
 Qed.

 Lemma chooseD_monot : forall S, monotonic S (_chooseD S).
 Proof.
   unfold monotonic. intros. cbv. intros. unfold _chooseD in *. auto.
   destruct H0. 
   apply H in H0. exists x. apply H0. 
 Qed.

 Definition chooseD (S : Type) : StateSpec S nat :=
   exist _ (_chooseD S) (chooseD_monot S).

 Definition chooseA (S : Type) : StateSpec S nat :=
   exist _ (_chooseA S) (chooseA_monot S). 

 Definition NondetHSpecD S : NondetE ~> StateSpec S :=
   fun _ ev => 
     match ev with | Choose => chooseD S end.

 Definition NondetHSpecA S : NondetE ~> StateSpec S :=
   fun _ ev =>
     match ev with | Choose => chooseA S end.

 Definition interpstop S A (m : Free (stateE S) A) : StateSpec S A :=
   interpfr (stateE S) (StateSpec S) A (StateHSpec S) m.
 
End Free. 
