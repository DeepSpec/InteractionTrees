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
     Core.Divergence
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

CoFixpoint spin {E: Type -> Type} {A : Type}  : itree E A := Tau spin.

Lemma spin_div : forall E A, @divergence E A spin.
Proof.
  intros. pcofix CIH. pfold. unfold divergence_. 
  cbn. constructor. right. auto.
Qed.

(*this implies that if a spec w accepts spin, then bind w f should too?   *)
Lemma spin_bind : forall (E : Type -> Type) (A B : Type) (f : A -> itree E B), spin ≈ bind spin f.
Proof.
  intros. pcofix CIH. pfold. unfold bind. simpl. red.
  cbn. constructor. right. auto.
Qed.

Inductive Void : Type -> Type := .
Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).
(* maybe  *)
Inductive resp_euttF  {E : Type -> Type} {A : Type} (F : (itree E A -> Prop) -> Prop)  (P : itree E A -> Prop): Prop :=
  resp_eutt_intro (t1 t2 : itree E A) (Heutt : t1 ≈ t2) (Hiff : P t1 <-> P t2).

Hint Constructors resp_euttF.
                  
Definition resp_eutt_ {E A} sim :=
  fun P => @resp_euttF E A sim P.

Hint Unfold resp_eutt_.

Lemma resp_euttF_mono {E A} sim sim' P (IN : resp_euttF sim P) (LE : sim <1= sim') :
  @resp_euttF E A sim' P.
Proof.
  induction IN; eauto.
Qed.

Lemma resp_euttF_mono' {E A} : monotone1 (@resp_euttF E A).
Proof.
  unfold monotone1. intros.
  eapply resp_euttF_mono; eauto.
Qed.

Hint Resolve resp_euttF_mono' : paco.

Definition resp_eutt' {E A} := paco1 (@resp_euttF E A) bot1.

Definition resp_eutt (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
  forall (t1 t2 : itree E A), t1 ≈ t2 -> (P t1 <-> P t2).

Lemma tau_invar_resp_eutt1: forall (E : Type -> Type) (A : Type) (P : itree E A -> Prop),
                                 (forall t1 t2, t1 ≈ t2 ->(P t1 <-> P t2)) -> tau_invar E A P.
  Proof.
    intros. unfold tau_invar. split; intros;
    eapply H; try eassumption; rewrite tau_eutt; reflexivity.
  Qed.
(* not sure that did anything
Lemma tau_invar_resp_eutt2_aux : forall (A : Type) (P : itree Void A -> Prop),
      tau_invar Void A P -> resp_eutt' P.
  Proof.
    intros A P HP. unfold tau_invar in *.
    pcofix CIH. pfold. 
    constructor.
    revert H t1 t2.
    (*pcofix CIH.
    split.
    -*)

  Admitted.
*)
Ltac inv_div_ret := match goal with [ H : divergenceF _ (RetF _) |- _  ] => inversion H end.
Lemma div_ret_eutt : forall (E : Type -> Type) (A : Type) (t: itree E A) (a : A),
      divergence t -> ~(t ≈ ret a).
  Proof.
    intros. intros HContra. rewrite HContra in H. pinversion H.
  Qed.  

Lemma ret_eutt_div : forall (E : Type -> Type) (A : Type) (t : itree E A) (a : A),
      t ≈ ret a -> ~ (divergence t).
  Proof.
    intros. intros HContra. rewrite H in HContra. pinversion HContra.
  Qed.

Lemma div_spin_eutt : forall (A : Type) (t : itree Void A), divergence t -> t ≈ spin.
Proof.
  intros A. pcofix CIH. intros. pfold. red. cbn.
  destruct (observe t) eqn : Heqt.
  - specialize (itree_eta t) as H. rewrite Heqt in H. rewrite H in H0. pinversion H0.
  - constructor. right. apply CIH. specialize (itree_eta t) as H. rewrite Heqt in H.
    assert (t ≈ Tau t0).
    + rewrite H. reflexivity.
    + rewrite <- tau_eutt. rewrite <- H1. auto.
  - destruct e.
Qed.

Section PureITree.
  
  Definition PureITree A := itree Void A.

  Definition _PureITreeSpec A := forall (p : itree Void A -> Prop), (resp_eutt Void A p) -> Prop.

  Definition _retpi A (a : A) : _PureITreeSpec A := fun p _ => p (ret a).

  Definition monotonici A (w : _PureITreeSpec A) :=
    forall (p p' : itree Void A -> Prop) (Hp : resp_eutt Void A p) (Hp' : resp_eutt Void A p'),
                                          (forall i', p i' -> p' i') -> w p Hp -> w p' Hp'. 

  Definition PureITreeSpec A := {w : _PureITreeSpec A | monotonici A w}.

  Lemma retpi_monot : forall A (a : A), monotonici A (_retpi A a).
  Proof.
    unfold monotonici. intuition. unfold _retpi in *. auto.
  Qed.

  Inductive is_val A (a : A) : itree Void A -> Prop :=
    | base :  is_val A a (ITreeDefinition.Ret a)
    | tau (t : itree Void A): is_val A a t -> is_val A a (Tau t) .

  Definition is_val_eutt A (a : A) (t : itree Void A) := t ≈ ret a.

  Lemma is_val_resp_eutt : forall A a, resp_eutt Void A (is_val_eutt A a).
    Proof.
      intros. intros t1 t2. unfold is_val_eutt. split; intros.
      - rewrite H in H0. auto.
      - rewrite H. auto.
    Qed.

  Lemma is_val_tau_invar : forall A (a : A), tau_invar Void A (is_val A a).
  Proof.
    intros. unfold tau_invar. split; intros.
    - constructor. auto.
    - inversion H. auto.
  Qed.

  Lemma eutt_reta_or_spin_aux : forall A (t : itree Void A), (forall a, ~(t≈ ret a)) -> divergence t.
    Proof.
      intros A. pcofix CIH. intros. pfold. unfold divergence_.
      destruct (observe t) eqn:Heqt.
      - specialize (itree_eta t) as H. rewrite Heqt in H.
        specialize (H0 r0). rewrite H in H0. exfalso. apply H0.
        reflexivity.
      - specialize (itree_eta t) as H. rewrite Heqt in H. constructor. right. eapply CIH; eauto.
        intros. rewrite <- tau_eutt. rewrite <- H. auto.
      - destruct e.
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

  Lemma tau_invar_prop_subst_aux_eutt : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), resp_eutt Void A p ->
                                     is_val_eutt A a t /\ is_val_eutt A a t' -> (p t -> p t').
    Proof.
      intros. destruct H0 as [Ht Ht'].
      unfold is_val_eutt in *. rewrite <- Ht in Ht'. eapply H; try eassumption.
    Qed.
  Lemma tau_invar_prop_subst : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), tau_invar Void A p ->
                               is_val A a t /\ is_val A a t' -> (p t <-> p t').
    Proof.
      split; intros; eapply tau_invar_prop_subst_aux; eauto.
      destruct H0. split; eauto.
    Qed.

  Lemma tau_invar_prop_subst_eutt : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), resp_eutt Void A p ->
                                     is_val_eutt A a t /\ is_val_eutt A a t' -> (p t <-> p t').
    Proof.
      split; intros; eapply tau_invar_prop_subst_aux_eutt; eauto. split; destruct H0; eauto.
    Qed.


  Lemma divergence_tau_invar : forall A, tau_invar Void A divergence.
  Proof.
    intros. split; intros.
    - pfold. left. constructor. auto.
    - pinversion H. subst. auto.
  Qed.

  Ltac dest_void := match goal with [ E : Void ?A  |- _ ]=> destruct E end.  

  Lemma divergence_resp_eutt : forall A, resp_eutt Void A divergence.
    Proof.
      intro A. intro. intro.  intro. split.
      - generalize dependent t2. generalize dependent t1. pcofix CIH.
        intros. assert (Ht1 : divergence t1). auto. pfold. punfold H1. unfold divergence_ in *.
        destruct (observe t1) eqn : Heqt1; destruct (observe t2) eqn : Heqt2; try dest_void; try inv_div_ret.
        + specialize (itree_eta t2) as H. rewrite Heqt2 in H.
          rewrite H in H0. rewrite H0 in Ht1. pinversion Ht1.
        + constructor. inversion H1; subst. right. eapply CIH with (t1 := t1); eauto.
          clear H2 H1. rewrite H0. clear Heqt1.  specialize (itree_eta t2) as H. rewrite Heqt2 in H.
          rewrite <- (tau_eutt t0). rewrite H. reflexivity.
      - generalize dependent t2. generalize dependent t1. pcofix CIH.
        intros. assert (Ht2: divergence t2). auto. pfold. punfold H1. unfold divergence_ in *.
        destruct (observe t1) eqn : Heqt1; destruct (observe t2) eqn : Heqt2; try dest_void; try inv_div_ret.
        + specialize (itree_eta t1) as H. rewrite Heqt1 in H. rewrite H in H0.
          rewrite <- H0 in Ht2. pinversion Ht2.
        + constructor. inversion H1; subst. right. eapply CIH with (t2 := t2); eauto.
          rewrite <- H0. clear H1 H2 Heqt2. specialize (itree_eta t1 ) as H. rewrite Heqt1 in H.
          rewrite <- (tau_eutt t). rewrite H. reflexivity.
  Qed.

  Lemma divergence_resp_eutt' : forall A, resp_eutt Void A divergence.
  Proof.
    intros. unfold resp_eutt. intros. rewrite H. tauto.
  Qed.

  Lemma no_val_div : forall A , tau_invar Void A (fun t => ~exists a, is_val A a t).
    Proof.
      intros. split; intros; intro Hcontra.
      - apply H. destruct Hcontra as [a Ha]. exists a. inv Ha. auto.
      - apply H. destruct Hcontra as [a Ha]. exists a. constructor. auto.
    Qed.

  Lemma eutt_reta_or_div_aux : forall A (t : itree Void A), ~(exists a, ret a ≈ t) -> divergence t.
    Proof.
      intro A. pcofix CIH. pfold. unfold divergence_.  intros. destruct (observe t) eqn : Heqt.
      - exfalso. specialize (itree_eta t) as H. rewrite Heqt in H. apply H0.
         exists r0. rewrite H. reflexivity.
       - constructor. right. eapply CIH; eauto. intro. apply H0.
         destruct H as [a Ha]. exists a. specialize (itree_eta t) as Ht. rewrite Heqt in Ht.
         rewrite Ht. rewrite tau_eutt. auto.
       - destruct e.
    Qed.

  Lemma eutt_reta_or_div : forall A (t : itree Void A), (exists a, ret a ≈ t) \/ (divergence t).
    Proof.
      intros A t.  specialize (classic (exists a, ret a ≈ t) ) as Hlem. destruct Hlem; auto.
      right. apply eutt_reta_or_div_aux. auto.
    Qed.


  Lemma bind_pred_resp_eutt : forall A B (f : A -> _PureITreeSpec B)
                                     (p : itree Void B -> Prop) (Hp : resp_eutt Void B p),
      resp_eutt Void A (fun (t : itree Void A) => (exists a, ret a ≈ t /\ f a p Hp) \/ 
                                                  (divergence t /\ p spin)).
  Proof.
    intros. intros t1 t2 Heutt. split; intros; destruct H.
    - destruct H as [ a [Hta Hfa] ]. left. exists a. rewrite Hta. auto.
    - rewrite Heutt in H. auto.
    - left. destruct H as [ a [Hta Hfa] ]. exists a. rewrite Hta. symmetry in Heutt. auto.
    - rewrite <- Heutt in H. auto.
  Qed.

  
  (*intuitively, you have two choices, prove the tree evaluates to a and prove f a p,
    or prove t is infinite and prove that the infinite predicate is in w*)
  Definition _bindpi A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B) :=
    fun (p : itree Void B -> Prop) (Hp : resp_eutt Void B p) =>
      w (fun (t : itree Void A) => (exists a, ret a ≈ t /\ f a p Hp) \/ 
                                   (divergence t /\  p spin ))
  (bind_pred_resp_eutt A B f p Hp).
(* replace   *)


  Lemma bindpi_monot : forall A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B),
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B (_bindpi A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *.
    set (fun (t : itree Void A) p0 Hp0 => (exists a, ret a ≈ t /\ f a p0 Hp0)\/ (divergence t /\ p spin))  as fp.
    enough (forall t, fp t p Hp -> fp t p' Hp').
    - eapply H with (p := fun t => fp t p Hp).
      + intros.  apply H3 in H4. 
        unfold fp in H4. destruct H4; auto.
        destruct H4. right. auto.
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
    fun A w1 w2 => forall (p : itree Void A -> Prop) (Hp : resp_eutt Void A p), proj1_sig w1 p Hp <-> proj1_sig w2 p Hp.


  Lemma ret_not_div : forall (A : Type) (E : Type -> Type) (a : A), ~ (@divergence E A (ret a)).
    Proof.
      intros. intro Hcontra. pinversion Hcontra.
    Qed.

  Lemma inv_ret : forall (A : Type) (E : Type -> Type) (a b : A),
        @eutt E A A eq (ret a) (ret b) -> a = b.
    Proof. 
      intros. pinversion H; subst. auto.
    Qed.
 
  Lemma retpi_bindpi : forall A B (f : A -> PureITreeSpec B) (a : A), 
      bind (ret a) f ≈ f a.
    Proof.
      intros. split.
      - cbn. unfold _bindpi. unfold _retpi. intros. 
        destruct H.
        + destruct H as [a0 [Hvala0 Hfa0] ].
          apply inv_ret in Hvala0. subst. auto.
        + exfalso. destruct H. eapply ret_not_div. eauto.
      - simpl. destruct (f a) as [fa Hfa] eqn : Heq. simpl. intros.
        left. exists a. split; auto.
        + reflexivity.
        + rewrite Heq. auto.
    Qed.

    
  Lemma bindpi_retpi : forall A (w : PureITreeSpec A), bind w (fun x => ret x) ≈ w.
  Proof.
    intros. destruct w as [ w Hw]. split.
    - intros. simpl in *. unfold _bindpi in H.
      unfold _retpi in H. simpl in H.
      eapply Hw.
      2: apply H.
      intros. destruct H0.
      + destruct H0 as [a [ Hvala Hpa]  ].
        eapply Hp; eauto. symmetry. auto.
      + destruct H0. apply div_spin_eutt in H0. eapply Hp; eauto.
    - simpl. intros. unfold _bindpi.
      eapply Hw. 2: apply H. intros. unfold _retpi.
      specialize (eutt_reta_or_div A i') as Hor. destruct Hor.
      + destruct H1 as [a Ha]. left. exists a. split; auto. eapply Hp; eauto.
      + right. split; auto. specialize (div_spin_eutt A i' H1) as H2. eapply Hp; eauto. symmetry. auto.
   Qed.
  Lemma bindpi_bindpi : forall (A B C : Type) (w : PureITreeSpec A) 
                               (f : A -> PureITreeSpec B) (g : B -> PureITreeSpec C),
      bind (bind w f) g ≈ bind w (fun a => bind (f a) g).
    Proof.
      intros. destruct w as [w Hw]. simpl. split; intros.
      - simpl in *. eapply Hw; try apply H. intros t0. intros. destruct H0.
        + destruct H0 as [a [Hreta Hfa] ].
          left. exists a. split; auto. destruct (f a) as [wfa Hwfa]. simpl in *.
          eapply Hwfa; try (apply Hfa). intros t1. intros. destruct H0; auto.
        + destruct H0. destruct H1.
          * destruct H1 as [b [Hretb Hgb ]  ]. exfalso. specialize (ret_not_div B Void b) as Hndiv.
            rewrite Hretb in Hndiv. apply Hndiv. apply spin_div.
          *  right. destruct H1. auto.
      - simpl in *. eapply Hw; try apply H. intros t0. intros. destruct H0.
        +  destruct H0 as [a [Hreta Hfa] ]. left. exists a. split; auto.
           destruct (f a) as [wfa Hwfa]. simpl in *. eapply Hwfa; try (apply Hfa). intros t1. intros.
           destruct H0; auto.
        + destruct H0. right. split; auto. right. split; auto. apply spin_div.
    Qed.


  Global Instance PureItreeSpecLaws : MonadLaws PureITreeSpec.
  Proof.
    constructor.
    - apply retpi_bindpi.
    - apply bindpi_retpi.
    - apply bindpi_bindpi.
  Qed.  

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
End StateITree.
(*
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
  Qed. *)
(* bind I think needs some coinduction, I'll leave it out for now
  Definition _bindis A B (m : _StateItreeSpec A) (f : A -> _StateItreeSpec B) :=
    fun p s => m (fun '(i,s') =>  ) s

    if i = tau ^ ω then p (i,s') since i has either type _StateItreeSpec A or _StateItreeSpec B
    else i = tau ^* (Ret a) then p (ret (a,s'))

    problem is the first case doesn't terminate, need more info on coinduction from Steve maybe?
*)

(*

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
*)
