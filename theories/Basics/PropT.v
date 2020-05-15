From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Typ_Class2
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
.

Import CatNotations.
Open Scope cat_scope.

Section MonadProp.
  Program Definition PropM : typ -> typ :=
    fun (A : typ) =>
      {|
        Ty := {p : A -> Prop | Proper (equalE A ==> iff) p};
        equal :=
          fun pm1 pm2 =>
            forall (a : A), ` pm1 a <-> ` pm2 a
      |}.
  Next Obligation.
    split.
    repeat red. intros x y H a.
    split. apply H. apply H.
    repeat red. intros x y z H H0 a.
    split. intros. apply H0, H, H1. intros. apply H, H0, H1.
  Qed.

  Instance PropM_Monad : Monad typ_proper PropM.
  split.
  - repeat red. intros A.
    refine (exist _ (fun (a:A) => (exist _ (fun x => equalE A a x) _)) _).
    repeat red. cbn. intros x y Heq a_term.
    rewrite Heq. auto.
    Unshelve.
    repeat red. intros.
    rewrite H.
    auto.
  - repeat red. intros A B HK.
    destruct HK as (K & KProper).
    refine (exist _ (fun PA: PropM A => (exist _ (fun b: B =>
            exists a : A, `PA a /\ (proj1_sig (K a)) b) _)) _).
    (* KS: For some reason the back-tick didn't work here *)
    repeat red. cbn. intros ma1 ma2 Heq b.
    split; intros; destruct H; exists x; specialize (Heq x).
    + rewrite <- Heq. auto.
    + rewrite Heq. auto.
    Unshelve.
    repeat red. intros b1 b2 Heq.
    split; intros; destruct H; exists x; destruct H; split; auto.
      * cbn in *. destruct K.
        (* KS: Coq can't find the necessary Proper instance to
               rewrite unless K is destructed. *)
        rewrite <- Heq. auto.
      * cbn in *; destruct K; rewrite Heq; auto.
  Qed.

End MonadProp.

Section MonadPropT.


  Context {M : typ -> typ}.
  Context `{F : Functor typ typ typ_proper typ_proper M}.
  Context `{CM : Monad typ typ_proper M}.
  Context `{ML : MonadLaws typ typ_proper M}.

  Lemma PropT_PER_equal:
    forall X : typ,
      PER
        (fun PA1 PA2 : {p : M X -> Prop | Proper (equalE (M X) ==> iff) p} =>
            forall ma : M X, equalE (M X) ma ma -> (` PA1) ma <-> (` PA2) ma).
  Proof.
    intros X.
    split.
    - repeat red. intros x y H6 ma H7.
      apply H6 in H7. destruct H7.
      split; eauto.
    - repeat red. intros x y z H6 H7 ma H8.
      specialize (H6 _ H8). destruct H6.
      specialize (H7 _ H8). destruct H7.
      split; eauto.
  Qed.

  Definition PropT : typ -> typ :=
    fun (X : typ) =>
      {|
        Ty := { p : M X -> Prop | Proper (equalE (M X) ==> iff) p };
        equal :=
          fun PA1 PA2 =>
            forall (ma : M X), equalE (M X) ma ma -> ` PA1 ma <-> ` PA2 ma;
        equal_PER := PropT_PER_equal X
      |}.

  Instance ret_equalE_proper {A}:
    Proper (equalE A ==> equalE (M A) ==> impl) (fun x => equalE (M A) ((` ret) x)).
  Proof.
    destruct ret. cbn in *.
    do 2 red in p. do 3 red. intros x0 y H6 x1 y0 H7.
    rewrite <- H7.
    specialize (p _ _ H6).
    rewrite p. reflexivity.
  Qed.

  Arguments fmap {_ _}.

  Definition agrees {A B} : typ_proper A (M B) -> typ_proper A ((PropT B)) -> Prop :=
    fun TA TB => forall (a : A), exists (mb : M B),
          equalE (M B) mb (` TA a) /\ ` (` TB a) mb.

  Definition ret_f :=
    fun A a (ma : M A) => equalE (M A) (` ret a) ma.

  Definition bind_f :=
    fun A B (PA : PropT A) (K : typ_proper A (PropT B)) (mb : M B) =>
      exists (ma : M A) (kb : typ_proper A (M B)), `PA ma /\
        (forall (x : M A), equalE (M A) ma x ->
        equalE (M B) mb ((` (bind kb)) x)) /\
        agrees kb K.


  Lemma ret_proper_inner:
    forall (A : typ) (a : A), Proper (equalE (M A) ==> iff) (fun ma : M A => ret_f A a ma).
  Proof.
    intros A a.
    unfold ret_f.
    repeat red.
    refine (fun x y EQ => _).
    (* Introduce a proper instance for rewriting under equalE (M A). *)
    split; intros EQ'.
    + rewrite EQ in EQ'. eapply EQ'.
    + rewrite <- EQ in EQ'. apply EQ'.
  Qed.

  Lemma ret_proper_outer:
    forall (A : typ) (x y : A),
      equalE A x y ->
      forall ma : M A,
        equalE (M A) ma ma ->
        (` (exist (Proper (equalE (M A) ==> iff)) (fun ma0 : M A => equalE (M A) ((` ret) x) ma0) (ret_proper_inner A x))) ma <->
        (` (exist (Proper (equalE (M A) ==> iff)) (fun ma0 : M A => equalE (M A) ((` ret) y) ma0) (ret_proper_inner A y))) ma.
  Proof.
    intros A x y EQ ma EQ'.
    (* Properness proof of outer case. *)
    split; intros EQ''.
    + cbn. rewrite <- EQ''.
      eapply ret_equalE_proper. apply EQ. symmetry. eauto. eauto.
    + cbn. rewrite <- EQ''.
      eapply ret_equalE_proper. symmetry. apply EQ. symmetry; eauto.
      assumption.
  Qed.

  Lemma bind_proper_inner:
    forall (A B : typ) (K : typ_proper A (PropT B)) (PA : PropT A),
      Proper (equalE (M B) ==> iff) (fun mb : M B => bind_f A B PA K mb).
  Proof.
    intros A B K PA.
    unfold bind_f.
    repeat red.
    intros x y EQ.
    split; intros EQ'.
    - edestruct EQ' as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H6.
      split. intros. specialize (H7 _ H9).
      rewrite <- EQ.
      apply H7. apply H8.
    - edestruct EQ' as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H6.
      split. intros. specialize (H7 _ H9). rewrite EQ. apply H7.
      apply H8.
  Qed.

  (* IY : Need equalE to be an Equivalence, not a PER. *)
  Lemma equalE_refl : forall A, Reflexive (equalE A).
  Admitted.

  Lemma bind_proper_outer:
    forall (A B : typ) (K : typ_proper A (PropT B)),
      Proper (equalE (PropT A) ==> equalE (PropT B))
            (fun PA : PropT A =>
                exist (Proper (equalE (M B) ==> iff)) (fun mb : M B => bind_f A B PA K mb) (bind_proper_inner A B K PA)).
  Proof.
    intros A B K. cbn.
    unfold bind_f.
    split; intros EQ''; cbn in EQ''; cbn.
    + edestruct EQ'' as (ma0 & kb & Hx & EQ & Hagr).
      exists ma0, kb. split.
      apply H6. 2 : assumption.
      2 : split ; assumption.
      apply equalE_refl.
    + edestruct EQ'' as (? & ? & ? & ? & ?).
      exists x0, x1. split.
      apply H6.  2 : apply H8.
      2 : split; assumption.
      apply equalE_refl.
  Qed.

  Instance PropT_Monad : Monad typ_proper PropT :=
    {|
      ret := (fun A => exist _
                (fun a => exist _ (fun ma => ret_f A a ma) (ret_proper_inner A a))
                (ret_proper_outer A));
      bind := (fun A B K => exist _
                (fun (PA : PropT A) => exist _
                  (fun (mb : M B) => bind_f A B PA K mb) (bind_proper_inner A B K PA))
                (bind_proper_outer A B K))
    |}.

  Instance PropT_MonadLaws : MonadLaws PropT_Monad.
  constructor.
  - intros a b f.
    unfold ret, bind, PropT_Monad. repeat cbn.
  Admitted.

End MonadPropT.

(* Outdated sketches. *)
  (* Lemma transport_refl_feq_PM: forall {X : typ}, *)
  (*     Reflexive (equalE X) -> Reflexive (feq_PM X). *)
  (* Proof. *)
  (*   intros X eqx T H. *)
  (*   repeat red. *)
  (*   tauto. *)
  (* Qed. *)

  (* Lemma transport_symm_feq_PM : forall {X : typ}, *)
  (*     Symmetric (equalE X) -> Symmetric (feq_PM X). *)
  (* Proof. *)
  (*   repeat red. intros X H x y H0 ma H1. *)
  (*   split. Admitted. *)

  (* Lemma transport_symm_feq : *)
  (*   forall {X : typ}, (Symmetric (equalE X) -> Symmetric feq). *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)

  (* Lemma transport_trans_feq : *)
  (*   forall {X : typ}, (Transitive (equalE X) -> Transitive feq). *)
  (* Proof. *)
  (*   intros. red in H. *)
  (* Admitted. *)

  (* Program Definition ret_PM {A : typ} `{Symmetric A (equalE A)} `{Transitive A (equalE A)} (a : A) : @PropT A := *)
  (*   exist _ (fun (x:M A) => feq (ret a) x) _. *)
  (* Next Obligation. *)
  (*   repeat red. *)
  (*   intros. split. intros. eapply transitivity. eassumption. eassumption. *)
  (*   intros. eapply transitivity. eassumption. *)
  (*   apply (transport_symm_feq H). assumption. *)
  (*   Unshelve. apply transport_trans_feq. assumption. *)
  (*   Unshelve. apply transport_trans_feq. assumption. *)
  (* Defined. *)


(*  
  Global Instance monad_return_PM : @MonadReturn PM A _ _ := @ret_PM.
  
  Definition bind_PM (m : PM A) (f : A -> PM B) : PM B := 
    fun (b:B) =>
      exists (a:A), eqa a a /\ m a /\ f a b.

  Global Instance monad_bind_PM : @MonadBind PM _ _ _ _ TA TB := @bind_PM.
    
  Global Instance functor_PM : Functor PM.
  unfold Functor. unfold PM.
  exact (fun A eqa P Q => forall (a b:A), eqa a b -> (P a <-> Q b)).
  Defined.

  Global Instance functorOK_PM : @FunctorOK PM functor_PM.
  unfold FunctorOK.
  intros.
  unfold transport, functor_PM.
  constructor.
  - red. intros. symmetry. apply H. symmetry. assumption.
  - red. intros x y z H H1 a b H2. 
    eapply transitivity. apply H. apply H2. apply H1. eapply transitivity. symmetry. apply H2. apply H2.
  Defined.
End MonadProp.

Section MonadPropLaws.
  Context {A B C : Type}.
  Context {eqa : rel A} {eqb : rel B} {eqc : rel C}.
  Context (TA: TYP eqa).
  Context (TB: TYP eqb).
  Context (TC: TYP eqc).

  About MonadProperties.

  Instance monad_properties_PM : @MonadProperties PM A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  split.
  - repeat reduce.
    + unfold ret, monad_return_PM, ret_PM. split.
      intros. eapply transitivity. symmetry. apply H0. eapply transitivity. apply H1. assumption.
      intros. eapply transitivity. apply H0. eapply transitivity. apply H1. symmetry. assumption.      

  - repeat reduce.
    unfold bind, monad_bind_PM, bind_PM. split.
    intros. destruct H4 as (a0 & I & J & K).
    exists a0. repeat split; try tauto. eapply H.  apply I. tauto. eapply H0.
    apply I. apply H1. apply K.
    intros. destruct H4 as (a0 & I & J & K).
    exists a0. repeat split; try tauto. eapply H; tauto. eapply H0. apply I. tauto. tauto.

  - repeat reduce.
    unfold ret, monad_return_PM, ret_PM.
    unfold bind, monad_bind_PM, bind_PM.
    split.
    + intros.
      destruct H1 as (a1 & I & J & K).
      apply (PF a1 a); eauto.
    + intros.
      exists a. tauto.

  - repeat reduce.
    unfold ret, monad_return_PM, ret_PM.
    unfold bind, monad_bind_PM, bind_PM.
    split.
    + intros.
      destruct H1 as (a1 & I & J & K).
      unfold id. unfold transport in H. unfold functor_PM in H.

*)


(* Section MonadLaws. *)


(*   Class MonadProperties : Prop := *)
(*     { *)
(*       (* mon_ret_proper  :> forall {A : typ} `{PER A (equalE A)}, *) *)
(*       (*     Proper ((equalE A) ==> feq) ret; *) *)

(*       (* mon_bind_proper :> forall {A B : typ} `{PER A (equalE A)} `{PER B (equalE B)}, *) *)
(*       (*                 Proper (feq ==> (equalE A ==> feq) ==> feq) *) *)
(*       (*                 bind; *) *)

(*       bind_ret_l : forall {A B : typ} `{PER A (equalE A)} `{PER B (equalE B)} *)
(*           (f : A -> M B) (PF:Proper (equalE A ==> feq) f), *)
(*         (equalE (equalE A ~~> feq)) (fun (a:A) => bind (ret a) f)  f; *)

(*       bind_ret_r : forall {A : typ} `{PER A (equalE A)}, *)
(*           (equalE (feq ~~> feq)) (fun x => bind x ret) (id); *)

(*       bind_bind : forall {A B C : typ} *)
(*                     `{PER A (equalE A)} `{PER B (equalE B)} `{PER C (equalE C)} *)
(*                     (f : A -> M B) (g : B -> M C) *)
(*                     (PF:Proper (equalE A ==> feq) f)  (* f \in TYP (eqa ~~> eqb) *) *)
(*                     (PG:Proper (equalE B ==> feq) g), *)
(*         (equalE (feq ~~> feq)) *)
(*           (fun (x: M A) => (@bind M _ B C (bind x f) g)) *)
(*           (fun (x: M A) => (@bind M _ A C x (fun (y : A) => (bind (f y) g)))) *)
(*     }. *)
(* End MonadLaws. *)
