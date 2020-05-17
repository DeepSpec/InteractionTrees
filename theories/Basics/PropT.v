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
    split. intros. apply H0, H, H1; auto. intros. apply H, H0, H1; auto.
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
            forall ma : M X, (` PA1) ma <-> (` PA2) ma).
  Proof.
    intros X.
    split.
    - repeat red. intros x y H6 ma.
      split; eauto. apply H6. apply H6.
    - repeat red. intros x y z H6 H7 ma. 
      split; eauto. intros.  apply H7. apply H6. apply H8.
      intros. apply H6. apply H7. apply H8.
  Qed.

  Definition PropT : typ -> typ :=
    fun (X : typ) =>
      {|
        Ty := { p : M X -> Prop | Proper (equalE (M X) ==> iff) p };
        equal :=
          fun PA1 PA2 =>
            forall (ma : M X), ` PA1 ma <-> ` PA2 ma;
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

  (* Ret definition. *)
  Definition ret_ty_fn {A : typ} (a : A) : M A -> Prop :=
    fun (ma : M A) => equalE (M A) (` ret a) ma.

  Lemma ret_ty_proper {A : typ} (a : A) :
    Proper (equalE (M A) ==> iff) (ret_ty_fn a).
  Proof.
    unfold ret_ty_fn.
    repeat red.
    refine (fun x y EQ => _).
    (* Introduce a proper instance for rewriting under equalE (M A). *)
    split; intros EQ'.
    + rewrite EQ in EQ'. eapply EQ'.
    + rewrite <- EQ in EQ'. apply EQ'.
  Qed.

  Definition ret_ty {A : typ} : A -> PropT A :=
    fun a => exist _ (ret_ty_fn a) (ret_ty_proper a).

  Lemma ret_prop_proper :
    forall {A : typ}, Proper (equalE (A) ==> equalE (PropT A)) ret_ty.
  Proof.
    unfold ret_ty.
    intros A a f.
    (* Properness proof of outer case. *)
    split; intros EQ''.
    + cbn. unfold ret_ty_fn. rewrite <- EQ''.
      eapply ret_equalE_proper. apply H6. symmetry. eauto. eauto.
    + cbn. unfold ret_ty_fn. rewrite <- EQ''.
      eapply ret_equalE_proper. symmetry. apply H6. symmetry; eauto.
      assumption.
  Qed.

  (* IY: We could try having this kind of definition, but trying to use this
    is more cumbersome... Maybe there's a better way to write this *)
  Definition propT {A B : typ} {X}
             (f : X -> M A -> Prop) :=
    fun (prop_f : forall (x : X), Proper (equalE (M A) ==> iff) (f x)) (x : X) =>
      let fn := f x in
      let prop_fn := prop_f x in
      let ty := exist _ fn prop_fn in
      let fn_ty := fun (b : B) => ty in
      fun (p : Proper (equalE B ==> equalE (PropT A)) fn_ty) => exist _ f p.

  (* Definition ret_propT {A : typ} (a : A) : typ_proper A (PropT A) := *)
  (*   propT ret_ty_fn ret_ty_proper a _. *)

  Definition ret_propT {A} : typ_proper A (PropT A) :=
    exist _ (fun a => ret_ty a) ret_prop_proper.

  (* Bind definition. *)
  Definition agrees {A B} : typ_proper A (M B) -> typ_proper A ((PropT B)) -> Prop :=
    fun TA TB => forall (a : A), exists (mb : M B),
          equalE (M B) mb (` TA a) /\ ` (` TB a) mb.

  Definition bind_ty_fn {A B} (k : typ_proper A (PropT B)) (PA : PropT A)  :
    M B -> Prop :=
    fun (mb : M B) =>
      exists (ma : M A) (kb : typ_proper A (M B)), `PA ma /\
        (forall (x : M A), equalE (M A) ma x ->
        equalE (M B) mb ((` (bind kb)) x)) /\
        agrees kb k.

  Lemma bind_ty_proper :
    forall {A B : typ} (k : typ_proper A (PropT B)) (PA : PropT A) ,
      Proper (equalE (M B) ==> iff) (bind_ty_fn k PA).
  Proof.
    intros A B k PA.
    unfold bind_ty_fn.
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

  Definition bind_ty {A B} (k : typ_proper A (PropT B)) : PropT A -> PropT B :=
    fun PA => exist _ (bind_ty_fn k PA) (bind_ty_proper k PA).

  Lemma bind_prop_proper:
    forall {A B : typ} (k : typ_proper A (PropT B)),
      Proper (equalE (PropT A) ==> equalE (PropT B)) (bind_ty k).
  Proof.
    intros A B K. cbn.
    unfold bind_ty, bind_ty_fn.
    split; intros EQ''; cbn in EQ''; cbn.
    + edestruct EQ'' as (ma0 & kb & Hx & EQ & Hagr).
      exists ma0, kb. split.
      apply H6. assumption.
      split ; assumption.

    + edestruct EQ'' as (? & ? & ? & ? & ?).
      exists x0, x1. split.
      apply H6.  apply H7.
      split; assumption.
  Qed.

  Definition bind_propT {A B} (k : typ_proper A (PropT B)) :
    typ_proper (PropT A) (PropT B):=
    exist _ (fun PA => bind_ty k PA) (bind_prop_proper k).

  Instance PropT_Monad : Monad typ_proper PropT :=
    {|
      ret := @ret_propT;
      bind := @bind_propT
    |}.

  Instance PropT_MonadLaws : MonadLaws PropT_Monad.
  constructor.
  - intros a b f.
    unfold ret, bind, PropT_Monad.
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
