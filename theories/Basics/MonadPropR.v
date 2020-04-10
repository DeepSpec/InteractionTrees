From ExtLib Require Import
     Structures.Monad.
From ITree Require Import
     ITree
     Eq.Eq
     ITreeMonad
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Monad.

From Paco Require Import paco.

From Coq Require Import Morphisms
     Program.Equality
     Classes.RelationClasses
     Relation_Definitions
.

Require Import Classical_Prop.
(* See [PropT.v] in the Vellvm repo for the exact framework to follow with respect to typeclasses, as well as a proof of most monad laws for [PropTM (itree E)] *)

Definition agrees {A : Type} :=
    fun (x : A) (P : A -> Prop) => P x.

(* NB: ∈ is the notation for [eqmR agrees], since if we think of (A -> Prop) as
       a set of elements of type A,

       eqmR agrees : A -> (A -> Prop) -> Prop

   is intuitively a proposition equivalent  for the set inclusion of an element of
   type A in a set of elements of type A.
 *)
Infix "∈" := (eqmR agrees) (at level 70).

Section Transformer.

  Variable (m : Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqMR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP : @EqMR_OK m EQM}.
  Context {HMLAWS : @MonadLaws m EQM _}.
  Context {ML : @EqmRMonad _ _ _}.

  Definition closed_eqmR {A B} (PA : m A -> Prop) (PB : m B -> Prop) (REL : A -> B -> Prop) :=
    forall a b, eqmR REL a b -> (PA a <-> PB b).

  (* === DESIGN 1 : Eqm Closure defined on definition of EQMR Instance. === *)

  (* Unlike in [MonadPropClosed.v] (in `prop` branch), under generalized eqm,
     PropTM is not closed by construction.
     Parameterizing each PropTM instance by a relation that it is closed under
     would not give us a monad instance. Instead, we parameterize the `eqm` relation
     that the EqMR instance is defined under.

     One thing that we would need to resolve now, though, is how we state the EqMR
     closedness property. It could either be stated as an auxiliary lemma or
     as seen in [DESIGN 2], we can instantiate the PropTM with a special eqm
     closedness on "agrees".
   *)
  Definition PropTM : Type -> Type :=
    fun A => m A -> Prop.

  Definition eqm' : forall (A B : Type) (R : A -> B -> Prop), PropTM A -> PropTM B -> Prop :=
    fun _ _ REL PA PB =>
      (forall x y r, eqmR r x y -> (PA x <-> PB y)) /\
      closed_eqmR PA PB REL.

  Global Instance EqMR_PropTM : EqMR PropTM := eqm'.

  Definition ret_f := (fun A (a : A) (ma : m A) => eqm ma (ret a)).

  (*
    Binding a PropTM monad (PA : PropTM A) and a continuation (K : A -> PropTM)
    intuitively means that we can have an "computational decomposition" of the
    bind on the underlying monad (i.e. mb ≈ bind ma kb), where:

    1. [PA ma]
           PA describes the nondeterministic set of computation on the first part of
       the computation, ma.

    2. [(fmap kb ma) ∈ (fmap K ma)]
           This means that the continuation PropTM captures all the nondeterministic
           computations that the monadic bind captures the continuation of.

    As an illustrative example, if we were to have the following bind:

        x <- {1; 2} ;;
        if (x is_even) then {ret x ; ret x} else { ret x})

    We would like the resulting set of nondeterministic computation to be:
       {ret 1; ret 2; ret 2}.
   *)
  Definition bind_f :=
  fun A B (PA : PropTM A) (K : A -> PropTM B) (mb : m B) =>
    exists (ma : m A) (kb : A -> m B),
      Monad.eqm mb (bind ma kb) /\
      PA ma /\
      (Functor.fmap kb ma) ∈ (Functor.fmap K ma).

  Global Instance Monad_PropTM : Monad (PropTM) :=
    {|
      ret:= fun A (a: A) => (ret_f A a)
      ; bind := fun A B (PA : PropTM A) (K : A -> PropTM B) =>
                  (bind_f A B PA K)
    |}.

  Instance eqmR_MonadProp_Proper {A} r (P : PropTM A) : Proper (eqmR r ==> iff) P.
  Proof.
    repeat red. intros x y Heq; split; [intros Px | intros Py].
  Admitted.

  Ltac solve_equiv :=
    unfold eqmR, EqMR_PropTM, eqm';
    intros RR; constructor; [ | unfold closed_eqmR ];
    intros ma ma'; [intros r |]; intros Heq; split; intros Hx;
    [ rewrite Heq in Hx | rewrite <- Heq in Hx |
        rewrite Heq in Hx | rewrite <- Heq in Hx ].

  Global Instance EqMR_OK_PropTM : @EqMR_OK PropTM EqMR_PropTM.
  split; intros A R.
  - solve_equiv; assumption.
  - solve_equiv; edestruct H0 as (Hr & HR); unfold closed_eqmR in *;
      specialize (Hr ma ma' _ Heq); apply Hr in Hx;
         [ rewrite Heq in Hx | rewrite <- Heq in Hx |
        rewrite Heq in Hx | rewrite <- Heq in Hx ]; assumption.
  - solve_equiv; edestruct H0 as (Hr & HR); edestruct H1 as (Hr' & HR');
      unfold closed_eqmR in *; specialize (Hr _ _ _ Heq);
        specialize (Hr' _ _ _ Heq);
    match goal with
      | H : _ ?x |- _ ?x => rewrite <- Heq in Hx; apply Hr in Hx;
                            rewrite <- Heq in Hx; apply Hr' in Hx
      | _ => rewrite Heq in Hx; apply Hr' in Hx;
                rewrite Heq in Hx; apply Hr in Hx
    end ; assumption.
  - do 3 red; unfold eqmR, EqMR_PropTM, eqm' in *.
    intros x y Heq pa pa' HA pr pr' HR. split;
    intros HAR; split;
      destruct HAR as (HAReq & HARclo);
      destruct HA as (HAeq & HAclo);
      destruct HR as (HReq & HRclo); try (unfold closed_eqmR);
      intros ma mr; [intros z | | intros z | ]; intros Heqm;
      assert (Hma : eqmR eq ma ma) by reflexivity;
      assert (Hmr : eqmR eq mr mr) by reflexivity;
      specialize (HAReq ma mr _ Heqm);
      specialize (HAeq ma ma eq Hma); clear Hma;
      specialize (HReq mr mr eq Hmr); clear Hmr;
      split; intros Hp;
    match goal with
    | |- _ mr => apply HAeq in Hp; apply HAReq in Hp; apply HReq in Hp; assumption
    | |- _ ma => apply HReq in Hp; apply HAReq in Hp; apply HAeq in Hp; assumption
    end.
  Qed.

  Lemma ret_ok : forall (A1 A2 : Type) (RA : A1 -> A2 -> Prop) (a1 : A1) (a2 : A2),
      RA a1 a2 <-> (eqmR RA (ret a1) (ret a2)).
  Proof.
    unfold eqmR, EqMR_PropTM.
  Admitted.

  Instance EqmRMonad_PropTM : @EqmRMonad PropTM _ _.
  Proof.
    pose proof EqMR_OK_PropTM.
    constructor; unfold eqmR, EqMR_PropTM, eqm'.
    - apply ret_ok.
    - intros A1 A2 B1 B2 RA RB ma1 ma2 kb1 kb2 HA HB.
      split; intros mb1 mb2 RB'.
      destruct HA as (HAeq & HAclo).
      + intros Heq. split. intros Hbind.
  Admitted.

  (* ===== DESIGN 2 : Defining "agrees-closed-eqm" by Construction ======== *)

  Definition closed_eqmR_agrees {A} (P : m A -> Prop) :=
    forall (ma : m A) (P' : m (A -> Prop)) (WP : m (A -> Prop) -> Prop),
      ma ∈ P' -> (P ma <-> WP P').

  (* Alternative definition, based on agrees. *)
  Definition PropTM' : Type -> Type :=
    fun A => {P : m A -> Prop | closed_eqmR_agrees P}.

  Lemma ret_f_closed_eqmR_agrees :
    forall A (a : A), closed_eqmR_agrees (ret_f A a).
  Proof.
    intros. red. intros; split; intros.
    - unfold ret_f in H1. rewrite H1 in H0.
  Admitted.

  Lemma bind_f_closed_eqmR_agrees:
    forall A B (PA : PropTM A) (K : A -> PropTM B),
      closed_eqmR_agrees (bind_f A B PA K).
  Proof.
  Admitted.
  
End Transformer.

Section Laws.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqMR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP: @EqMR_OK m EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.

  Instance eqm_MonadProp_Proper {A} (P: PropTM m A) : Proper (@eqm _ _ A ==> iff) P.
  Proof.
    cbv. intros x y Heq.
  Admitted.

  Lemma bind_ret_l:
    forall A B (f : A -> PropTM m B) (a : A),
      eqm (bind (ret a) f) (f a).
  Proof.
    intros A B k a.
    cbn. unfold bind_f, ret_f. split.
    - intros x y r Heq. split.
      + intros Hm. edestruct Hm as (ma & km & Hma & HeqmR & Hx).
        clear Hm.
      (*   rewrite Hx in Heq; clear Hx. *)
      (*   rewrite Hma, bind_ret_l in Heq; clear Hma. *)
      (*   setoid_rewrite <- Heq; clear Heq x y r. admit. *)
      (* + intros Hk. setoid_rewrite <- Heq in Hk; clear Heq. *)
      (*   exists (ret a). exists (fun _ => x). split; [reflexivity | split]. *)
      (*   * cbn. unfold liftM. rewrite 2 bind_ret_l. *)
  Admitted.

  Lemma bind_ret_r:
    forall A (ma : PropTM m A),
      eqm (bind ma (fun x => ret x)) ma.
  Proof.
    intros A PTmA.
    cbn in *. unfold bind_f, ret_f in *.
    cbn in *. unfold liftM in *.
    split.
    - intros mA1 mA2 R. intros Heqmr.
      split.
      + intros comp.
        destruct comp as (mA & ka & Hpta & Heqmrbind & Heqbind).
        
        assert (HProper: Proper (eqmR R --> flip impl) PTmA).
        admit.

        rewrite <- Heqmr. clear Heqmr. clear HProper.
        (* rewrite Heqbind. clear Heqbind. *)
        (* Want to take (bind mA ka) to mA, which might mean
           that kamA is ret. I think Heqmrbind gives this. *)
        admit.
      + intros Hpta2.
        exists mA2, (fun x => ret x). split; auto.
        * admit.
        *
          (* rewrite bind_ret_r. *)

          (* assert (HProper: Proper (eqmR R --> flip impl) (eqm mA1)). *)
          admit.

          (* rewrite <- Heqmr. *)
          (* reflexivity. *)
    - split.
      rename a into mA1. rename b into mA2. rename H0 into Heqmr.
      + intros comp.
        destruct comp as (mA & ka & Hpta & Heqmrbind & Heqbind).
        (* This rewrite works for some reason?? *)
        rewrite <- Heqmr. clear Heqmr.
        (* rewrite Heqbind. clear Heqbind. *)
        (* same situation as above *)
        admit.
      + intros Hpta2. 
        rename a into mA1. rename b into mA2. rename H0 into Heqmr.
        exists mA2, (fun x => ret x). split; auto. 
        * admit.
        (* * rewrite bind_ret_r. auto. *)
Admitted.

  Lemma bind_bind:
    forall A B C (ma : PropTM m A) (mab : A -> PropTM m B)
           (mbc : B -> PropTM m C),
      eqm (bind (bind ma mab) mbc) (bind ma (fun x => bind (mab x) mbc)).
  Proof.
  Admitted.

  Lemma respect_bind :
  forall a b : Type, Proper (eqm ==> pointwise_relation a eqm ==> @eqm (PropTM m) _ b) bind.
  Proof.
  Admitted.

  Global Instance PropTM_Laws : @MonadLaws (PropTM m) _ _.
  split. apply bind_ret_l.
  apply bind_ret_r. apply bind_bind.
  apply respect_bind.
  Qed.

End Laws.
