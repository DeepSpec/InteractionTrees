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

   is equivalent to set inclusion.
 *)
Infix "∈" := (eqmR agrees) (at level 70).

Section Transformer.

  Variable (m : Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqMR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP : @EqmR_OK m EQM}.
  Context {HMLAWS : @MonadLaws m EQM _}.
  Context {ML : @EqmRMonad _ _ _}.

  Definition closed_eqmR {A B} (REL : A -> B -> Prop) (PA : m A -> Prop) (PB : m B -> Prop)  :=
    forall ma mb, eqmR REL ma mb -> (PA ma <-> PB mb).

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

     M : Type -> Type

     M : {A:Type | rel A} -> {B:Type | rel B}
   *)
  Definition PropTM (A:Type) := (m A -> Prop).


  Definition eqm' : forall (A B : Type) (R: A -> B -> Prop), PropTM A -> PropTM B -> Prop :=
    fun A B R PA PB =>
      (forall ma, PA ma -> exists mb, PB mb /\ eqmR R ma mb) /\
      (forall mb, PB mb -> exists ma, PA ma /\ eqmR R ma mb).

      
    
  Global Instance EqMR_PropTM : EqMR PropTM := eqm'.

  Definition ret_f {A} (a:A) := (fun (x : m A) => eqm x (ret a)).

  (*
  Program Definition ret_f : forall A, A -> PropTM A := fun A (a : A) => _.
  Next Obligation.
    exists (ret_f' a).
    repeat red. unfold ret_f'. intros.
    split; intros. rewrite <- H0. assumption. intros. rewrite H0. assumption.
  Defined.
    *)                                   

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
  Definition bind_f' :=
  fun A B (PA : PropTM A) (K : A -> PropTM B) (mb : m B) =>
    exists (ma : m A) (kb : A -> m B),
      Monad.eqm mb (bind ma kb) /\
      (PA) ma /\
      (Functor.fmap kb ma) ∈ (Functor.fmap K ma).

  (*
  Lemma bind_f'_Proper :
    forall A B (PA : PropTM A) (K : A -> PropTM B),
      Proper (eqm ==> iff) (bind_f' A B PA K).
  Proof.
    intros.
    repeat red; unfold bind_f'; intros.
    split. intros.
    destruct H1 as (ma & kb & Hma & Hf).
    exists ma. exists kb. split. rewrite <- H0. assumption. assumption.
    intros.
    destruct H1 as (ma & kb & Hma & Hf).
    exists ma. exists kb. split. rewrite H0. assumption. assumption.
  Qed.
*)

  Global Instance Monad_PropTM : Monad (PropTM) :=
    {|
      ret:= @ret_f
      ; bind := bind_f'
    |}.

  (*
  Instance eqmR_MonadProp_Proper_impl {A} R (P : PropTM A) : Proper (eqmR R --> impl) P.
  Proof.
  Admitted.
   *)


  Ltac solve_equiv :=
    unfold eqmR, EqMR_PropTM, eqm';
    intros RR; constructor; [ | unfold closed_eqmR ];
    intros ma ma'; [intros r |]; intros Heq; split; intros Hx;
    [ rewrite Heq in Hx | rewrite <- Heq in Hx |
        rewrite Heq in Hx | rewrite <- Heq in Hx ].

  Global Instance EqMR_OK_PropTM : @EqmR_OK PropTM EqMR_PropTM.
  split. 
  - intros A R. unfold eqmR, EqMR_PropTM, eqm'.
    intros RR. split.
     + intros. exists ma. split. assumption. reflexivity.
     + intros. exists mb. split. assumption. reflexivity.

  - intros A R. unfold eqmR, EqMR_PropTM, eqm'.
    intros RR. split; intros.
    + destruct H0 as (HL & HR).
      apply HR in H1.  destruct H1 as (mb & MB & MB').
      exists mb. split. assumption. symmetry. assumption.
    + destruct H0 as (HL & HR).
      apply HL in H1.  destruct H1 as (ma & MB & MB').
      exists ma. split. assumption. symmetry. assumption.
  - intros A R. unfold eqmR, EqMR_PropTM, eqm'.
    intros RR. split; intros.
    + destruct H0 as (HL & HR).
      destruct H1 as (KL & KR).
      apply HL in H2. destruct H2 as (mb & MB & MB').
      apply KL in MB. destruct MB as (mc & MC & MC').
      exists mc. split. assumption. eapply transitivity; eassumption.
    + destruct H0 as (HL & HR).
      destruct H1 as (KL & KR).
      apply KR in H2. destruct H2 as (ma & MA & MA').
      apply HR in MA. destruct MA as (mc & MC & MC').
      exists mc. split. assumption. eapply transitivity; eassumption.

  - intros A B. 
    unfold eqmR, EqMR_PropTM, eqm'.
    repeat red.
    intros R1 R2 EQR PA1 PA2.
    intros (MA1 & MB1) PB1 PB2 (MA2 & MB2).
    split; intros (MC1 & MC2); split; intros ma Hma.
    + apply MB1 in Hma. destruct Hma as (ma' & MA' & EQ').
      apply MC1 in MA'. destruct MA' as (ma'' & MA'' & EQ'').
      apply MA2 in MA''. destruct MA'' as (ma''' & MA''' & EQ''').
      exists ma'''. split. assumption.
      apply MB2 in MA'''. destruct MA''' as (ma'''' & MA'''' & EQ'''').
      rewrite EQR in EQ''.

      (* SAZ :
      
          It looks like we need another property in the eqmR typeclass that
          acts like a kind of transitivity:

           eqmR R1 ma mb -> eqmR R2 mb mc -> eqmR (R1 ∘ R2) ma mc

         Then we can conclude this case by observing that 
            - eq_rel (eq ∘ R2) R2
            - eq_rel R2 (R2 ∘ eq) 
         and so by the property above (and symmetry for eq) we have:
             symmetry (EQ') ; EQ'' ; Eq ''' relates ma to ma'''

       *)
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

Section PropT_EqmRMonad.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQMR : EqMR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP: @EqMR_OK m EQMR}.
  Context {HM: @EqmRMonad m EQMR _}.

  Instance eqmR_OK_PropT : EqmR_OK (PropTM m).
End PropT_EqmRMonad.

Section Laws.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqMR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP: @EqMR_OK m EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.
<<<<<<< HEAD



  
  Instance eqm_MonadProp_Proper {A} (P: PropTM m A) : Proper (@eqm _ _ A ==> iff) P.
  Proof.
    cbv. intros x y Heq.

  Admitted.
=======
  Context {ML : EqmRMonad m}.
>>>>>>> fa1ee28772a58325ada40f7ccc78bf8157008a24

  Lemma bind_ret_l:
    forall A B (f : A -> PropTM m B) (a : A),
      eqm (bind (ret a) f) (f a).
  Proof.
    cbn; unfold bind_f, ret_f; cbn; unfold liftM.
    intros A B k a. pose proof EqmRMonad_PropTM as PM.
    specialize (PM m H EQM ITERM _ _ _).
    split.
    - intros x y r Heq. split.
      + intros Hm. edestruct Hm as (ma & km & Hma & HeqmR & Hx).
        clear Hm.
        rewrite HeqmR in Hma. rewrite bind_ret_l in Hma.
        rewrite HeqmR in Hx. rewrite 2 bind_ret_l in Hx.
        rewrite <- eqmR_ret in Hx; [ | assumption].
        unfold agrees in Hx.
         (* IY: Why doesn't rewrite <- Heqmr work directly? (Also, is this proper instance too generalized? )*)
        eapply eqmR_MonadProp_Proper_impl_flip; try assumption.
        apply Heq.
        eapply eqmR_MonadProp_Proper_impl; try assumption.
        apply Hma. apply Hx.
      + intros Hk. exists (ret a). exists (fun _ => x).
        split. rewrite bind_ret_l. reflexivity.
        split. reflexivity. rewrite 2 bind_ret_l.
        apply eqmR_ret; [assumption | ].
        unfold agrees.
        eapply eqmR_MonadProp_Proper_impl; try assumption.
        apply Heq. apply Hk.
    - split. (* Can I split while introducing variable names? *)
      + intros Hm.
        edestruct Hm as (ma & kb & Hb & Hma & Heq).
        rewrite Hma in Heq. rewrite 2 bind_ret_l in Heq.
        apply eqmR_ret in Heq; [ | assumption]. unfold agrees in Heq.
        rewrite Hma in Hb. rewrite bind_ret_l in Hb.
        eapply eqmR_MonadProp_Proper_impl_flip in Heq; try assumption.
        2 : apply HEQP. 2 : apply HMLAWS. 2 : apply ML. (* Why aren't these discharged? *)
        apply Heq. rewrite <- Hb. apply H0.
      + intros K.
        exists (ret a). exists (fun _ => a0).
        split. rewrite bind_ret_l. reflexivity.
        split. reflexivity. rewrite 2 bind_ret_l. apply eqmR_ret; [assumption | ].
        unfold agrees. eapply eqmR_MonadProp_Proper_impl; try assumption.
        apply H0. assumption.
  Qed.

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
        (* rewrite <- Heqmr. clear Heqmr. *)
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
