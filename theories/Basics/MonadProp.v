From ExtLib Require Import
     Structures.Monad.
From ITree Require Import
     ITree
     Eq.Eq
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.HeterogeneousRelations
     Basics.Monad.

From Paco Require Import paco.

From Coq Require Import Morphisms
     Program.Equality
     Classes.RelationClasses
     Relation_Definitions
.

Require Import Classical_Prop.
(* See [PropT.v] in the Vellvm repo for the exact framework to follow with respect to typeclasses, as well as a proof of most monad laws for [PropT (itree E)] *)

Definition agrees {A : Type} :=
    fun (x : A) (P : A -> Prop) => P x.

(* NB: ∈ is the notation for [eqmR agrees], since if we think of (A -> Prop) as
       a set of elements of type A,

       eqmR agrees : A -> (A -> Prop) -> Prop

   is equivalent to set inclusion.
 *)
Infix "∈" := (eqmR agrees) (at level 70).

Import RelNotations.
Open Scope relationH_scope.

Section Transformer.

  Variable (m : Type -> Type).
  Context {Mm: Monad m}.
  Context {EqMRm : EqmR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP : EqmR_OK m}.
  Context {ML : EqmRMonad m}.

  (* === Eqm Closure defined on definition of EQMR Instance. === *)

  (* Unlike in [MonadPropClosed.v] (in `prop` branch), under generalized eqm,
     PropT is not closed by construction.
     Parameterizing each PropT instance by a relation that it is closed under
     would not give us a monad instance. Instead, we parameterize the `eqm`
     relation that the EqMR instance is defined under.
     One thing that we would need to resolve now, though, is how we state the EqMR
     closedness property.
   *)
  Definition PropT (A:Type) := (m A -> Prop).

  Definition sub_predicate {A B: Type} (R: A -> B -> Prop): PropT A -> PropT B -> Prop :=
    fun PA PB => forall ma, PA ma -> exists mb, PB mb /\ eqmR R ma mb.
  Notation "PA '[⊆' R ']' PB" := (sub_predicate R PA PB) (at level 80).
  (* Note: the following could me more cleanly defined as (PA [⊆ †R] PB),
     but we need to assume that (eqmR †R ≈ †(eqmR R)) then
   *)
  Definition sub_predicate_rev {A B: Type} (R: A -> B -> Prop): PropT A -> PropT B -> Prop :=
    fun PA PB => forall mb, PB mb -> exists ma, PA ma /\ eqmR R ma mb.

  (* YZ: We probably want _some_ notion of closure here additionally in the definition of [eqm].
     Has been tried and appeared to be too strong:
   *)
  Definition relatively_closed_by_R {A B: Type} (R: A -> B -> Prop) (PA: PropT A) (PB: PropT B)
    := forall ma mb, eqmR R ma mb -> (PA ma <-> PB mb).

  (* Could be tried: *)
  Definition relatively_closed_by_R_weak {A B: Type} (R: A -> B -> Prop) (PA: PropT A) (PB: PropT B)
    := forall ma mb, eqmR R ma mb -> PA ma -> PB mb ->
                (forall (ma': m A), eqmR R ma' mb -> PA ma') /\
                (forall (mb': m B), eqmR R ma mb' -> PB mb').

  (* Note that we have: *)
  Lemma relatively_closed_strong_weak:
    forall {A B: Type} (R: A -> B -> Prop) (PA: PropT A) (PB: PropT B),
      relatively_closed_by_R R PA PB ->
      relatively_closed_by_R_weak R PA PB.
  Proof.
    split; intros;
      match goal with
      | h: relatively_closed_by_R _ _ _ |- _ => eapply h; eauto
      end.
  Qed.

  (* But not the converse (there can be a computation in PA linked to another one that is not in PB as long as it is not linked to anyone in PB *)
  (* However we have: *)
  Lemma relatively_closed_weak_bij_strong:
    forall {A B: Type} (R: A -> B -> Prop) (PA: PropT A) (PB: PropT B),
      PA [⊆ R] PB ->
      sub_predicate_rev R PA PB ->
      (* PB [⊆ †R] PA -> *)
      relatively_closed_by_R_weak R PA PB ->
      relatively_closed_by_R R PA PB.
  Proof.
    intros A B R PA PB INA INB REL;
      split; intros.
    edestruct INA as (x & ? & ?); eauto; eapply REL; eauto.
    edestruct INB as (x & ? & ?); eauto; eapply REL; eauto.
  Qed.

  Definition eqm_PropT : forall (A B : Type) (R: A -> B -> Prop), PropT A -> PropT B -> Prop :=
    fun A B R PA PB =>
      PA [⊆ R] PB /\
      PB [⊆ †R] PA.

  Global Instance EqmR_PropT : EqmR PropT := {| eqmR := eqm_PropT |}.

  Definition ret_f {A} (a:A) := (fun (x : m A) => eqm x (ret a)).

  (*
    Binding a PropT monad (PA : PropT A) and a continuation (K : A -> PropT)
    intuitively means that we can have an "computational decomposition" of the
    bind on the underlying monad (i.e. mb ≈ bind ma kb), where:

    1. [PA ma]
          PA describes the nondeterministic set of computation on the first part of
       the computation, ma.
    2. [(fmap kb ma) ∈ (fmap K ma)]
          This means that the continuation PropT captures all the nondeterministic
          computations that the monadic bind captures the continuation of.

    As an illustrative example, if we were to have the following bind:

        x <- {1; 2} ;;
        if (x is_even) then {ret x ; ret x} else { ret x})

    We would like the resulting set of nondeterministic computation to be:
       {ret 1; ret 2; ret 2}.
   *)
  Definition bind_f' :=
  fun A B (PA : PropT A) (K : A -> PropT B) (mb : m B) =>
    exists (ma : m A) (kb : A -> m B),
      Monad.eqm mb (bind ma kb) /\
      (PA) ma /\
      (Functor.fmap kb ma) ∈ (Functor.fmap K ma).

  Global Instance Monad_PropT : Monad (PropT) :=
    {|
      ret:= @ret_f
      ; bind := bind_f'
    |}.

  Ltac eq_hyp_specialize :=
    repeat match goal with
    | [H0 : forall (x : m ?A), ?b x -> _ , H' : m ?A |- _] =>
      remember H' as e;
        match goal with
          | [H : b e |- _] =>
      specialize (H0 _ H); edestruct H0 as (? & ? & ?); clear H0; subst
        end
            end.

  Global Instance EqmR_OK_PropT : @EqmR_OK PropT EqmR_PropT.
  split.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT. intros RR.
    split; intros mx ; exists mx; split; try assumption; try reflexivity.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR. split; red; intros ma H1.
    + destruct H as (HL & HR).
      apply HR in H1.  destruct H1 as (mb & MB & MB').
      exists mb. split. assumption.
      pose proof eqmR_lift_transpose.
      symmetry in H. apply H. assumption.
      symmetry. apply MB'.
    + destruct H as (HL & HR).
      apply HL in H1.  destruct H1 as (mb & MB & MB').
      exists mb. split. assumption. symmetry.
      apply eqmR_lift_transpose. assumption. unfold transpose.
      assumption.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR. repeat intro.
    destruct H0 as (HL & HR).
    destruct H as (KL & KR).
    repeat red in KL, KR, HL, HR.
    split.
    + repeat red. intros ma H.
      eq_hyp_specialize.
      exists x1. split. assumption.
      etransitivity; eassumption.
    + repeat red. intros ma H.
      eq_hyp_specialize.
      exists x2. split. assumption.
      etransitivity; eassumption.
  - intros A B C R1 R2 a b c EQ EQ'.
    unfold eqmR, EqmR_PropT, eqm_PropT in *.
    destruct EQ as (HL & HR).
    destruct EQ' as (KL & KR).
    repeat red in HL, HR, KL, KR.
    split.
    + repeat red. intros ma H.
      eq_hyp_specialize.
      exists x0. split. assumption.
      eapply eqmR_rel_trans; eassumption.
    + repeat red. intros ma H.
      eq_hyp_specialize.
      exists x1. split. assumption.
      apply eqmR_lift_transpose. (* IY: Why is the typeclass instance not immediately found? *)
      assumption.
      red.
      eapply eqmR_rel_trans. assumption.
      apply eqmR_lift_transpose. assumption. apply H5.
      apply eqmR_lift_transpose. assumption. apply H1.
  - intros A B R. unfold eq_rel. split.
    + repeat red. intros a b EQ. split.
      * destruct EQ.
        repeat red in H, H0.
        intros ma Hb.
        eq_hyp_specialize.
        exists x. split. assumption.
        apply H2.
      * repeat red.
        destruct EQ. repeat red in H, H0.
        intros ma Hb.
        eq_hyp_specialize.
        exists x. split; assumption.
    + repeat red. intros a b EQ. split.
      * repeat red. intros ma H.
        destruct EQ. repeat red in H0, H1.
        eq_hyp_specialize.
        exists x. split; assumption.
      * repeat red. intros ma H. repeat red in EQ.
        repeat red in H0, H1.
        eq_hyp_specialize.
        exists x. split; assumption.
  - intros A B. split; intros.
    + repeat red. split; repeat red.
      * intros ma H'.
        (* IY: This chain of destructs is super cumbersome. Also defeats the
         purpose of notations.. *)
        repeat red in H0, H1, H2.
        destruct H0, H1, H2.
        repeat red in H0, H1, H2, H3, H4, H5.
        eq_hyp_specialize.
        exists x6. split. assumption. rewrite <- H.
        rewrite <- H11. (* IY : ugly rewriting.. Can we get around this?*)
        eassert († eq ≡ eq). { (* IY : Put this in HeterogeneousRelations *)
          repeat red. split; repeat red; intros; eauto.
        }
        rewrite H4 in H7.
        rewrite H7. apply H8.
      * intros ma H'.
        repeat red in H0, H1, H2.
        destruct H0, H1, H2.
        repeat red in H0, H1, H2, H3, H4, H5.
        eq_hyp_specialize.
        exists x6. split. assumption. (* IY : Rewriting under transpose? *)
        apply eqmR_lift_transpose. assumption.
        unfold transpose. rewrite <- H.
        eassert († eq ≡ eq). {
          repeat red. split; repeat red; intros; eauto.
        }
        rewrite <- H11.
        rewrite H3 in H7. rewrite <- H7 in H8.
        pose proof eqmR_lift_transpose. (* Janky transpose rewriting, again. LTac?*)
        symmetry in H13. apply H13 in H8.
        unfold transpose in H8.
        assumption. assumption.
    + repeat red. split; repeat red.
      * intros ma H'.
        (* IY: This chain of destructs is super cumbersome. Also defeats the
         purpose of notations.. *)
        repeat red in H0, H1, H2.
        destruct H0, H1, H2.
        repeat red in H0, H1, H2, H3, H4, H5.
        eq_hyp_specialize.
        eassert († eq ≡ eq). { (* IY : Put this in HeterogeneousRelations *)
          repeat red. split; repeat red; intros; eauto.
        }
        exists x6. split. assumption. rewrite H1 in H11.
        rewrite <- H11.
        rewrite <- H7 in H8.
        rewrite H. assumption.
      * intros ma H'.
        repeat red in H0, H1, H2.
        destruct H0, H1, H2.
        repeat red in H0, H1, H2, H3, H4, H5.
        eq_hyp_specialize.
        exists x6. split. assumption. (* IY : Rewriting under transpose? *)
        apply eqmR_lift_transpose. assumption.
        unfold transpose. rewrite H7.
        rewrite H.
        eassert († eq ≡ eq). {
          repeat red. split; repeat red; intros; eauto.
        }
        rewrite H0 in H11.
        pose proof eqmR_lift_transpose.
        symmetry in H13. apply H13 in H8.
        unfold transpose in H8.
        rewrite H11 in H8. assumption. assumption.
  - intros A B. split.
    destruct H0. repeat red in H0, H1.
    + repeat red. intros.
      eq_hyp_specialize.
      exists x1. split. assumption.
      eapply eqmR_Proper_mono; eassumption.
    + repeat red. intros. destruct H0.
      repeat red in H0, H2.
      eq_hyp_specialize.
      exists x1. split. assumption.
      apply eqmR_lift_transpose. assumption. unfold transpose.
      eapply eqmR_Proper_mono. assumption. eassumption.
      pose proof eqmR_lift_transpose. symmetry in H0.
      apply H0. assumption. assumption.
  Qed.

  Lemma ret_ok : forall (A1 A2 : Type) (RA : A1 -> A2 -> Prop) (a1 : A1) (a2 : A2),
      RA a1 a2 <-> (eqmR RA (ret a1) (ret a2)).
  Proof.
    unfold eqmR, EqmR_PropT.
  Admitted.

  Instance EqmRMonad_PropT : @EqmRMonad PropT _ _.
  Proof.
    pose proof EqmR_OK_PropT.
    constructor; unfold eqmR, EqmR_PropT, eqm_PropT.
    - apply ret_ok.
    -
  Admitted.

End Transformer.
