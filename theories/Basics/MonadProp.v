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
      PB [⊆ †R] PA /\
      relatively_closed_by_R_weak R PA PB
  .

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

  Ltac destruct_eq :=
    repeat lazymatch goal with
    | [ H : eqmR _ _ _ |- _ ] => repeat red in H
    | [ H : _ /\ _ /\ _ |- _ ] => destruct H as (? & ? & ?)
    | [ H : _ [⊆ _] _, H' : _ [⊆† _] _ |- _] => repeat red in H, H'
    end.

  Ltac eq_hyp_specialize :=
    repeat match goal with
       | [H0 : forall (x : m ?A), ?b x -> _ , H' : m ?A |- _] => remember H' as e;
          match goal with
          | [H : b e |- _] => specialize (H0 _ H);
                            edestruct H0 as (? & ? & ?); clear H0; subst
          end
      end
  .

  Ltac match_goal_prop :=
    match goal with
      [ H : ?z ?mb |- exists _, ?z _ /\ _ ] => exists mb; split; [ assumption | ]
    end.

  Tactic Notation "rewrite_transpose_l" "in" hyp (H) :=
    pose proof eqmR_lift_transpose as tr;
    symmetry in tr; apply tr in H; clear tr; unfold transpose in H.

  Ltac rewrite_transpose_l :=
    pose proof eqmR_lift_transpose as tr;
    symmetry in tr; apply tr; clear tr; unfold transpose.

  Ltac rewrite_eq_rel :=
    match goal with
    | [H : ?x ≡ ?y |- eqmR ?x _ _ ] => rewrite H
    | [H : ?x ≡ ?y |- eqmR ?y _ _ ] => rewrite <- H
    end.

  Ltac try_eqmR_solve :=
    destruct_eq; eq_hyp_specialize; try match_goal_prop; try rewrite_eq_rel.

  Ltac rewrite_eqm_eq :=
    match goal with
    | [H : eqmR eq ?ma _ |- eqmR _ ?ma _ ] => rewrite H
    | [H : eqmR eq _ ?ma |- eqmR _ ?ma _ ] => rewrite <- H
    | [H : eqmR eq ?ma _ |- eqmR _ _ ?ma ] => rewrite H
    | [H : eqmR eq _ ?ma |- eqmR _ _ ?ma ] => rewrite <- H
    end.

  Global Instance EqmR_OK_PropT : @EqmR_OK PropT EqmR_PropT.
  Proof with eauto.
  split.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT. intros RR.
    constructor; [ | split ].
    intros mx ; exists mx; split; try assumption; try reflexivity.
    repeat intro. exists ma. split... reflexivity.
    red. intros ma ma' EQ H H'. split.
    + intros ma'' EQ'. admit.
    + admit.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR. split; [ | split]; red; intros ma H1.
    + try_eqmR_solve.
      rewrite_transpose_l in H4. symmetry... assumption.
    + try_eqmR_solve.
      symmetry.
      apply eqmR_lift_transpose...
    + admit.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR. repeat intro.
    split; [ | split]; [ | | shelve ]; repeat red; intros ma H';
    try_eqmR_solve; etransitivity...
  - intros A B C R1 R2 a b c EQ EQ'.
    unfold eqmR, EqmR_PropT, eqm_PropT in *.
    split; [ | split]; [ | | shelve]; repeat red; intros ma H; try_eqmR_solve...
    + eapply eqmR_rel_trans...
    + apply eqmR_lift_transpose. (* IY: Why is the typeclass instance not immediately found? *)
      assumption.
      red.
      eapply eqmR_rel_trans. assumption.
      apply eqmR_lift_transpose...
      apply eqmR_lift_transpose...
  - intros A B R. unfold eq_rel. split; repeat red; intros a b EQ.
    + split ; [ | split]; [ | | shelve];
      intros ma H; repeat red in EQ; try_eqmR_solve...
    + split; [ | split]; [ | | shelve];
      intros ma H; repeat red in EQ; try_eqmR_solve...
  - intros A B. split; intros; repeat red.
    + repeat red. split; [ | split ]; [ | | shelve]; repeat red;
      intros ma H'; try_eqmR_solve.
      * rewrite <- H14.
        rewrite transpose_sym in H10.
        rewrite H10...
        typeclasses eauto. (* Why does this get generated? *)
      * rewrite transpose_sym in H10.
        rewrite H10. (* IY : ugly rewriting.. Can we get around this?*)
        rewrite_transpose_l...
        rewrite <- H14. setoid_rewrite <- H.
        rewrite_transpose_l in H11...
        eauto.
    + repeat red.
      split; [ | split ]; [ | | shelve];
        repeat red; intros ma H'; try_eqmR_solve.
      * rewrite transpose_sym in H14.
        rewrite <- H14... rewrite_eqm_eq... eauto.
      * rewrite transpose_sym in H14.
        rewrite <- H14. rewrite_transpose_l...
        rewrite H10. rewrite_transpose_l in H11. setoid_rewrite H...
        eauto. eauto.
  - intros A B. split; [ | split]; [| | shelve];
                  repeat red; intros ma H'; try_eqmR_solve.
    + eapply eqmR_Proper_mono; eassumption.
    + apply eqmR_lift_transpose. assumption. unfold transpose.
      eapply eqmR_Proper_mono. assumption. eassumption.
      pose proof eqmR_lift_transpose. symmetry in H0.
      apply H0. assumption. assumption.
  Unshelve.
  Admitted. (* relatively_closed properties. *)

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
