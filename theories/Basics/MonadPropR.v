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
Open Scope relation_scope.

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

  Import RelNotations.
  Global Instance EqmR_OK_PropT : @EqmR_OK PropT EqmR_PropT.
  split.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT. intros RR.
    split; intros mx ; exists mx; split; try assumption; try reflexivity.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR. split; red; intros.
    + destruct H as (HL & HR).
  (*     apply HR in H1.  destruct H1 as (mb & MB & MB'). *)
  (*     exists mb. split. assumption. symmetry. assumption. *)
  (*   + destruct H0 as (HL & HR). *)
  (*     apply HL in H1.  destruct H1 as (ma & MB & MB'). *)
  (*     exists ma. split. assumption. symmetry. assumption. *)
  (* - intros A R. unfold eqmR, EqmR_PropT, eqm'. *)
  (*   intros RR. split; intros. *)
  (*   + destruct H0 as (HL & HR). *)
  (*     destruct H1 as (KL & KR). *)
  (*     apply HL in H2. destruct H2 as (mb & MB & MB'). *)
  (*     apply KL in MB. destruct MB as (mc & MC & MC'). *)
  (*     exists mc. split. assumption. eapply transitivity; eassumption. *)
  (*   + destruct H0 as (HL & HR). *)
  (*     destruct H1 as (KL & KR). *)
  (*     apply KR in H2. destruct H2 as (ma & MA & MA'). *)
  (*     apply HR in MA. destruct MA as (mc & MC & MC'). *)
  (*     exists mc. split. assumption. eapply transitivity; eassumption. *)
  (* - intros A B. *)
  (*   unfold eqmR, EqmR_PropT, eqm'. *)
  (*   repeat red. *)
  (*   intros C R1 R2 EQR PA1 PA2. *)
  (*   intros Htr (MA1 & MB1) (MB2 & MC1). *)
  (*   split. *)
  (*   + intros ma Hma. *)
  (*     specialize (MA1 ma Hma). edestruct MA1 as (mb & HPA1 & EQ). *)
  (*     specialize (MB2 mb HPA1). edestruct MB2 as (mc & HPA2 & EQ'). *)
  (*     exists mc. split. assumption. unfold compose. *)
  (*     epose proof compose_id_l. *)
  (*     epose proof compose_id_r. *)
    (*   specialize (H0 R2). specialize (H1 R2). *)
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
  Admitted.

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
