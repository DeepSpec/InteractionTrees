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
  Definition PropT (A:Type) := m A -> Prop. (* { p : (m A -> Prop) | Proper (eqmR eq ==> iff) p}. *)

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
      PB [⊆ †R] PA -> 
      relatively_closed_by_R_weak R PA PB ->
      relatively_closed_by_R R PA PB.
  Proof.
    intros A B R PA PB INA INB REL;
      split; intros.
    - edestruct INA as (x & ? & ?).  eauto. eapply REL; eauto.
    - edestruct INB as (x & ? & ?). eauto.
      assert († (eqmR R) mb x). { apply eqmR_lift_transpose; eauto. }
      red in H3. eapply REL; eauto.
  Qed.

  Definition eqm_PropT : forall (A B : Type) (R: A -> B -> Prop), PropT A -> PropT B -> Prop :=
    fun A B R PA PB =>
      PA [⊆ R] PB /\
      PB [⊆ †R] PA /\
      relatively_closed_by_R_weak R PA PB.

  Global Instance EqmR_PropT : EqmR PropT := {| eqmR := eqm_PropT |}.

  
  (* SAZ: I believe that any "good" definition of eqm_PropT should allow us 
     to prove this lemma: It just says that a "good" PropT predicate respects  
     the underlying monad equivalence.
  *)
  Lemma eqmR_PropT_sane : forall A (R: A -> A -> Prop) (PA : PropT A),
      eqm_PropT A A R PA PA -> Proper (eqmR R ==> iff) PA.
  Proof.
    intros A R PA (INA & INB & REL).
    specialize (relatively_closed_weak_bij_strong _ _ _ INA INB REL) as H.
    apply H.
  Qed.

  
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
    | [ H : _ /\ _ |- _ ] => destruct H as (? & ?)
    | [ H : _ [⊆ _] _ |- _] => repeat red in H
    | [ H : _ [⊆ † _] _ |- _] => repeat red in H
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

  Lemma eqmR_transpose: forall A (R : relationH A A) (ma mb: m A) , eqmR †R ma mb <-> eqmR R mb ma.
  Proof.
    intros A R ma mb.
    split; intros H.
    - assert († (eqmR R) ma mb). apply eqmR_lift_transpose. assumption. assumption.
      apply H0.
    - apply eqmR_lift_transpose; assumption.
  Qed.

  Global Instance EqmR_OK_PropT : @EqmR_OK PropT EqmR_PropT.
  Proof with eauto.
  split.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT. intros RR.
    repeat red.
    intros PA.
    repeat split.
    + intros ma Hma. exists ma. split; try assumption. try reflexivity.
    + intros ma Hma. exists ma. split; try assumption. try reflexivity.
    + intros ma' Hma'. 

                       
                             

      (* SAZ: I'm not sure that we can always show that Reflexivity lifts this way... *)
      (* If we only require eqmR to lift symmetry and transitivity, that might just be enough. *)
      admit.
    + admit.    

  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR. repeat red. intros PA PB (INA & INB & REL).
    repeat split.
    + destruct_eq.
      repeat red. intros ma Hma.
      specialize (INB _ Hma).
      destruct INB as (mb & Hmb & EQ).
      apply eqmR_transpose in EQ.
      exists mb. split. assumption. symmetry. assumption.

    + destruct_eq.
      repeat red. intros ma Hma.
      specialize (INA _ Hma).
      destruct INA as (mb & Hmb & EQ).
      exists mb. split. assumption. symmetry. apply eqmR_transpose. assumption.

    + unfold relatively_closed_by_R_weak in REL.
      intros ma2 H2.
      specialize (REL mb ma).
      assert (eqmR R mb ma). {  symmetry. assumption. }
      specialize (REL H3 H1 H0).
      apply REL. symmetry. assumption.

  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR. repeat intro;
    split; repeat red; intros ma H';
    try_eqmR_solve; etransitivity...
  - intros A B C R1 R2 a b c EQ EQ'.
    unfold eqmR, EqmR_PropT, eqm_PropT in *.
    split; repeat red; intros ma H; try_eqmR_solve...
    + eapply eqmR_rel_trans...
    + apply eqmR_lift_transpose...
      red. rewrite_transpose_l in H7...
      clear H8.
      eapply eqmR_rel_trans...
      apply eqmR_lift_transpose...
  - intros A B R. unfold eq_rel.
    split; repeat red; intros a b EQ; split ;
      intros ma H; repeat red in EQ; try_eqmR_solve...
  - intros A B. split; intros; repeat red.
    + repeat red. split; repeat red;
      intros ma H'; try_eqmR_solve;
      rewrite transpose_sym in H7; eauto; rewrite H7...
      * rewrite <- H11...
      * rewrite_transpose_l...
        rewrite <- H11... setoid_rewrite <- H.
        rewrite_transpose_l in H8...
    + repeat red.
      split; repeat red; intros ma H'; try_eqmR_solve;
        rewrite transpose_sym in H11...
      * rewrite <- H11... rewrite_eqm_eq...
      * rewrite <- H11... rewrite_transpose_l...
        rewrite H7. rewrite_transpose_l in H8... setoid_rewrite H...
  - intros A B. split; repeat red; intros ma H'; try_eqmR_solve.
    + eapply eqmR_Proper_mono; eassumption.
    + apply eqmR_lift_transpose. assumption. unfold transpose.
      eapply eqmR_Proper_mono. assumption. eassumption.
      pose proof eqmR_lift_transpose. symmetry in H0.
      apply H0. assumption. assumption.
 Qed.

  Lemma ret_ok : forall (A1 A2 : Type) (RA : A1 -> A2 -> Prop) (a1 : A1) (a2 : A2),
      RA a1 a2 -> (eqmR RA (ret a1) (ret a2)).
  Proof.
    intros A1 A2 RA a1 a2.
    unfold eqmR, EqmR_PropT, eqm_PropT.
    intros HR. split.
      + intros ma Hma. exists (ret a2). split. repeat red. reflexivity.
        repeat red in Hma.
        rewrite Hma. apply eqmR_ret; assumption.
      + intros ma Hma. exists (ret a1). split. repeat red. reflexivity.
        repeat red in Hma.
        rewrite Hma. apply eqmR_ret; assumption.
  Qed.

  Lemma propT_eqmR_bind_bind : forall {A B C}
                       (RA : A -> A -> Prop)
                       (RB : B -> B -> Prop)
                       (RC : C -> C -> Prop)
                       (f : A -> (PropT B))
                       (f_OK : Proper (RA ==> (eqmR RB)) f)
                       (g : B -> (PropT C))
                       (g_OK : Proper (RB ==> (eqmR RC)) g)
                       (PA : (PropT A))
                       (PA_OK : eqmR RA PA PA),
      eqmR RC (bind (bind PA f) g)  (bind PA (fun y => bind (f y) g)).
  Proof.
    intros A B C RA RB RC f f_OK g g_OK PA PA_OK.
    unfold eqmR, EqmR_PropT, eqm_PropT.
    unfold bind, Monad_PropT.
    split.
    - repeat red. intros mc HB.
      unfold bind_f' in HB.
      destruct HB as (mb & Kbc & EQmc & (ma & Kab & EQma & Hma & HF) & HFfm).
      exists (bind mb Kbc). split.
      repeat red.
      exists ma. exists (fun a => bind (Kab a) Kbc).
      repeat split.
      + rewrite EQma. apply bind_bind.
      + assumption.
      + cbn.
        unfold liftM.
        unfold agrees.
        eapply eqmR_bind_ProperH. assumption.
  Abort.

  Instance EqmRMonad_PropT : @EqmRMonad PropT _ _.
  Proof.
    pose proof EqmR_OK_PropT.
    constructor; unfold eqmR, EqmR_PropT, eqm_PropT.
    - apply ret_ok.
    - 
  Admitted.

End Transformer.


(*
  Possible way to define mayRet based on impurity?
*)

Context {m : Type -> Type}.
Context {M : Monad m}.
Context {E : EqmR m}.
  Definition impure {A} (ma : m A) := ~exists a, eqm ma (ret a).

  Inductive mayRet  : forall A, (m A) -> A -> Prop :=
  | mayRet_ret : forall A (a:A), mayRet A (ret a) a
  | mayRet_bind : forall A B (mb : m B) (k : B -> m A) a b,
      mayRet B mb b -> mayRet A (k b) a -> impure mb ->
      mayRet A (bind mb k) a.

  Definition atomic {A} (ma : m A) :=
    (forall B (mb : m B) (k : B -> m A),
        eqm ma (bind mb k) -> impure mb -> (forall (v:B), mayRet B mb v -> ~impure (k v)))
    /\ impure ma.



(*  ------------------------------------------------------------------------- *)
(*
   Misc. notes from discussion:

  (* Class Triggerable (M : (Type -> Type) -> Type -> type := *)
  (*                            { trigger : forall E, E ~> M E }. *)

  Trying to prove this relation between fmap and mayRet:

     mayRet ma x <->
     mayRet (fmap f ma) (f x)


  Test theorems for the state monad:
  impure (get)
  impure (set 3)
  atomic (get)
  atomic ma -> eqmR eq ma (get) \/ exists x, eqmR ma (set x)

  More general case analysis for monadic compuations:
  monadic_cases : forall (ma : m A),
        (exists B, (p : m B) (k : B -> m A), atomic p /\ eqm ma (bind p k))
      \/ exists (a:A), eqm ma (ret a).



        Diverges m := eqmR (fun a b => False) m m
        Halts m := exists k1 k2 : A -> m bool, ~ eqm (bind m k1) (bind m k2)
        Fails m := forall k, eqm m (bind m k)
*)
