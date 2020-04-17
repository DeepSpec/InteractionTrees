From ExtLib Require Import
     Structures.Monad.

From Coq Require Import Morphisms
     Program.Equality
     Classes.RelationClasses
     Relation_Definitions
.


From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.HeterogeneousRelations
     Basics.Monad.

From Paco Require Import paco.


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


(* SAZ: TODO: The following lemmas belong in HeterogeneousRelations *)

(* SAZ: There is a conflice between RelationClasses.relation and HeterogeneousRelations.relation *)

  Lemma symmetric_eq_rel_transpose : forall {A} (R : A -> A -> Prop) `{@Symmetric A R},
    eq_rel R (†R).
  Proof.
    intros A R H.
    split.
    - intros x y HR. unfold transpose. symmetry. assumption.
    - intros x y HR. unfold transpose. symmetry. assumption.
  Qed.

  Lemma transpose_compose : forall {A B C} (R1 : relationH A B) (R2 : relationH B C),
      eq_rel † (R2 ∘ R1) ((† R1) ∘ († R2)).
  Proof.
    intros A B C R1 R2.
    split.
    - unfold inclusion. intros x y H.
      red. unfold transpose in H. red in H.
      destruct H as (b & R1b & R2b).
      exists b; auto.
    - unfold inclusion. intros x y H.
      red. unfold transpose in H. red in H.
      destruct H as (b & R1b & R2b).
      exists b; auto.
  Qed.

  Lemma transpose_transpose : forall {A B} (R : relationH A B),
      eq_rel R († † R).
  Proof.
    intros A B R.
    split.
    - unfold subrelationH. unfold transpose. tauto.
    - unfold subrelationH, transpose. tauto.
  Qed. 
  
  Lemma transpose_inclusion : forall {A B} (R1 : relationH A B) (R2 : relationH A B),
      R1 ⊑ R2 <-> († R1 ⊑ † R2).
  Proof.
    intros A B R1 R2.
    split.
    - intros HS.
      unfold subrelationH, transpose in *. eauto.
    - intros HS.
      unfold subrelationH, transpose in *. eauto.
  Qed.

  Lemma transpose_eq : forall A, eq_rel (@eq A) († eq).
  Proof.
    intros A.
    repeat red. split; unfold subrelationH; intros; subst.
    - reflexivity.
    - red in H. auto.
  Qed.
  
  Lemma eq_rel_compose_id_l : forall {A B} (R : relationH A B),
      eq_rel R (eq ∘ R).
  Proof.
    intros A B R.
    repeat red. unfold subrelationH. split; intros.
    repeat red. exists y. tauto. red in H. destruct H as (b & Hb & eq).
    subst; auto.
  Qed.

  Lemma eq_rel_compose_id_r : forall {A B} (R : relationH A B),
      eq_rel R (R ∘ eq).
  Proof.
    intros A B R.
    repeat red. unfold subrelationH. split; intros.
    repeat red. exists x. tauto. red in H. destruct H as (b & Hb & eq).
    subst; auto.
  Qed.

  Global Instance transpose_Proper :forall A B, Proper (@eq_rel A B ==> eq_rel) (@transpose A B).
  Proof.
    intros A B R1 R2 (Hab & Hba).
    split.
    - apply transpose_inclusion in Hab. assumption.
    - apply transpose_inclusion in Hba. assumption.
  Qed.
    
  
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
    intros RR PA PB (Hab & Hba). split; red; intros ma Hma.
    + apply Hba in Hma.  destruct Hma as (mb & MB & MB').
      exists mb. split. assumption. rewrite <- symmetric_eq_rel_transpose in MB'; auto.
    + apply Hab in Hma.  destruct Hma as (mb & MB & MB').
      exists mb. split. assumption. rewrite <- symmetric_eq_rel_transpose; auto.
  - intros A R. unfold eqmR, EqmR_PropT, eqm_PropT.
    intros RR PA PB PC (Hab & Hba) (Hbc & Hcb). split; red; intros ma Hma.
    + apply Hab in Hma. destruct Hma as (mb & Hmb & EQab).
      apply Hbc in Hmb. destruct Hmb as (mc & Hmc & EQbc).
      exists mc. split. assumption. eapply transitivity; eassumption.
    + apply Hcb in Hma. destruct Hma as (mb & Hmb & EQab).
      apply Hba in Hmb. destruct Hmb as (mc & Hmc & EQbc).
      exists mc. split. assumption. eapply transitivity; eassumption.
  - intros A B C R1 R2 PA PB PC (Sab & Sba) (Sbc & Scb).
    unfold eqmR, EqmR_PropT, eqm_PropT in *. 
    split.
    + intros ma Hma.
      apply Sab in Hma. destruct Hma as (mb & Hmb  & EQab).
      apply Sbc in Hmb. destruct Hmb as (mc & Hmc & Eqbc).
      exists mc. split. assumption. eapply eqmR_rel_trans; eauto.
    + intros mc Hmc.
      apply Scb in Hmc. destruct Hmc as (mb & Hmb  & EQcb).
      apply Sba in Hmb. destruct Hmb as (ma & Hma & Eqba).
      exists ma. split. assumption.
      rewrite transpose_compose.
      eapply eqmR_rel_trans; eauto.
  - intros A B R.
    unfold eqmR, EqmR_PropT, eqm_PropT.

    split.
    + intros PB PA (Hba & Hab).
      red. split.
      * intros ma Hma.
        apply Hab in Hma. destruct Hma as (mb & Hmb & EQab).
        exists mb. split. assumption.  rewrite <- transpose_transpose in EQab. assumption.
      * intros mb Hmb.
        apply Hba in Hmb. destruct Hmb as (ma & Hma & EQba).
        exists ma. split. assumption. assumption.
    + intros PB PA (Hab & Hba).
      split.
      * intros mb Hmb.
        apply Hba in Hmb. destruct Hmb as (ma & Hma & EQba).
        exists ma. split. assumption. assumption.
      * intros ma Hma.
        apply Hab in Hma. destruct Hma as (mb & Hmb & EQab).
        exists mb. split. assumption.  rewrite <- transpose_transpose. assumption.

  - intros A B.
    repeat red.
    intros R1 R2 EQR PA1 PA2 (Ha1 & Ha2) PB1 PB2 (Hb1 & Hb2).
    split.
    + intros (Hab & Hba).
      split.
      * intros ma2 Hma2.
        apply Ha2 in Hma2. destruct Hma2 as (ma1 & Hma1 & EQab).
        apply Hab in Hma1. destruct Hma1 as (mb1 & Hmb1 & EQa1b).
        apply Hb1 in Hmb1. destruct Hmb1 as (mb2 & Hmb2 & EQb1b).
        exists mb2. split. assumption. rewrite <- EQR.
        rewrite (@eq_rel_compose_id_r _ _ R1).
        eapply eqmR_rel_trans. assumption. rewrite <- transpose_eq in EQab. apply EQab.
        rewrite (@eq_rel_compose_id_l _ _ R1).
        eapply eqmR_rel_trans; eauto.
      * intros mb2 Hmb2.
        apply Hb2 in Hmb2. destruct Hmb2 as (mb1 & Hmb1 & EQb1b).
        apply Hba in Hmb1. destruct Hmb1 as (ma1 & Hma1 & EQb1a).
        apply Ha1 in Hma1. destruct Hma1 as (ma2 & Hma2 & EQa1a).
        exists ma2. split. assumption. rewrite <- EQR.
        rewrite <- transpose_eq in EQb1b.
        rewrite (@eq_rel_compose_id_r _ _ († R1)).
        eapply eqmR_rel_trans. assumption. apply EQb1b.
        rewrite (@eq_rel_compose_id_l _ _ († R1)).
        eapply eqmR_rel_trans; eauto.
   +  intros (Hab & Hba).
      split.
      * intros ma1 Hma1.
        apply Ha1 in Hma1. destruct Hma1 as (ma2 & Hma2 & EQab).
        apply Hab in Hma2. destruct Hma2 as (mb2 & Hmb2 & EQa2b).
        apply Hb2 in Hmb2. destruct Hmb2 as (mb1 & Hmb1 & EQb1b).
        exists mb1. split. assumption. rewrite EQR.
        rewrite (@eq_rel_compose_id_r _ _ R2).
        eapply eqmR_rel_trans. assumption. apply EQab. rewrite <- transpose_eq in EQb1b. 
        rewrite (@eq_rel_compose_id_l _ _ R2).
        eapply eqmR_rel_trans; eauto.
      * intros mb1 Hmb1.
        apply Hb1 in Hmb1. destruct Hmb1 as (mb2 & Hmb2 & EQb2b).
        apply Hba in Hmb2. destruct Hmb2 as (ma2 & Hma2 & EQb2a).
        apply Ha2 in Hma2. destruct Hma2 as (ma1 & Hma1 & EQa1a).
        exists ma1. split. assumption. rewrite EQR.
        rewrite <- transpose_eq in EQa1a.
        rewrite (@eq_rel_compose_id_r _ _ († R2)).
        eapply eqmR_rel_trans. assumption. apply EQb2b.
        rewrite (@eq_rel_compose_id_l _ _ († R2)).
        eapply eqmR_rel_trans; eauto.

  - intros A B.   unfold eqmR, EqmR_PropT, eqm_PropT in *.
    repeat red.
    intros R1 R2 HS PA PB (Hab & Hba).
    split.
    + intros ma Hma.
      apply Hab in Hma. destruct Hma as (mb & Hmb & EQab).
      exists mb. split. assumption. eapply eqmR_Proper_mono; eauto.
    + intros mb Hmb.
      apply Hba in Hmb. destruct Hmb as (ma & Hma & EQba).
      exists ma. split. assumption. eapply eqmR_Proper_mono. assumption.
      2: apply EQba. specialize (transpose_inclusion R1 R2).
      intros H. apply H. assumption.

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
  

      match goal with
        | |- eqmR ?P ?C1 ?C2 => generalize (eqmR_Proper_bind m eq P)
        end.
        
        

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
        eqm ma (bind mb k) -> impure ma -> (forall (v:B), mayRet B mb v -> impure (k v)))
    /\ impure ma.
                                                 
  

(*  ------------------------------------------------------------------------- *)
(*
   Misc. notes from discussion:
             
  (* Class Triggerable (M : (Type -> Type) -> Type -> type := *)
  (*                            { trigger : forall E, E ~> M E }. *)


  monadic_cases : forall (ma : m A),
        (exists B, (p : m B) (k : B -> m A), impure p /\ eqm ma (bind p k))
      \/ exists (a:A), eqm ma (ret a).

                           

        Diverges m := eqmR (fun a b => False) m m
        Halts m := exists k1 k2 : A -> m bool, ~ eqm (bind m k1) (bind m k2)
        Fails m := forall k, eqm m (bind m k)
*)        
        { admit. }

  
  
