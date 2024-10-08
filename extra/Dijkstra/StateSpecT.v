From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Data.Monads.StateMonad
     Structures.Monad.

From Paco Require Import paco.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Props.Infinite.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad.

Import Monads.
Import MonadNotation.

#[local] Open Scope monad_scope.
#[local] Open Scope dijkstra_scope.
#[local] Open Scope delayspec_scope.

Section StateSpecT.
  Context (S : Type).
  Context (W : Type -> Type).
  Context {MonadW : Monad W}.
  Context {OrderW : OrderM W}.
  Context {OrderedMonadW : OrderedMonad W}.
  Context {EqW : Eq1 W}.
  Context {EquivRel : forall A, Equivalence (eq1 (A := A)) }.
  Context {MonadLawsW : MonadLawsE W}.

  Definition StateSpecT (A : Type) := stateT S W A.

  #[global] Instance Monad_StateSpecT : Monad StateSpecT := Monad_stateT S MonadW.

  #[global] Instance StateSpecTOrder : OrderM StateSpecT :=
    fun A (w1 w2 : stateT S W A) => forall (s : S), runStateT w1 s <≈ runStateT w2 s.

  #[global] Instance StateSpecTOrderedLaws : OrderedMonad StateSpecT.
  Proof.
    destruct OrderedMonadW.
    constructor.
    - repeat intro.  auto.
    - repeat intro. eapply trans; eauto.
    - intros A B w1 w2 f1 f2 Hlw Hlf. unfold StateSpecT in *.
      repeat red.
      intros. apply monot; auto. intros. destruct a as [s' a]. simpl.
      repeat red in Hlf. apply Hlf.
  Qed.

  #[global] Instance StateSpecTEq : Eq1 StateSpecT := Eq1_stateTM W S.

  #[global] Instance StateSpecTMonadLaws : @MonadLawsE StateSpecT (Eq1_stateTM W S) _ :=
    @MonadLawsE_stateTM W S _ _ EquivRel MonadLawsW.

  Section Observation.
    Context (M : Type -> Type).
    Context {MonadM : Monad M}.
    Context {EffectObsMW : EffectObs M W}.
    Context {MonadMorphismMW : MonadMorphism M W EffectObsMW}.

    #[global] Instance EffectObsStateT : EffectObs (stateT S M) (stateT S W) :=
      fun T (m : stateT S M T) => mkStateT (fun s => obs _ (runStateT m s)).

    #[global] Instance MonadMorphismStateT : MonadMorphism (stateT S M) (stateT S W) EffectObsStateT.
    Proof.
      destruct MonadMorphismMW.
      constructor.
      - intros. repeat red. intros. specialize (ret_pres (A * S)%type (a,a0)).
        cbn. rewrite <- ret_pres. reflexivity.
      - intros. repeat red. intros. cbn. specialize (bind_pres (A * S)%type (B * S)%type).
        rewrite bind_pres.
        apply Proper_bind.
        + reflexivity.
        + intros []. reflexivity.
    Qed.

  End Observation.

  (*Can I encode a pre post thing, state spec enriches the precondition and
     specializes post condition*)

  (*maybe I need a computational monad M with a monad iter structure,
    I think the taus only showed up because I was using hte monad iter structure
    of strong bisimulation not weak,
    also note that this loop invar stuff, while relevant to D monads, is not
    itself of D monads
   *)

End StateSpecT.

Section LoopInvarSpecific.
  Context (S : Type).

  Definition StateSpec (A : Type) := StateSpecT S DelaySpec A.

  Definition State (A : Type) := stateT S Delay A.

  Instance StateIter : MonadIter State := MonadIter_stateT.

  Definition reassoc {A B : Type} (t : Delay ((A + B) * S)) : Delay ((A * S) + (B * S)) :=
    t >>= (fun '(ab,s) =>
             match ab with
             | inl a => ret (inl (a,s))
             | inr b => ret (inr (b,s))
             end
).

  Definition iso_arrow {A B : Type} (f : A -> State B) (g : (A * S) -> Delay (B * S)) :=
    forall (a : A) (s : S), runStateT (f a) s ≈ g (a,s).

  Definition decurry_flip {A B C : Type} (f : A -> B -> C) : B * A -> C :=
    fun '(b,a) => f a b.

  (*this is just decurry*)
  Definition iso_destatify_arrow {A B : Type} (f : A -> State (A + B) ) : (A * S) -> Delay ((A * S) + (B * S)) :=
    fun '(a,s) => reassoc (runStateT (f a) s).

  (*should be able to use original*)
  Lemma loop_invar_state: forall (A B : Type) (g : A -> State (A + B)) (a : A) (s : S)
               (p : Delay (B * S) -> Prop) (q : Delay ((A * S) + (B * S))  -> Prop  )
               (Hp : resp_eutt p) (Hq : resp_eutt q) ,
        (q (reassoc (runStateT (g a) s) )) ->
        (q -+> p) -> (forall t, q t -> q (t >>= (iter_lift ( iso_destatify_arrow g)  ))) ->
         (p \1/ any_infinite) (runStateT (MonadIter_stateT _ _ g a) s) .
  Proof.
    intros.
    set (iso_destatify_arrow g) as g'.
    enough ((p \1/ any_infinite) (ITree.iter g' (a,s) )).
    - assert (ITree.iter g' (a,s) ≈ runStateT (iter g a) s).
      + unfold g', iso_destatify_arrow.
        unfold iter, Iter_Kleisli, Basics.iter, MonadIterDelay, StateIter,
        MonadIter_stateT, reassoc. unfold Basics.iter.
        unfold MonadIterDelay. eapply eutt_iter. intro.
        destruct a0 as [a' s']. simpl.
        eapply eutt_clo_bind; try reflexivity. intros.
        subst. destruct u2. simpl. destruct s0; reflexivity.
      + assert (Hpdiv : resp_eutt (p \1/ any_infinite)).
        { intros t1 t2 Heutt. split; intros; basic_solve.
          - left. eapply Hp; eauto. symmetry. auto.
          - right. rewrite <- Heutt. auto.
          - left. eapply Hp; eauto.
          - right. rewrite Heutt. auto.
         }
        eapply Hpdiv; try apply H2. symmetry. auto.
     - eapply loop_invar; eauto.
  Qed.

  Definition state_iter_arrow_rel {A B S : Type} (g : A -> stateT S Delay (A + B) ) '(a0,s0) '(a1,s1) :=
    runStateT (g a0) s0 ≈ Ret (inl a1, s1).

  Locate not_wf.

  Lemma iter_inl_spin_state : forall (A B S : Type) (g : A -> stateT S Delay (A + B) ) (a : A) (s : S),
      not_wf_from (state_iter_arrow_rel g ) (a,s) -> runStateT (MonadIter_stateT _ _  g a) s ≈ ITree.spin.
  Proof.
    intros. unfold MonadIter_stateT.
    apply iter_inl_spin. (*seems to require some coinduciton*)
    generalize dependent a. generalize dependent s.
    pcofix CIH. intros. pinversion H0; try apply not_wf_F_mono'. pfold.
    apply not_wf with (a' := a'); eauto.
    - red in Hrel. destruct a' as [s' a']. simpl. red. simpl. rewrite Hrel.
      rewrite bind_ret_l. simpl. reflexivity.
    - right. destruct a'. eauto.
  Qed.

  Lemma iter_wf_converge_state : forall (A B S : Type)  (g : A -> stateT S Delay (A + B) ) (a : A) (s : S),
      (forall a s, exists ab, runStateT (g a) s ≈ Ret ab) ->
      wf_from (state_iter_arrow_rel g) (a,s) ->
      exists (p : B * S), runStateT (MonadIter_stateT _ _ g a) s ≈ Ret p.
  Proof.
    intros. unfold MonadIter_stateT, Basics.iter, MonadIterDelay.
    apply iter_wf_converge.
    - eapply wf_from_sub_rel; try apply H0.
      repeat intro. unfold iter_arrow_rel in *. unfold state_iter_arrow_rel.
      clear H0 a s.
      destruct x as [a s]. simpl in *. destruct y as [a' s'].
      destruct (eutt_reta_or_div (runStateT (g a) s)); basic_solve.
      + rewrite <- H0. rewrite <- H0 in H1. simpl in H1. rewrite bind_ret_l in H1.
        simpl in *. destruct a0. simpl in *. destruct s0; basic_solve.
        reflexivity.
      + apply div_spin_eutt in H0. rewrite H0 in H1. rewrite <- spin_bind in H1.
        symmetry in H1. exfalso. eapply not_ret_eutt_spin; eauto.
   - clear H0 a s. intros [a s]. specialize (H a s). basic_solve.
     destruct ab as [[a' | b] s'].
     + exists (inl (a',s')). simpl. rewrite H. rewrite bind_ret_l. simpl.
       reflexivity.
     + exists (inr (b,s')). simpl. rewrite H. rewrite bind_ret_l. simpl.
       reflexivity.
  Qed.

End LoopInvarSpecific.
