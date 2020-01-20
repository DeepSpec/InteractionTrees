From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac clear_ret_eutt_spin :=
  match goal with | H : ret ?a ≈ spin  |- _ => simpl in H; exfalso; eapply not_ret_eutt_spin; eauto
             | H : Ret ?a ≈ spin  |- _ => exfalso; eapply not_ret_eutt_spin; eauto
             | H : spin ≈ ret ?a  |- _ => exfalso; symmetry in H; eapply not_ret_eutt_spin; eauto
             | H : divergence (ret _ ) |- _ => pinversion H
  end.
  
Ltac invert_evidence :=
  intros; repeat match goal with 
                 | H : _ /\ _ |- _ => destruct H
                 | H : _ \/ _ |- _ => destruct H 
                 | H : exists a : ?A, _ |- _ => destruct H as [?a ?H]
                 | x : ?A + ?B |- _ => destruct x as [?a | ?b]
                 | H : upaco1 _ _ _ |- _ => pclearbot
                 end.

Ltac invert_ret := simpl in *; match goal with | H : Ret ?a ≈ Ret ?b |- _ => 
                                                 apply inv_ret in H; try discriminate; try (injection H as H);
                                                 subst end.


Ltac basic_solve := invert_evidence; try clear_ret_eutt_spin; try invert_ret.

Ltac dest_dep f a := destruct (f a) as [?fa ?Hfa] eqn : ?Heq; simpl in *.


Notation "a ∈ b" := (proj1_sig b a) (at level 70). 

Notation "a ∋ b" := (proj1_sig a b) (at level 70).

Definition Delay (A : Type) := itree Void A.

Global Instance EqMDelay : EqM Delay := @ITreeMonad.EqM_ITree Void.

Global Instance MonadDelay : Monad Delay := @Monad_itree Void.

Definition DelaySpecInput (A : Type) := {p : Delay A -> Prop | resp_eutt _ _ p}.

Definition DelayIn {A : Type} (t : Delay A) (p : DelaySpecInput A) := proj1_sig p t.

Definition DelaySpec (A : Type) := {w : DelaySpecInput A -> Prop | forall (p p' : DelaySpecInput A),
                                   (forall t, t ∈ p -> t ∈ p') -> w p -> w p'}.

Program Definition ret_del (A : Type) (a : A) : DelaySpec A := fun p => p (Ret a).


Program Definition _bind_del (A B : Type) (w : DelaySpec A) (f : A -> DelaySpec B):=
  fun p => w ∋ (fun t => (exists a, Ret a ≈ t /\ p ∈ f a) \/ (divergence t /\ p spin)).
Next Obligation.
  intros t1 t2 Heutt. split; intros; basic_solve.
  - left. exists a. split; auto. rewrite H. auto.
  - right. rewrite <- Heutt. auto.
  - left. exists a. rewrite Heutt. auto.
  - right. rewrite Heutt. auto.
Qed.

Program Definition bind_del (A B : Type) (w : DelaySpec A) (f : A -> DelaySpec B) : DelaySpec B :=
  _bind_del A B w f.
Next Obligation.
  red. red in H0. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H0.
  simpl. intros. basic_solve.
  - left. exists a. split; auto. dest_dep f a. eapply Hfa; eauto.
  - right. split; auto.
Qed.

Global Instance DelaySpecEq : EqM DelaySpec :=
  fun _ w1 w2 => forall p, p ∈ w1 <-> p ∈ w2.

Global Instance DelaySpecMonad : Monad DelaySpec :=
  {
    ret := ret_del;
    bind := bind_del
  }.

Program Instance DelaySpecMonadLaws : MonadLaws DelaySpec.
Next Obligation.
  repeat red. cbn. split; intros; basic_solve; auto.
  - pinversion H.
  - left. exists x. split; auto; reflexivity.
Qed.
Next Obligation.
  rename a into A.
  rename x into w.
  repeat red. cbn. split; intros.
  - red in H. simpl in H. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H.
    intros. simpl in *. destruct p as [p Hp]. simpl in *. basic_solve.
    +  eapply Hp; eauto. symmetry. auto.
    + apply div_spin_eutt in H0. eapply Hp; eauto.
  - red. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H. intros.
    destruct p as [p Hp]. simpl in *.
    destruct (eutt_reta_or_div _ t); basic_solve. 
    + left. exists a. split; auto. eapply Hp; eauto.
    + right. split; auto. eapply Hp; try apply H0. symmetry. apply div_spin_eutt. auto.
Qed.
Next Obligation.
  rename a into A. rename b into B. rename c into C. rename x into w.
  repeat red. cbn. split; intros. 
  - red. red in H. destruct w as [w Hw]. simpl in *. destruct p as [p Hp]. simpl in *.
    eapply Hw; try apply H. intros. simpl in *. clear H. basic_solve.
    + left. exists a. auto.
    + right. auto.
  - red. red in H. destruct w as [w Hw]. simpl in *. destruct p as [p Hp]. simpl in *.
    eapply Hw; try apply H. simpl in *. intros. basic_solve.
    + left. exists a. auto.
    + right. split; auto. right. split; try auto using spin_div.
Qed.

Global Instance DelaySpecOrderM : OrderM DelaySpec :=
  fun _ w1 w2 => forall p, p ∈ w2 -> p ∈ w1.

Global Instance DelaySpecOrder : OrderedMonad DelaySpec.
Proof.
  red. intros. repeat red. cbn. destruct w1 as [w1 Hw1]. destruct w2 as [w2 Hw2].
  intros. simpl in *. apply H. simpl in *. eapply Hw2; try apply H1. simpl in *. intros.
  basic_solve.
  - left. exists a. split; auto. apply H0. auto.
  - right. auto.
Qed.

Program Definition obs_del (A : Type) (t : Delay A) : DelaySpec A := fun p => t ∈ p.

Global Instance DelaySpecObs : EffectObs Delay DelaySpec := obs_del.

Global Instance DelaySpecMonadMorph : MonadMorphism Delay DelaySpec DelaySpecObs.
Proof.
  constructor.
  - repeat red. cbn. tauto.
  - repeat red. cbn. split; intros; basic_solve.
    + destruct (eutt_reta_or_div _ m); basic_solve.
      * left. exists a. split; auto. destruct p as [p Hp]. simpl in *. eapply Hp; try apply H.
        rewrite <- H0. setoid_rewrite bind_ret. reflexivity.
      * right. split; auto. apply div_spin_eutt in H0. destruct p as [p Hp]. eapply Hp; try apply H.
        rewrite H0. apply spin_bind.
    + destruct p as [p Hp]. simpl in *. eapply Hp; try apply H0. rewrite <- H. setoid_rewrite bind_ret. reflexivity.
    + apply div_spin_eutt in H. destruct p as [p Hp]. simpl in *. eapply Hp; try apply H0. rewrite H. 
      symmetry. apply spin_bind.
Qed.
