(* begin hide *)
From Coq Require Import
     Ensembles
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.Monad.

Import ITree.Basics.Basics.Monads.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.

Section prop.
  Global Instance Monad_Prop : Monad Ensemble :=
    {|
    ret := fun _ x y => x = y;
    bind := fun _ _ Pa K b => exists a, In _ Pa a /\ In _ (K a) b
    |}.

  Global Instance Eq1_Prop : Eq1 Ensemble := Same_set.

  Global Instance Eq1Equivalence_Prop : Eq1Equivalence Ensemble.
  Proof.
    constructor.
    - split; repeat intro; auto.
    - repeat intro. destruct H. split; auto.
    - repeat intro. destruct H, H0. split; repeat intro; auto.
  Qed.

  Instance MonadLawsE_Prop : MonadLawsE Ensemble.
  Proof.
    constructor.
    - split; repeat intro; simpl in *.
      + destruct H as (? & ? & ?). red in H. subst; auto.
      + eexists; split; eauto. reflexivity.
    - split. repeat intro; simpl in *.
      + destruct H as (? & ? & ?). red in H0; subst; auto.
      + red. repeat intro. eexists; split; eauto. reflexivity.
    - intros; split; repeat intro; simpl in *;
        [destruct H as (? & (? & ? & ?) & ?) | destruct H as (? & ? & (? & ? & ?))];
        do 2 (eexists; split; eauto).
    - repeat intro; auto. destruct H.
      split; simpl; repeat red; intros;
        destruct H2 as (? & ? & ?); eexists; split; eauto; apply H0; auto.
  Qed.

  Global Instance Proper_Iter_stateTM : forall a b,
      @Proper (Kleisli Ensemble a (a + b) -> (Kleisli Ensemble a b)) (eq2 ==> eq2) iter.
  Proof.
    repeat red; split; repeat intro;
      (induction H0; [constructor 1 | econstructor 2; eauto]; apply H; auto).
 Qed.

  Global Instance IterUnfold_Prop : IterUnfold (Kleisli Ensemble) sum.
  Proof.
    repeat red; split; repeat intro.
    - repeat red in H |- *. destruct H.
      + exists (inr x). split; repeat red; auto.
      + eexists; split; eauto.
    - repeat red in H |- *. decompose [ex and] H; clear H. destruct x0.
      + econstructor 2; eauto.
      + constructor 1. repeat red in H2. subst; auto.
  Qed.

  Global Instance IterNatural_Prop : IterNatural (Kleisli Ensemble) sum.
  Proof.
    repeat red; split; repeat intro.
    - repeat red in H |- *. decompose [ex and] H; clear H. induction H1.
      + constructor 1. eexists; split; eauto. eexists; split; eauto. reflexivity.
      + econstructor 2; repeat red; eauto.
        eexists; split; eauto. eexists; split; reflexivity.
    - repeat red in H |- *.
      induction H; repeat red in H; decompose [ex and] H; clear H.
      + destruct x; destruct H2 as (? & ? & H'); inversion H'; subst.
        eexists; split; eauto. constructor 1. auto.
      + destruct x; destruct H3 as (? & ? & H'); inversion H'; clear H'; subst.
        decompose [ex and] IHiter_Prop; clear IHiter_Prop.
        inversion H; clear H; subst.
        eexists; split; eauto. econstructor 2; eauto.
  Qed.

  Global Instance IterDinatural_Prop : IterDinatural (Kleisli Ensemble) sum.
  Proof.
    repeat red; split; repeat intro.
    - induction H; destruct H as (? & ? & ?).
      + destruct x; repeat red in H0.
        * eexists; split; eauto. constructor; auto. eexists; split; eauto. reflexivity.
        * inversion H0; subst. eexists; split; eauto. constructor; auto.
      + destruct x; repeat red in H1; try inversion H1.
        destruct IHiter_Prop as (? & ? & ?). destruct x; eexists; split; eauto.
        * econstructor 2; eauto. eexists; split; eauto.
        * repeat red in H3. subst. repeat red. constructor 1. eexists; split; eauto.
    - destruct H as (? & ? & ?). destruct x0; repeat red in H0.
      + generalize dependent a0. induction H0; intros; destruct H as (? & ? & ?).
        * destruct x.
          -- econstructor 2; eauto. eexists; split; eauto.
             constructor 1. eexists; split; eauto. reflexivity.
          -- inversion H1; clear H1; subst. constructor 1. eexists; split; eauto.
        * destruct x; try inversion H2.
          econstructor 2; eauto. 2: { apply IHiter_Prop. apply H2. }
          eexists; split; eauto.
      + subst. constructor 1. eexists; split; eauto. reflexivity.
  Qed.

  Global Instance IterCodiagonal_stateTM : IterCodiagonal (Kleisli Ensemble) sum.
  Proof.
    repeat red; split; repeat intro.
    - induction H.
      + remember (inr r). generalize dependent r. induction H; intros; subst.
        * constructor 1. eexists; split; eauto; reflexivity.
        * econstructor 2. 2: { apply IHiter_Prop; auto. }
          eexists; split; eauto; reflexivity.
      + remember (inl i'). generalize dependent i'. induction H; intros; subst.
        * econstructor 2; eauto. eexists; split; eauto; reflexivity.
        * econstructor 2. 2: { eapply IHiter_Prop; eauto. }
          eexists; split; eauto; reflexivity.
    - induction H.
      + destruct H as (? & ? & ?). destruct x as [? | [? | ?]]; inversion H0; clear H0; subst.
        constructor 1. constructor 1. auto.
      + destruct H as (? & ? & ?).
        destruct x as [? | [? | ?]]; inversion H1; clear H1; subst.
        * destruct IHiter_Prop.
          -- constructor 1. econstructor 2; eauto.
          -- econstructor 2; eauto. econstructor 2; eauto.
        * econstructor 2; eauto. constructor 1. apply H.
  Qed.

  Global Instance Iterative_Prop : Iterative (Kleisli Ensemble) sum.
  Proof.
    constructor; typeclasses eauto.
  Qed.

End prop.
