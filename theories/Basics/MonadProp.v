(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From stdpp Require Import propset.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli.

Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.

Definition subset {A} (P Q : propset A) : Prop :=
  forall x, x ∈ P -> x ∈ Q.

#[global]
Instance Eq1_Prop : Eq1 propset :=
  fun _ P Q => subset P Q /\ subset Q P.

#[global]
Instance Eq1Equivalence_Prop : Eq1Equivalence propset.
Proof.
  constructor.
  - split; repeat intro; auto.
  - repeat intro. destruct H. split; auto.
  - repeat intro. destruct H, H0. split; repeat intro; auto.
Qed.

Section lemmas.

#[local]
Transparent propset_bind.

Lemma unfold_elem_of_mbind {A B} (P : propset A) (Q : A -> propset B) (x : B)
  : x ∈ P ≫= Q -> exists y, y ∈ P /\ x ∈ Q y.
Proof.
  intros H.
  apply (proj1 (elem_of_PropSet _ _)) in H.
  destruct H as [y []]; eauto.
Qed.

Lemma fold_elem_of_mbind {A B} (P : propset A) (Q : A -> propset B) (x : B)
  : (exists y, y ∈ P /\ x ∈ Q y) -> x ∈ P ≫= Q.
Proof.
  intros H.
  apply (proj2 (elem_of_PropSet _ _)).
  destruct H as [y []]; eauto.
Qed.

End lemmas.

Ltac simp_propset :=
  repeat lazymatch goal with
  | [ H : _ ∈ mret ?x |- _ ] =>
      apply (elem_of_PropSet (eq x)) in H;
      tryif is_var x then subst x else idtac
  | [ |- _ ∈ mret ?x ] =>
      apply (proj2 (elem_of_PropSet (eq x) _))
  | [ H : _ ∈ mbind _ _ |- _ ] =>
      apply unfold_elem_of_mbind in H
  | [ |- _ ∈ mbind _ _ ] => apply fold_elem_of_mbind
  | [ H : _ ∈ PropSet _ |- _ ] => rewrite elem_of_PropSet in H
  | [ |- _ ∈ PropSet _ ] => rewrite elem_of_PropSet
  end.

Instance MonadLawsE_Prop : MonadLawsE propset.
Proof.
  constructor.
  - split; intros y HIn.
    + destruct HIn as (? & Hf & Hx). simp_propset; auto.
    + eexists; split; eauto; reflexivity.
  - split. intros y HIn.
    + destruct HIn as (? & Hx & Hy). simp_propset; auto.
    + eexists; split; eauto; reflexivity.
  - intros; split; intros c Hc; simp_propset.
    + destruct Hc as [b [Hb ?]]; simp_propset.
      destruct Hb as [a [Ha ?]].
      exists a; split; [ auto | simp_propset; eauto ].
    + destruct Hc as [a [? Hb]]; simp_propset.
      destruct Hb as [b []].
      exists b; split; [ simp_propset; eauto | auto ].
  - intros A B f1 f2 EQf P1 P2 EQP. split;
      intros x Hx; simp_propset;
      destruct Hx as [y []]; exists y; split;
        apply EQP + apply EQf; auto.
Qed.

#[global]
Instance Proper_Iter_propset : forall a b,
    @Proper (Kleisli propset a (a + b) -> (Kleisli propset a b)) (eq2 ==> eq2) iter.
Proof.
  intros A B P1 P2 EQP x.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_Prop.
  split; intros y Hy;
    apply elem_of_PropSet;
    apply (proj1 (elem_of_PropSet _ _)) in Hy.
  all: induction Hy; [constructor 1 | econstructor 2; eauto]; apply EQP; auto.
Qed.

#[global]
Instance IterUnfold_Prop : IterUnfold (Kleisli propset) sum.
Proof.
  intros A B f x.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_Prop.
  unfold cat, Cat_Kleisli, case_, Case_Kleisli, Function.case_sum.
  unfold id_, Id_Kleisli, pure, id.
  split; intros y Hy; simp_propset.
  - destruct Hy as [ | b ? ? ].
    + exists (inr y); split; auto. simp_propset; auto.
    + exists (inl b); split; auto.
  - destruct Hy as [[a | b] []].
    + econstructor 2; eauto.
    + simp_propset. constructor 1; auto.
Qed.

#[global]
Instance IterNatural_Prop : IterNatural (Kleisli propset) sum.
Proof.
  intros A B C f g x.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_Prop.
  unfold bimap, Bimap_Coproduct, case_, Case_Kleisli, Function.case_sum,
    inl_, Inl_Kleisli, inr_, Inr_Kleisli, id_, Id_Kleisli, pure, id, cat, Cat_Kleisli.
  split.
  - intros y Hy; simp_propset.
    destruct Hy as [b []]; simp_propset.
    induction H as [ | a r a' ? ? IH].
    + constructor 1.
      simp_propset; exists (inr r); split; auto.
      simp_propset; exists y; split; auto.
      simp_propset; auto.
    + econstructor 2; eauto.
      simp_propset; exists (inl a'); split; auto.
      simp_propset; exists a'; split; simp_propset; auto.
  - intros y Hy; simp_propset.
    induction Hy as [ | a0 r a' ? ? IH ].
    + simp_propset; destruct H as [[a | b] [Hf H]]; simp_propset.
      * destruct H as [a' []]; simp_propset; discriminate.
      * destruct H as [a' [Hg H]]; simp_propset. injection H; clear H; intros <-.
        exists b.
        split; auto; simp_propset.
        constructor 1; auto.
    + destruct IH as [b []]; exists b; split; auto.
      simp_propset.
      destruct H as [[a | b'] [Hf H]]; simp_propset.
      * destruct H as [a2 [Ha Ha']]; simp_propset.
        injection Ha'; clear Ha'; intros <-.
        econstructor 2; eauto.
      * destruct H as [c [Hg Ha']]; simp_propset; discriminate.
Qed.

#[global]
Instance IterDinatural_Prop : IterDinatural (Kleisli propset) sum.
Proof.
  intros A B C f g x.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_Prop.
  unfold case_, Case_Kleisli, Function.case_sum, inr_, Inr_Kleisli, id_, Id_Kleisli, id, pure, cat, Cat_Kleisli.
  split.
  - intros y Hy; simp_propset.
    induction Hy as [ a c H | a c' a' H1 H2 IH].
    + simp_propset; destruct H as [[b | c'] [Ha Hbc]].
      * exists (inl b); split; auto.
        simp_propset; constructor 1.
        simp_propset; exists (inr c); split; auto.
        simp_propset; auto.
      * exists (inr c'); split; auto.
        simp_propset; injection Hbc; intros <-; auto.
    + simp_propset; destruct H1 as [bc [Hf Hg]].
      destruct IH as [bc' [Hf' Hg']].
      exists bc; split; auto.
      destruct bc.
      * destruct bc'; simp_propset.
        { econstructor 2; eauto.
          simp_propset; exists (inl a'); split; eauto. }
        { constructor 1.
          simp_propset; exists (inl a'); split; eauto. }
      * simp_propset; discriminate.
  - intros y Hy; simp_propset.
    destruct Hy as [[b | c] [Hf Hg]].
    + simp_propset.
      revert x Hf.
      induction Hg as [ | a c a' H1 H2 IH ]; intros x Hf.
      * simp_propset; destruct H as [[a | c] [H1 H2]].
        { econstructor 2.
          { simp_propset; exists (inl i); split; eauto. }
          econstructor 1.
          simp_propset; exists (inr r); split; eauto.
          simp_propset; auto.
        }
        { econstructor 1.
          simp_propset; exists (inl i); split; auto.
          injection H2; intros <-; auto.
        }
      * simp_propset; destruct H1 as [[a1 | c1] [Hg Hf']].
        { econstructor 2.
          { simp_propset; exists (inl a); split; eauto. }
          auto.
        }
        { simp_propset; discriminate. }
    + simp_propset. constructor 1.
      simp_propset; exists (inr y); split; auto.
      simp_propset; auto.
Qed.

#[global]
Instance IterCodiagonal_Prop : IterCodiagonal (Kleisli propset) sum.
Proof.
  intros A B f x.
  unfold case_, Case_Kleisli, Function.case_sum, inl_, Inl_Kleisli, id_, Id_Kleisli, id, pure, cat, Cat_Kleisli.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_Prop.
  split; intros y Hy; simp_propset.
  - induction Hy.
    + remember (inr r). generalize dependent r. simp_propset. induction H; intros; subst.
      * constructor 1. eexists; split; eauto; reflexivity.
      * econstructor 2. 2: { apply IHiter_Prop; auto. }
        eexists; split; eauto; reflexivity.
    + remember (inl i'). generalize dependent i'. induction H; intros; subst.
      * econstructor 2; eauto. eexists; split; eauto; reflexivity.
      * econstructor 2. 2: { eapply IHiter_Prop; eauto. }
        eexists; split; eauto; reflexivity.
  - induction Hy as [ | ? ? ? ? ? IH ].
    + destruct H as (? & H & ?). destruct x as [? | [? | ?]]; simp_propset; inversion H; clear H; subst.
      constructor 1. constructor 1. auto.
    + destruct H as (? & H & ?).
      destruct x as [? | [? | ?]]; inversion H; clear H; subst.
      * destruct IH.
        -- constructor 1. econstructor 2; eauto.
        -- econstructor 2; eauto. econstructor 2; eauto.
      * econstructor 2; eauto. constructor 1. auto.
Qed.

#[global]
Instance Iterative_Prop : Iterative (Kleisli propset) sum.
Proof.
  constructor; typeclasses eauto.
Qed.
