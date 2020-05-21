
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Typ_Class2
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
.

Import CatNotations.
Open Scope cat_scope.

Section MonadProp.
  Program Definition PropM : typ -> typ :=
    fun (A : typ) =>
      {|
        Ty := {p : A -> Prop | Proper (equalE A ==> iff) p};
        equal :=
          fun pm1 pm2 =>
            forall (a : A), ` pm1 a <-> ` pm2 a
      |}.
  Next Obligation.
    split.
    repeat red. intros x y H a.
    split. apply H. apply H.
    repeat red. intros x y z H H0 a.  
    split. intros. apply H0, H, H1; auto. intros. apply H, H0, H1; auto.
  Qed.

  Instance PropM_Monad : Monad typ_proper PropM.
  split.
  - repeat red. intros A.
    refine (exist _ (fun (a:A) => (exist _ (fun x => equalE A a x) _)) _).
    repeat red. cbn. intros x y Heq a_term.
    rewrite Heq. auto.
    Unshelve.
    repeat red. intros.
    rewrite H.
    auto.
  - repeat red. intros A B HK.
    destruct HK as (K & KProper).
    refine (exist _ (fun PA: PropM A => (exist _ (fun b: B =>
            exists a : A, `PA a /\ (proj1_sig (K a)) b) _)) _).
    (* KS: For some reason the back-tick didn't work here *)
    repeat red. cbn. intros ma1 ma2 Heq b.
    split; intros; destruct H; exists x; specialize (Heq x).
    + rewrite <- Heq. auto.
    + rewrite Heq. auto.
    Unshelve.
    repeat red. intros b1 b2 Heq.
    split; intros; destruct H; exists x; destruct H; split; auto.
      * cbn in *. destruct K.
        (* KS: Coq can't find the necessary Proper instance to
               rewrite unless K is destructed. *)
        rewrite <- Heq. auto.
      * cbn in *; destruct K; rewrite Heq; auto.
  Qed.

End MonadProp.
