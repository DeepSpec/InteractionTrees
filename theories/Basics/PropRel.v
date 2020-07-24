(* So far, we've experimented on defining the nondeterministic propositional
   monad transformer (PropT) in the category of types with equalities (setoids)
   where the morphisms are setoids. From the study in [relPropT.v], it seems
   that we might be able to prove the monad laws for PropT if we work in the
   category where objects are [typ] (our setoid types) and the arrows are
   relations between [typ]s. Here goes the experiment. *)

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
     Basics.CategoryRelation
     Basics.HeterogeneousRelations
     Basics.Monad
     Basics.Typ.

Import CatNotations.
Open Scope cat_scope.

Section PropT.

  Context (m : typ -> typ).
  Context {MREL : Monad relationH m}.
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.
  Context {EqmRInverses : EqmRMonadInverses m}.
  Context {MREL_laws : MonadLaws MREL}.

  Definition PropT (X:typ) : typ := (m X) ~~> prop_typ.

  Program Definition lift {A:typ} (ma : m A) : PropT A :=
    fun mb : m A => mb == ma.
  Next Obligation.
    do 2 red.
    intros. rewrite H. reflexivity.
  Qed.

  Notation rret := (@ret _ _ _ MREL _).
  Notation rbind A B := (@bind _ _ _ MREL A B).

  (* First attempt: trying to define PropT in relation category. The bind definition is not
   quite right. *)
  Program Definition retT : forall a : typ, relationH a (PropT a) :=
    fun a : typ =>
    (-=->!)
      (fun X : a × m a ~~> prop_typ =>
         let (t, t0) := X in rret @ (t, ret @ t)) _.
  Next Obligation.
    repeat intro. cbn in *. destruct x, y. cbn in *.
    destruct t0, t2. cbn in *. destruct H.
    rewrite H. reflexivity.
  Qed.

  Program Definition bindT :
    forall a b : typ, relationH a (PropT b) -> relationH (PropT a) (PropT b).
  intros. unfold relationH, PropT in *.
  destruct X.
  refine (-=->! _ _). Unshelve.
  2 : {
    cbn. intros. destruct X. destruct t, t0. cbn in *.
    refine (exists (u : m a), x0 u /\ _).
    (* refine (rsubst a b _ @ _). clear p p0 p1. *)
    Admitted.


  (* Second attempt: defining PropT in typ_proper category. *)
  Program Definition rsubst : forall a b : typ, (relationH a (m b)) -> (relationH (m a) (m b)) :=
    fun (a b : typ) (X : relationH a (m b)) =>
    (-=->!) (fun X0 : m a × m b => rbind a b X @ X0) _.
  Next Obligation.
    repeat intro. destruct x, y. cbn in *.
    destruct H. rewrite H, H0. reflexivity.
  Qed.


  Program Definition retT_ : forall a : typ, a -=-> PropT a :=
    fun a : typ =>
    (-=->!)
      (fun X : a =>
      (-=->!) (fun X0 : m a => rret @ (X, X0)) _) _.
  Next Obligation.
    repeat intro. rewrite H. reflexivity.
  Qed.
  Next Obligation.
    repeat intro. cbn. rewrite H, H0. reflexivity.
  Qed.

  Program Definition bindT_ : forall a b : typ, a -=-> PropT b -> PropT a -=-> PropT b :=
    fun (a b : typ) (X : a -=-> PropT b) =>
    (-=->!)
    (fun X0 : m a -=-> prop_typ =>
       (-=->!) (fun X1 : m b => exists ma : m a, X0 @ ma /\ rsubst a b (uncurry X) @ (ma, X1)) _) _.
  Next Obligation.
    repeat intro. cbn. setoid_rewrite H. reflexivity.
  Qed.
  Next Obligation.
    repeat intro. cbn. setoid_rewrite H0. setoid_rewrite H.
    reflexivity.
  Qed.

  Instance MonadPropT : Monad typ_proper PropT.
    split.
    - exact retT_.
    - exact bindT_.
  Defined.

  Lemma bind_ret_l_: forall (a b : typ) (f : a -=-> PropT b), ret >>> bind f ⩯ f.
  Proof.
    repeat intro. rewrite <- H, <- H0. cbn.
    clear H H0 y y0.
    destruct MREL. cbn in *. destruct MREL_laws.
    clear bind_ret_r bind_bind bind_proper. cbn in *.
    repeat red in bind_ret_l.
    unfold cat, Cat_rel, compose in bind_ret_l. cbn in *. unfold subrelationH in *.
    specialize (bind_ret_l a b (uncurry f)).
    destruct bind_ret_l; cbn in *.
    split.
    - intros.
      destruct H1 as (ma & Ret & Bind).
      apply H. exists ma. split; auto.
    - intros. apply H0. auto.
  Qed.

  Lemma ret_uncurry:
    forall (a : typ), rret ⩯ (uncurry (retT_ a)).
  Admitted.

  Lemma bind_uncurry:
    forall (a b c : typ) (f : a -=-> PropT b) (g : b -=-> PropT c),
    ((@cat typ relationH Cat_rel a (m b) (m c) (@uncurry a (m b) prop_typ f)
                          (@bind typ relationH m MREL b c (@uncurry b (m c) prop_typ g)))
       ⩯ uncurry (f >>> bindT_ b c g)).
  Admitted.

  Lemma bind_ret_r_ : forall a : typ, bind ret ⩯ id_ (PropT a).
  Proof.
    repeat intro. rewrite <- H, <- H0. cbn.
    clear H H0 y y0.
    pose proof @bind_ret_r as bind_ret_r.
    specialize (bind_ret_r _ _ _ _ _ _ MREL _).
    unfold cat, Cat_rel, compose in bind_ret_r. cbn in *. unfold subrelationH in *.
    specialize (bind_ret_r a).
    destruct bind_ret_r; cbn in *.
    split.
    - intros.
      destruct H1 as (? & ? & ?).
      unfold subrelationH in *. cbn in *.
      specialize (H x1 x0).
      epose proof bind_proper. repeat red in H3.
      specialize (H3 _ _ (ret_uncurry a)). unfold subrelationH in *.
      destruct H3.
      specialize (H4 _ _ H2).
      specialize (H H4). rewrite <- H. auto.
    - intros.
      exists x0. split; auto.
      epose proof bind_proper.
      specialize (H2 _ _ (ret_uncurry a)).
      destruct H2. unfold subrelationH in *.
      apply H2. apply H0. cbn. reflexivity.
  Qed.

  Lemma bind_bind_ :
    forall (a b c : typ) (f : a -=-> PropT b) (g : b -=-> PropT c),
      bind f >>> bind g ⩯ bind (f >>> bind g).
  Proof.
    repeat intro. rewrite <- H, <- H0; cbn.
    clear H H0 y y0.
    pose proof @bind_bind as bind_bind.
    specialize (bind_bind _ _ _ _ _ _ MREL _).
    specialize (bind_bind a b c (uncurry f) (uncurry g)).
    cbn in *.
    unfold eq2, Eq2_rel, eq_rel, subrelationH in bind_bind.
    cbn in *.
    split.
    - destruct bind_bind as (bind_bind & _).
      intros.
      destruct H as (mb & (ma & Ret & Bind1) & Bind2).
      exists ma. split; auto.
      specialize (bind_bind ma x0).
      epose proof bind_proper. repeat red in H.
      specialize (H _ _ (bind_uncurry a b c f g)). unfold subrelationH in *.
      cbn. destruct H.
      apply H. apply bind_bind. exists mb. split; auto.
    - destruct bind_bind as (_ & bind_bind).
      intros.
      destruct H as (ma & Ret & Bind).
      specialize (bind_bind ma x0).
      destruct bind_bind.
      + epose proof bind_proper. repeat red in H.
        specialize (H _ _ (bind_uncurry a b c f g)). unfold subrelationH in *.
        cbn. destruct H.
        apply H0. apply Bind.
      + exists x1. destruct H. split. exists ma. split; auto. auto.
  Qed.

  Instance MonadPropTLaws : MonadLaws MonadPropT.
  split.
  - apply bind_ret_l_.
  - apply bind_ret_r_.
  - apply bind_bind_.
  Admitted.
