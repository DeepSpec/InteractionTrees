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
     Basics.Basics
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

(* Testing definition of relational monad *)
(* We have a suspicion that Li-yao's definition of *prop_rel* is not quite right, i.e. it's not possible to define the
   substitution rules for meaningful monads. Let's try the definition on basic monads. *)
Section RelMonadExp.


  Class RelMonad (M : Type -> Type) : Type :=
    { rret : forall A, A -> M A -> Prop
    ; rsubst : forall A B, (A -> M B -> Prop) -> M A -> M B -> Prop
    }.

  Arguments rret {M _ _}.
  Arguments rsubst {M _ _ _}.

  Definition eq_rel {A B} (RL RR : A -> B -> Prop) : Prop :=
    forall a b, RL a b <-> RR a b.

  Infix "≂" := eq_rel (at level 40).

  Definition catrel {A B C} (RL : A -> B -> Prop) (RR : B -> C -> Prop)
    : A -> C -> Prop :=
    fun a c => exists b, RL a b /\ RR b c.

  Class RelMonadLaws (M : Type -> Type) {RM : RelMonad M} : Prop :=
    { Proper_rsubst : forall A B, Proper (eq_rel ==> eq_rel) (rsubst (A := A) (B := B))
    ; rsubst_rret : forall A,
        rsubst rret ≂ @eq (M A)
    ; cat_rsubst_rret : forall A B (f : A -> M B -> Prop),
        catrel rret (rsubst f) ≂ f
    ; rsubst_rsubst : forall A B C (f : A -> M B -> Prop) (g : B -> M C -> Prop),
        catrel (rsubst f) (rsubst g) ≂ rsubst (catrel f (rsubst g))
    }.

  (* Identity Monad *)
  Definition ID (X:Type) := X.

  Definition ID_ret {X:Type} (a : X) : X := a.
  Definition ID_bind {X:Type} (a : X) (f: X->X) : X := f a.

  Instance RelIDMonad : RelMonad ID.
  split.
  - intros A a ma.
    refine (ma = ID_ret a).
  - intros A B f ma mb.
    refine (f ma mb).
  Defined.

  Lemma rsubst_rsubst_ID :
    forall A B C (f : A -> ID B -> Prop) (g : B -> ID C -> Prop),
        catrel (rsubst f) (rsubst g) ≂ rsubst (catrel f (rsubst g)).
  Proof.
    cbn. intros. repeat intro.
    unfold catrel. split; auto.
  Qed. (* ! We proved it.. *)

  (* OK, Perhaps for the ID Monad it is too trivial to prove. Let's look at the state monad. *)


  (* General RelMonad transformer *)
  Definition lift_ret {M : Type -> Type} `{Monad.Monad M} {A} : A -> M A -> Prop :=
    fun a ma => Monad.ret a = ma.

  (* Definition in_domain {M} `{Monad.Monad M} {A} (a : A) (ma : M A) := Prop. *)

  Definition lift_rsubst {M} `{Monad.Monad M} (in_image : forall X, X -> M X -> Prop) {A B} : (A -> M B -> Prop) -> M A -> M B -> Prop :=
    (fun P ma mb => forall a, in_image A a ma -> forall f, P a (f a) -> Monad.bind ma f = mb).


  Instance RelMonadT (M : Type -> Type) `{Monad.Monad M} (in_image : forall A, A -> M A -> Prop): RelMonad M.
  split.
  - exact (@lift_ret M H).
  - exact (@lift_rsubst M H in_image).
  Defined.

  Definition state (S A : Type) := S -> (S * A)%type.
  Instance stateMonad S : Monad.Monad (state S).
  split.
  - intros. unfold state. intros. split. apply X0. apply X.
  - intros. unfold state in *. intros. specialize (X X1). clear X1. destruct X.
    specialize (X0 t0 s). apply X0.
  Defined.

  Instance RelStateMonad (S : Type) : RelMonad (state S) := RelMonadT (state S) (fun X a ma => exists s, (snd (ma s)) = a).

  Lemma rsubst_rsubst_state (S : Type) :
    forall A B C (f : A -> state S B -> Prop) (g : B -> state S C -> Prop),
      catrel (rsubst f) (rsubst g) ≂ rsubst (catrel f (rsubst g)).
  Proof.
    cbn. intros A B C f g ma mc.
    unfold catrel. split.
    - intros. destruct H as (mb & bindF & bindG).
      unfold lift_rsubst in *. intros a HA h bindH.
      destruct bindH as (mb' & fmb' & H).
      specialize (bindF a HA).
      destruct HA as (s & HA).
      specialize (H (snd (mb' s))).
      assert (exists s0 : S, snd (mb' s0) = snd (mb' s)).  {
        exists s; auto.
      }
      specialize (H H0); clear H0.
      From Coq Require Import Logic.FunctionalExtensionality.
      apply functional_extensionality.
      intros s'.
      (* While the predicate quantifies over the domain, the equality of state monads depend more so on the state..!
       There needs to be something in the relation that talks about the "choice" taken for the effectful part of the
       computation. How do we express this?

       (Similar to the problem that we had before, where we could not gain enough information about the "state" that was
       being piped through.)

       In terms of ITrees, it makes sense to look at the "History", but what does it mean for states?
       *)
      (* 2 : { *)
      (*   specialize (H ) *)
      (* } *)
      (* apply H1. *)
      (* destruct H0. specialize (H a ) *)
Abort.


  Opaque StateMonad.Monad_state.
  Lemma rsubst_rsubst_state_F (S : Type) :
    forall A B C (f : A -> state S B -> Prop) (g : B -> state S C -> Prop),
      not (catrel (rsubst f) (rsubst g) ≂ rsubst (catrel f (rsubst g))).
  Proof.
    (* intros A B C f g. cbn. unfold lift_rsubst, catrel. *)
    (* intro. cbn in H. edestruct H. cbn in *.  *)
  Abort.

End RelMonadExp.

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
        let (t, t0) := X in
          forall m, t0 m <-> m == ret @ t) _.
         (* rret @ (t, ret @ t)) _. *)
  Next Obligation.
  Admitted.
  (*   repeat intro. cbn in *. destruct x, y. cbn in *. *)
  (*   destruct t0, t2. cbn in *. destruct H. *)
  (*   rewrite H. reflexivity. *)
  (* Qed. *)

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
  - epose proof bind_proper. repeat intro. cbn.
    assert (uncurry x ⩯ uncurry y). admit.
    repeat red in H.
    (* specialize (H (uncurry x)).  H3).  *)
  Admitted.
