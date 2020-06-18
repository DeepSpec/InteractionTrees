(** * Monad laws and associated typeclasses *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryMonad
     Basics.CategoryTheory
     Basics.Typ
     Basics.HeterogeneousRelations
     Basics.Function.

(* end hide *)

Set Primitive Projections.

Import Carrier.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope typ_scope.
Section EqmR.

(* SAZ: really HeterogenousRelations should be proper.  We could remove all those assumptions here. *)

  (* We consider heterogeneous relations on computations parameterized by a relation on the return types *)
  (* Rq: if we make [EqMR] a singleton class, the type checker tends to craft dumb instances for itself behind our back.
    I wrapped it up in a record, it seems to prevent this behavior.
  *)
  Class EqmR (m : typ -> typ) : Type :=
    {
      eqmR : forall (A B : typ) (R : relationH A B), relationH (m A) (m B) ;
      eqmR_equal : forall (A : typ), eq_rel (eqmR A A A) (m A)
    }.

  (*
    The more traditional notion of monadic equivalence is recovered at the equality relation
    [forall A,  m A -> m A -> Prop]
   *)
  Definition eqm {m : typ -> typ} `{@EqmR m} {A: typ} := eqmR A A A.

End EqmR.

(* YZ: I don't think [A] should be maximally inserted, but putting it back as is for now for retro-compatibility *)
Arguments eqmR {m _ A B}.
Arguments eqm {m _ A}.
Arguments eqmR_equal {m _}.
Infix "A ≈ B" := (eqm @ (A, B)) (at level 70) : monad_scope.

Import RelNotations.
Local Open Scope relationH_scope.

Section EqmRRel.
  Context (m : typ -> typ).
  Context {EqMR : EqmR m}.

(*
  Global Instance Proper_transpose_relationH {A B : typ} (R: relationH A B) `{Proper _ (equalE A ==> equalE B ==> iff)%signature R} : Proper (equalE B ==> equalE A ==> iff) (†R).
  Proof.
    repeat red.
    unfold transpose; intros; cbn in *.
    apply H; assumption.
  Qed.

  Global Instance Proper_compose_relationH {A B C: typ}
         (R1: relationH A B)
         (R2 : relationH B C)
         `{Proper _ (equalE A ==> equalE B ==> iff)%signature R1}
         `{Proper _ (equalE B ==> equalE C ==> iff)%signature R2}
    : Proper (equalE A ==> equalE C ==> iff) (R2 ∘ R1).
  Proof.
    repeat red. unfold HeterogeneousRelations.compose.
    intros; cbn in *.
    split; intros (b & Hxb & Hbx); exists b; split; intros.
    - specialize (H _ _ H1).
*)

  (* Requirements of well-formedness of [eqmR] *)
  Class EqmR_OK : Type :=
    {
    (* [eqmR] should transport elementary structures of the relation [R] *)
    (* Question: should it transport anti-symmetry? 


       Could remove reflexivity: It isn't satisfied by [StateT void] (but could
       also add the non-emptyness predicate for StateT instance.
     *)

    eqmR_transport_refl :  forall {A : typ} (R : relationH A A), ReflexiveH R -> ReflexiveH (eqmR R);

    eqmR_transport_symm :  forall {A : typ} (R : relationH A A), SymmetricH R -> SymmetricH (eqmR R);

    eqmR_transport_trans : forall {A : typ} (R : relationH A A), TransitiveH R -> TransitiveH (eqmR R);

      (* [eqmR] is associative by composing the underlying relationHs *)
    eqmR_rel_trans : forall {A B C : typ}
                       (R1 : relationH A B)
                       (R2 : relationH B C)
                       (ma : m A) (mb : m B) (mc : m C),
        eqmR R1 @ (ma, mb) ->
        eqmR R2 @ (mb, mc) ->
        eqmR (R2 ∘ R1) @ (ma, mc);

    eqmR_lift_transpose : forall {A B : typ} (R : relationH A B)
      , eq_rel (eqmR †R) (†(eqmR R));

    (* SAZ: I don't think that this can hold in general as stated -- at least it doesn't
       seem to be true of the ID monad.

       I think that we might insist that f and g be "pairing" -- that is 
       f must be [fun a b -> ret (a, b)] and similarly for g.  
     *)
    (* eqmR_rel_prod : forall {A1 A2 B1 B2 : typ} *)
    (*                       (RA : relationH A1 A2) *)
    (*                       (RB : relationH B1 B2) *)
    (*                        (x1 : A1) (x2 : A2) (y1 : B1) (y2 : B2), *)
    (*   RA @ (x1, x2) -> *)
    (*   RB @ (y1, y2) -> *)
    (*   eqmR (RA ⊗ RB) @ (ret @ ((x1, y1),(x2, y2))); *)

      (* [eqmR] respects extensional equality of the underlying relationH
         and [eqm] on both arguments over the monad *)
      (* SAZ: We need to restrict this to only Proper relations R, otherwise even
         the identity monad doesn't work.
         - option 1 : change relationH to be A -=-> B -=-> Prop_type
           keep the old fully-general version

         - option 2 : restrict eqmR_Proper as shown:
      *)
    eqmR_Proper :> forall {A B : typ},
        Proper (@eq_rel A B ==> eq_rel) eqmR;

      (* [eqmR] is monotone as a morphism on relationHs *)
    eqmR_Proper_mono :> forall {A B},
        Proper ((@subrelationH _ _) ==> (@subrelationH _ _)) (@eqmR m _ A B);
    }.

End EqmRRel.

(* SAZ : TODO Add typeclass instances of the form:

    EqmR_OK m -> `{Reflexive R} : Reflexive (` emqR m R)
    etc.
*)


(* SAZ: Renamed "Domain" to "Image" -- more accurate *)
Section Image.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmROKm : EqmR_OK m}.

  (** *Partitions on Heterogeneous Relations
    *
    * https://en.wikipedia.org/wiki/Heterogeneous_relation#Difunctional
    * Among homogeneous relations, equivalence relations partition the set.
    *
    * For heterogeneous relations, a partitioning relation is a
    * _difunctional_ relation, R = F (†G), where F and G are univalent
    * (functional), i.e. forall x y z, F x y /\ F x z => y = z.
    *
    * N.B.: For homogeneous relations, PER's are _difunctional_.
    * *)

  (* Riguet's characterization of difunctional relations. *)
  Definition difunctional {A B : typ} (R : relationH A B) : Prop :=
    R ∘ († R ∘ R) ⊑ R.

  Ltac crunch :=
  repeat match goal with
         | [ H : exists X, _ |- _ ] => destruct H
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : _ \/ _ |- _ ] => destruct H
         | [ |- _ /\ _ ] => split
         end.

  Ltac saturate H :=
    match goal with
           | [ H1 : forall a b, ?R a b -> _,
               H2 : forall a b, ?R b a -> _,
               H : ?R ?A ?B  |- _ ] => pose proof (H1 A B H); pose proof (H2 B A H); clear H; crunch
           end.

  (* SAZ:
     We *don't* want the image to be reflexive because it's not true.

     Consider itrees then [image spin] is the empty PER because there
     are no elements that can be returned.


     Q: should we instead define this as a predicate of type A -=-> prop_typ ?
   *)

  (*
   * An _image_ is a (unary) logical predicate that specifies the intersection
   * of PER's that a monadic value satisfies. Intuitively, what this entails is
   * the possible set of elements of the specified type [A] that a monadic
   * value can return. In this sense, it is an "image" as in set theory,
   * indicating the set of all output values that a monad may produce.
   *
   * Notice the definition of _image_ takes the universal quantification over
   * all PER's satisfying [EQ], giving the smallest relation which will
   * describe the set of elements that a monadic value may return.
   *
   * Consider [image spin] in ITrees, or more simply, [image Nothing] for the
   * option monad, where the carrier type is [A].
   *
   * There exists no PER over any carrier type that this option monad may have
   * in which [Nothing] can give an image to, i.e. the smallest relation over
   * [Nothing] cannot say anything about values of type [A].
   *)
  Program Definition imageH {A1 A2:typ} (m1 : m A1) (m2 : m A2) : relationH A1 A2 :=
    fun (p : A1 × A2) =>
      forall (R : relationH A1 A2)
        (H : difunctional R)
        (EQ: eqmR R @ (m1, m2)), R @ p.
  Next Obligation.
    repeat intro. destruct x, y, H. cbn in *. split.
    - repeat intro. rewrite <- H. rewrite <- H0.
      apply H1; eauto.
    - repeat intro. rewrite H, H0. apply H1; eauto.
  Defined.

  (* NB: Every PER is difunctional, but the converse does not hold. *)
  Program Definition image {A:typ} (m : m A) : relationH A A :=
    (* imageH m m. *)
    fun p =>
      forall (R : relationH A A) (PH : PER R)
        (EQ: eqmR R @ (m, m)), R @ p.
  Next Obligation.
    do 2 red.
    intros (x1 & y1) (x2 & y) (H1 & H2). cbn in *.
    split; intros.
    - specialize (H R).
      rewrite <- H1.
      rewrite <- H2.
      apply H; assumption.
    - specialize (H R).
      rewrite H1, H2.
      apply H; assumption.
  Qed.

  (* Using [image] we can define the [mayRet] predicate, which identifies
   * the subset of A on which the computation [ma] can halt with
   * a [ret x]. (When we characterize monadic computations, we use [mayRet]
   * and we only care about this unary form.) *)
  Program Definition mayRet {A:typ} (ma : m A) : A -=-> prop_typ :=
    (fun (a:A) => image ma @ (a, a)).
  Next Obligation.
    do 2 red.
    intros a1 a2 HA; split; intros.
    - rewrite <- HA. apply H; auto.
    - rewrite HA; apply H; auto.
  Qed.

  Lemma transpose_eq {A} (R : relationH A A) (x:A) :
    R @ (x, x) <-> (transpose R) @ (x, x).
  Proof.
    split; intros.
    destruct R; cbn in *.
    assumption.
    destruct R; cbn in *.
    assumption.
  Qed.

  Global Instance image_PER {A} (ma : m A) : PER (image ma).
  Proof.
    constructor.
    - red.
      intros a.
      repeat intro.
      apply per_symm.
      apply H; auto.
    - red.
      intros.
      destruct p; destruct q; cbn in *.
      intros.
      pose proof (per_trans (t, t0) (t1, t2)). apply H2. apply H; assumption.
      apply H0; assumption. apply H1.
  Defined.

  Lemma image_Reflexive_l {A:typ} (ma : m A) (a1 a2:A) 
    (H : image ma @ (a1, a2)) : image ma @ (a1, a1).
  Proof.
    assert (image ma @ (a2, a1)).
    { apply per_symm in H. apply H. }
    eapply per_trans in H. apply H in H0. apply H0. reflexivity.
  Qed.

  Lemma image_Reflexive_r {A:typ} (ma : m A) (a1 a2:A) 
    (H : image ma @ (a1, a2)) : image ma @ (a2, a2).
  Proof.
    assert (image ma @ (a2, a1)).
    { apply per_symm in H. apply H. }
    eapply per_trans in H0. apply H0 in H. apply H. reflexivity.
  Qed.


  Lemma image_least {A} (ma : m A)
        (R : relationH A A) (PH : PER R)
        (G: eqmR R @ (ma, ma))
    : subrelationH (image ma) R.
  Proof.
    intros x y D.
    unfold image in D.
    cbn in *.
    apply D; assumption.
  Qed.

  Global Instance Proper_image {A} :
    Proper (equalE (m A) ==> eq_rel) image.
  Proof.
    do 2 red.
    intros x y EQ.
    split.
    - red. intros a b H.
      repeat red.
      intros.
      repeat red in H.
      rewrite <- EQ in EQ0.
      specialize (H R PH EQ0).
      apply H.
    - red. intros a b H.
      repeat red.
      intros.
      repeat red in H.
      rewrite  EQ in EQ0.
      specialize (H R PH EQ0).
      apply H.
  Qed.

  Global Instance Proper_image2 {A}  :
    Proper (equalE (m A) ==> equalE (A × A) ==> iff) (fun ma => (proj1_sig (image ma))).
  Proof.
    do 3 red.
    intros a b H (p1 & p2) (q1 & q2) (HP & HQ).
    split; intros; cbn in *;  intros.
    - rewrite <- HP.
      rewrite <- HQ.
      apply H0; auto. rewrite H. assumption.
    - rewrite HP.
      rewrite HQ.
      apply H0; auto. rewrite <- H. assumption.
  Qed.

  Global Instance Proper_image3 {A}  :
    Proper (equalE (m A) ==> (@eq2 typ typ_proper _ _ _)) image.
  Proof.
    do 3 red.
    intros a b H (p1 & p2) (q1 & q2) (HP & HQ).
    cbn in HP, HQ. rewrite HP. rewrite HQ. 
    split; intros; cbn in *;  intros.
    - apply H0; auto. rewrite H. assumption.
    - apply H0; auto. rewrite <- H. assumption.
  Qed.

  
  Global Instance Proper_mayRet {A:typ} :
    Proper (equalE (m A) ==> (equalE A) ==> iff) (fun ma => (proj1_sig (mayRet ma))).
  Proof.
    do 3 red.
    intros x y H x0 y0 H0.
    split; intros; cbn in *; intros.
    - rewrite <- H0. apply H1; auto. rewrite H. assumption.
    - rewrite H0. apply H1; auto. rewrite <- H. assumption.
  Qed.      

  Global Instance Proper_mayRet2 {A}  :
    Proper (equalE (m A) ==> (@eq2 typ typ_proper _ _ _)) mayRet.
  Proof.
    repeat red.
    intros; split; intros; cbn in *; intros.
    - rewrite <- H0. apply H1; auto. rewrite H. auto.
    - rewrite H0. apply H1; auto. rewrite <- H. auto.
  Qed.

  
  Lemma image_subset {A:typ} (ma : m A) :
    subrelationH (eqmR (image ma)) (m A).
  Proof.
    unfold subrelationH.
    intros.
    apply eqmR_equal.
    specialize (@image_least A ma).
    intros P.
    specialize (P (relationH_of_typ A)).
    eapply eqmR_Proper_mono; eauto.
    apply image_least.
    apply relationH_PER.
    - apply eqmR_equal. apply (@relationH_reflexive (m A)).
  Qed.

  (* SAZ:
     This seems trivial -- since [image ma : relationH A A] can't we just
     use it as the witness?
  *)
  Lemma image_surj:
    forall {A B : typ} (ma : m A) (a1 a2 : A),
        image ma @ (a1, a2) -> exists (R : relationH A A), R @ (a1, a2).
  Proof.
    repeat intro. eexists ?[R]. repeat red in H. apply H.
    apply relationH_PER. eapply eqmR_equal. cbn. reflexivity.
  Qed.

  Lemma image_inv:
    forall {A B : typ} (ma : m A) (a1 a2 : A),
      image ma @ (a1, a2) ->
      forall (R : relationH A A) (H : PER R), eqmR R @ (ma, ma) -> R @ (a1, a2).
  Proof.
    repeat intro. unfold image in *.
    cbn in H. apply H; eauto.
  Qed.

  (* IY: What we might want is this lemma, combined with the axiom of choice. *)
  (* SAZ: The assumption (forall a2, image ma @ (a1, a2)) seems very strong.
     Doesn't that say that if ma can produce a1, it can produce any a2:A ?  
     For example, if we take ma to be [ret a1], then image (ret a1) = singleton (a1)
     and so we'll never be able to satisfy the hypothesis...
  *)
  Lemma eqmR_image:
    forall {A : typ} (ma : m A) (a1 : A),
      (forall a2, image ma @ (a1, a2)) ->
      eqmR (image ma) @ (ma, ma).
  Proof.
    intros. eapply eqmR_transport_refl; eauto.
    repeat intro. eapply image_inv; eauto.
    eapply image_Reflexive_r. apply H.
  Qed.


End Image.



(* In particular, well-formedness of [eqmR] recovers that [eqm] is an equivalence relationH *)
Section EqmRMonad.
  Context (m : typ -> typ).
  Context {EqMRm : EqmR m}.
  Context {Mm : Monad typ_proper m}.

  (* Generalization of monadic laws.
     These are of two quite distinct natures:
     * Heterogeneous generalizations of the usual three monad laws
     * Reasoning principles relating [eqmR R] to [R]
     *)
  Class EqmRMonad :=
    {
    (* SAZ: we can prove only one direction of this law.
          - for StateT we can take the void state, which also cannot be inverted.

          - However, for some monads we do get the other direction:
            (itree E) and StateT S when S is non-void, for example.  So we
            break the other direction out into a different typeclass that
            can be instantiated differently.
     *)


    (* SAZ : Move this requirement earlier? *)
    (* SAZ: Do we need this? Maybe try to do without everywhere. *)

    (* IY: Don't we want this to always hold true? [image m ma] describes the
     * "set of A" that is described by [ma]. Perhaps what we need is that
     * eqmR/image is a "function", so that the resulting set is always equal
     * to each other. This makes me wonder if we want to introduce classical
     * reasoning here, when we're introducing images. (Because the intuition
     * should be similar to dealing with sets of computations, where we can
     * choose elements from the image to reason about them..)*)
    (* IY: Otherwise, we need to have a way of knowing that there is already
     * an element to be in the image. See [eqmR_image] lemma above. *)
    image_eqmR {A : typ} (ma : m A) : eqmR (image m ma) @ (ma, ma);

    (* eqmR_bind_refl_inv : *)
    (*   forall {A : typ} {B : typ} *)
    (*     (RB : relationH B B) (PH: PER RB) *)
    (*     (ma : m A) *)
    (*     (k1 k2  : A -=-> m B), *)
    (*     eqmR RB @ (bind k1 @ ma, bind k2 @ ma) -> *)
    (*       eqmR (image m ma) @ (ma, ma) /\ *)
    (*       (forall a, mayRet m ma @ a -> eqmR RB @ (k1 @ a, k2 @ a)) *)

    (* IY : Is this the same as eqmR_bind_refl_inv? *)
    (* SAZ: I don't think that they're interderivable.  also, this one
       might be better named mayRet_bind_inversion (and mayRet_bind_inv below
       renamed to mayRet_bind)
    *)
    mayRet_bind : forall {A B:typ} (ma : m A) (k : A -=-> m B) (b : B),
        mayRet m (bind k @ ma) @ b ->
        (exists a, mayRet m ma @ a /\ mayRet m (k @ a) @ b);

    (* mayRet_bind' : forall {A B:typ} (ma : m A) (k : A -=-> m B) (b : B), *)
    (*     mayRet m (bind k @ ma) @ b -> *)
    (*     (forall a, mayRet m ma @ a -> mayRet m (k @ a) @ b); *)

    eqmR_mayRet_l : forall {A1 A2 : typ}
                      (RA : relationH A1 A2)
                      (ma1 : m A1) (ma2 : m A2)
                      (EQ : eqmR RA @ (ma1, ma2)),
        forall a1, mayRet m ma1 @ a1 -> exists a2, RA @ (a1, a2) /\ mayRet m ma2 @ a2;

    eqmR_mayRet_r : forall {A1 A2 : typ}
                      (RA : relationH A1 A2)
                      (ma1 : m A1) (ma2 : m A2)
                      (EQ : eqmR RA @ (ma1, ma2)),
        forall a2, mayRet m ma2 @ a2 -> exists a1, RA @ (a1, a2) /\ mayRet m ma1 @ a1;


    eqmR_ret : forall {A1 A2 : typ} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        RA @ (a1, a2) -> eqmR RA @ (ret @ a1, ret @ a2);


    (* SAZ: This used to be: 
       forall (a1:A1) mayRet m ma1 @ a1 -> exists a2, RA @ (a1, a2) /\ eqmR RB @ (kb1 @ a1, kb2 @ a2)
      /\ (...vice versa...)


      This vesion causes problems with later proofs.
      Try stating like Lemma eqmR_bind_ProperH_PropM'
     *)
    eqmR_bind_ProperH : forall {A1 A2 B1 B2 : typ}
                          (RA : relationH A1 A2)
                          (RB : relationH B1 B2)
                          ma1 ma2
        (kb1 : A1 -=-> m B1) (kb2 : A2 -=-> m B2),
      eqmR RA @ (ma1, ma2) ->
      (forall (a1 : A1), mayRet m ma1 @ a1 -> forall a2, RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2)) ->
      (forall (a2 : A2), mayRet m ma2 @ a2 -> forall a1, RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2)) ->
      eqmR RB @ (bind kb1 @ ma1, bind kb2 @ ma2);

    eqmR_bind_ret_l : forall {A B : typ}
                        (f : A -=-> m B)
                        (a : A),
        equalE (m B) (bind f @ (ret @ a)) (f @ a);

    eqmR_bind_ret_r : forall {A B : typ}
                        (ma : m A),
        equalE (m A) (bind ret @ ma) ma;

    (* forall (a b c : obj) (f : C a (M b)) (g : C b (M c)), bind f >>> bind g ⩯ bind (f >>> bind g) *)
    eqmR_bind_bind : forall {A B C : typ}
                       (ma : m A)
                       (f : A -=-> m B)
                       (g : B -=-> m C),
        equalE (m C) ((bind f >>> bind g) @ ma) (bind (f >>> bind g) @ ma)
    }.

End EqmRMonad.

Arguments eqmR_bind_ret_l {_ _ _ _}.

Section EqmRConsequences.

  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.

  Local Open Scope monad_scope.

  Global Instance monad_eqmR : MonadLaws Mm.
  Proof.
    split; intros.
    - intros x y H.
      pose proof eqmR_bind_ret_l as Hbr.
      specialize (Hbr a b f).
      specialize (Hbr x).
      rewrite <- H.
      apply Hbr.
    - intros x y H. cbn.
      rewrite eqmR_bind_ret_r. apply H. apply EqmRm. eauto.
    - repeat intro.
      pose proof eqmR_bind_bind.
      rewrite H.
      specialize (H0 m _ _ _ _ _ _ y f g).
      assumption.
    - repeat intro. rewrite H0.
      pose proof (eqmR_bind_ProperH).
      specialize (H1 _ _ _ _ a a b b a b y0 y0 x y).
      assert (eqmR a @ (y0, y0)).
      { apply eqmR_transport_refl; auto. rewrite ReflexiveH_Reflexive. destruct a. red. reflexivity. }
      specialize (H1 H2).
      apply eqmR_equal.
      apply H1.
      + intros.
        apply eqmR_equal. cbn. apply H. apply H4.
      + intros.
        apply eqmR_equal. cbn. apply H. apply H4.
      
  Qed.


  Lemma eqmR_bind_ProperH_simple : forall {A1 A2 B1 B2 : typ}
                                     (RA : relationH A1 A2)
                                     (RB : relationH B1 B2)
                                     (ma1 : m A1) (ma2 : m A2)
                                     (kb1 : A1 -=-> m B1) (kb2 : A2 -=-> m B2),
      eqmR RA @ (ma1, ma2) ->
      (forall a1 a2, RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2)) ->
      eqmR RB @ (bind kb1 @ ma1, bind kb2 @ ma2).
  Proof.
    intros A1 A2 B1 B2 RA RB ma1 ma2 kb1 kb2 HMA HK.
    apply eqmR_bind_ProperH with (RA:=RA); auto.
  Qed.


  Lemma  eqmR_bind_ProperH_ma :
    forall {A B1 B2 : typ}
      (RB : relationH B1 B2)
      (ma : m A)
      (kb1 : A -=-> m B1) (kb2 : A -=-> m B2),
      (forall (a : A), mayRet m ma @ a -> eqmR RB @ (kb1 @ a, kb2 @ a)) ->
      eqmR RB @ (bind kb1 @ ma, bind kb2 @ ma).
  Proof.
    intros A B1 B2 RB ma kb1 kb2 H.
    apply eqmR_bind_ProperH with (RA := (relationH_of_typ A)); auto.
    - apply eqmR_equal. change (ma == ma). reflexivity.
    - intros. rewrite H1. cbn. apply H. rewrite <- H1. apply H0.
    - intros. rewrite H1. cbn. apply H. assumption.
  Qed.

  
  Lemma image_bind_eq {A B:typ} (ma : m A) (k1 k2 : A -=-> m B)
        (HK : forall (a1 a2 : A), image m ma @ (a1, a2)  -> (k1 @ a1) == (k2 @ a2)) :
    (bind k1) @ ma == (bind k2) @ ma.
  Proof.
    apply eqmR_equal.
    cbn.
    change (eqmR B @ (bind k1 @ ma, bind k2 @ ma)).
    eapply eqmR_bind_ProperH with (RA := image m ma); auto.
    eapply image_eqmR. auto.
    - intros. 
      apply eqmR_equal. apply HK. assumption.
    - intros. 
      apply eqmR_equal. apply HK. assumption.
  Qed.


  Lemma image_ret_bind {A:typ} (ma : m A) (k : A -=-> m A) : 
      (forall (a1 a2 : A), image m ma @ (a1, a2)  -> k @ a1 == ret @ a2) -> bind k @ ma == (bind ret) @ ma.
  Proof. 
    intros H.
    apply image_bind_eq. intros.
    apply H. assumption.
  Qed.

  Lemma mayRet_image1 {A:typ} (ma : m A) (a1 a2 : A) (HI : image m ma @ (a1, a2)) : mayRet m ma @ a1.
  Proof.
    repeat red.
    intros.
    specialize (HI R PH EQ).
    change (R @ (a1, a1)).
    PER_reflexivityH.
  Qed.


  Lemma mayRet_image2 {A:typ} (ma : m A) (a1 a2 : A) (HI : image m ma @ (a1, a2)) : mayRet m ma @ a2.
  Proof.
    repeat red.
    intros.
    specialize (HI R PH EQ).
    change (R @ (a2, a2)).
    PER_reflexivityH.
  Qed.

  Lemma mayRet_bind_eq {A B:typ} (ma : m A) (k1 k2 : A -=-> m B)
        (HK : forall (a : A), mayRet m ma @ a  -> (k1 @ a) == (k2 @ a)) :
    (bind k1) @ ma == (bind k2) @ ma.
  Proof.
    intros.
    apply eqmR_equal. apply eqmR_bind_ProperH_ma.
    intros. apply eqmR_equal. apply HK; auto.
  Qed.    

  Lemma mayRet_ret_bind {A:typ} (ma : m A) (k : A -=-> m A) : 
      (forall a : A, mayRet m ma @ a  -> k @ a == ret @ a) -> bind k @ ma == (bind ret) @ ma.
  Proof. 
    intros H.
    apply mayRet_bind_eq. intros.
    apply H. assumption.
  Qed.
  
End EqmRConsequences.



Section EqmRInversion.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.

  (* TODO: We need to rearrange / rationalize this typeclass.  This one should
     probably be named something to do with mayRet
  *)
  Class EqmRMonadInverses :=
    {
    (* SAZ : This property doesn't quite overlap with the next two - if the
       monad is such that [ret @ a] doesn't actually return a (e.g. StateT Void)
       then this is not the same.  

       We could also replace this with:
       [forall a, mayRet m (ret @ a) @ a] which should be inter-derivable
    *)
    eqmR_ret_inv : forall {A1 A2 : typ} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        eqmR RA @ (ret @ a1, ret @ a2) -> RA @ (a1, a2);

    (* SAZ: This is a much less general inversion principle, but it seems more likely
       to be true.  It also may be all that we need. 

       SAZ: I don't think that this holds with distinct continuations k1 and k2:
          in the case on nondeterminism, ma = {3, 4} and k1 = [3 -> {5}, 4 -> {6}] and
          k2 = [3 -> {6}, 4 -> {5}] then the resulting binds are quivalent but k1 != k2


       SAZ: The part about eqmR (image m ma) @ (ma, ma) is redundant with 
       image_eqmR, so we should drop it.
     *)
    eqmR_bind_refl_inv :
      forall {A : typ} {B : typ}
        (RB : relationH B B) (SH: SymmetricH RB) (TH: TransitiveH RB)
        (ma : m A)
        (k : A -=-> m B),
        eqmR RB @ (bind k @ ma, bind k @ ma) ->
          (forall a, mayRet m ma @ a -> eqmR RB @ (k @ a, k @ a));

    (* IY : Attempting to state bind inversion in terms of mayRet. *)
    (* SAZ: I don't think we need this -- it is actually weaker than the combination
       of image_eqmR and mayRet_bind.  (See the proof in MonadProp.)
       I propose that we cut it.
    eqmR_bind_refl_inv_mayRet :
      forall {A : typ} {B : typ}
        (RB : relationH B B) (SH: SymmetricH RB) (TH: TransitiveH RB)
        (ma : m A) (k : A -=-> m B) (b : B),
        mayRet m (bind k @ ma) @ b ->
        eqmR (image m ma) @ (ma, ma) /\
        (exists a : A, mayRet m ma @ a ->
                  mayRet m (k @ a) @ b)
    *)
    }.


  (* SAZ :
     The following inversion principle is way too strong.  I'm not sure that it holds
     in any monad except for very trivial cases (like ID).  We cannot rely on it.
  *)
  Class EqmRBindInversion :=
    {
    eqmR_bind_inv : forall {A1 A2 : typ} {B1 B2 : typ} (RB : relationH B1 B2)
                      (ma1 : m A1) (ma2 : m A2)
                      (k1 : A1 -=-> m B1)
                      (k2 : A2 -=-> m B2),
        eqmR RB @ (bind k1 @ ma1, bind k2 @ ma2) ->
        exists (RA : relationH A1 A2),   (* P a1 a2 <-> mayRet ma1 @ a1 <-> mayRet ma2 @ a2  *)
          eqmR RA @ (ma1, ma2) /\
          (forall a1, mayRet m ma1 @ a1 -> exists (a2:A2), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2))
          /\
          (forall a2, mayRet m ma2 @ a2 -> exists (a1:A1), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2));
    }.
  
End EqmRInversion.


Section InversionFacts.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.
  Context {MI : EqmRMonadInverses m}.


  Lemma image_bind {A B: typ} (ma : m A) (k : A -=-> m B) (a1 a2:A) (b1 b2:B) :
    image m ma @ (a1, a2) ->
    image m (k @ a2) @ (b1, b2) ->
    image m (bind k @ ma) @ (b1, b2).
  Proof.
    intros HM HK.
    repeat red.
    intros.
    specialize (eqmR_bind_refl_inv m R _ _ ma k EQ) as Hma.
    cbn in HK.
    specialize (HK R PH). apply HK.
    apply Hma. repeat red. intros.
    specialize (HM R0 PH0 EQ0). 
    change (R0 @ (a2, a2)). 
    PER_reflexivityH.
  Qed.
  
  Lemma mayRet_bind_inv {A B: typ} (ma : m A) (k : A -=-> m B) (a:A) (b:B) :
    mayRet m ma @ a ->
    mayRet m (k @ a) @ b ->
    mayRet m (bind k @ ma) @ b.
  Proof.
    intros HM HK.
    repeat red.
    intros.
    specialize (eqmR_bind_refl_inv m R _ _ ma k EQ) as Hma.
    apply Hma in HM.
    cbn in HK.
    specialize (HK R PH HM). assumption. 
  Qed.
  
  (* SAZ: This one is probably not needed 
     It is unfortunate that k can't have type A -=-> m B -- we need
     some kind of typecast "conversion lemma":
  *)
  Lemma empty_image {A:typ} (ma : m A) : 
    ~(exists a, mayRet m ma @ a) -> forall (k : A -=-> m A), bind k @ ma == ma.
  Proof.
    intros N k.
    assert (ma == (bind ret @ ma)).
    { rewrite bind_ret_r. cbn. reflexivity. }
    rewrite H at 2.
    apply eqmR_equal.
    apply eqmR_bind_ProperH with (RA := (image m ma)). assumption.
    eapply image_eqmR. auto.
    intros.
    assert (exists a, image m ma @ (a, a)).
    { exists a1. eapply image_Reflexive_l. apply H0. }
    contradiction.
    intros.
    assert (exists a, image m ma @ (a, a)).
    { exists a1. eapply image_Reflexive_l. apply H1. }
    contradiction.
  Qed.

  Import RelNotations.
  Local Open Scope relationH_scope.

  

  (* A sanity check about the images: *)
  Program Definition singletonR {A:typ} (x:A) : relationH A A :=
    (fun p => (fst p) == (snd p) /\ (fst p) == x).
  Next Obligation.
    do 2 red.
    intros.
    destruct x0, y; cbn in *.
    destruct H.
    split; intros (HA & HB); split.
    - rewrite <- H. rewrite <- H0. assumption.
    - rewrite <- H. assumption.
    - rewrite H. rewrite H0. assumption.
    - rewrite H. assumption.
  Qed.


  Lemma singletonR_SymmetricH {A:typ} (x:A) : SymmetricH (singletonR x).
  Proof.
    repeat red. intros (a1 & a2) H. unfold singletonR in H. cbn in *.
    destruct H. split; symmetry. tauto. rewrite <- H. symmetry. assumption.
  Qed.

    
  (* Global Instance singletonR_symetric  *)
  (* Proof. *)
  (*   repeat red. intros. unfold singletonR in H. *)
  (*   destruct H. split; symmetry. tauto. rewrite <- H. symmetry. assumption. *)
  (* Qed. *)

  Lemma singletonR_TransitiveH {A:typ} (x:A) : TransitiveH (singletonR x).
  Proof.
      repeat red. intros (a1 & a2) (b1 & b2) HA HB H. unfold singletonR in *. cbn in *.
      destruct HA, HB; split; etransitivity; eauto. rewrite <- H3. assumption. PER_reflexivity.
  Qed.

(*    
  Global Instance singletonR_transitive {A:typ} (x:A) : Transitive (singletonR x).
  Proof.
      repeat red. intros. unfold singletonR in *.
      destruct H, H0; split; etransitivity; eauto. rewrite <- H2. assumption. PER_reflexivity.
  Qed.
 *)

  (*
  Global Instance singletonR_PER {A:typ} (x:A) : PER (singletonR x).
  Proof.
    split; typeclasses eauto.
  Qed.
   *)
(*
  Global Instance Proper_singletonR {A:typ} (x:A) : Proper (equalE A ==> equalE A ==> iff) (singletonR x).
  Proof.
    repeat red; intros; unfold singletonR in *.
    split; intros (HA & HB); split.
    - rewrite <- H. rewrite HA. assumption.
    - rewrite <- H. assumption.
    - rewrite H. rewrite H0. assumption.
    - rewrite H. assumption.
  Qed.
*)
  Lemma ret_image {A:typ} (x:A) : eq_rel (image m (ret @ x)) (singletonR x).
  Proof.
    split.
    - repeat red. intros. 
      unfold image in H. cbn in *.
      specialize (H (singletonR x)).
      assert (PER (singletonR x)).
      { split. apply singletonR_SymmetricH. 
        apply singletonR_TransitiveH. }
      specialize (H H0).
      assert (eqmR (singletonR x) @ (ret @ x, ret @ x)).
      { apply eqmR_ret. typeclasses eauto.  repeat red. cbn. split. reflexivity. reflexivity. }
      apply H in H1. repeat red in H2. assumption.
    - do 4 red. intros.
      unfold singletonR in H. destruct H. cbn in *.
      rewrite <- H. rewrite H0.
      eapply eqmR_ret_inv; eauto.
  Qed.

  
End InversionFacts.
