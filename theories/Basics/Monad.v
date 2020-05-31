(** * Monad laws and associated typeclasses *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryMonad
     Basics.CategoryTheory
     Basics.HeterogeneousRelations
     Basics.Typ_Class2
     Basics.Function.
(* end hide *)

Set Primitive Projections.

Import Carrier.
Import CatNotations.
Local Open Scope cat_scope.

Section EqmR.

  (* We consider heterogeneous relations on computations parameterized by a relation on the return types *)
  (* Rq: if we make [EqMR] a singleton class, the type checker tends to craft dumb instances for itself behind our back.
    I wrapped it up in a record, it seems to prevent this behavior.
  *)
  Class EqmR (m : typ -> typ) : Type :=
    { eqmR : forall (A B : typ) (R : relationH A B), relationH (m A) (m B) ;
      (* IY: Is there an alternative way to define this? *)
      eqmR_equal : forall A, eqmR A A (equalE A) = equalE (m A)
    }.

  Arguments eqmR {m _ A B}.

  (*
    The more traditional notion of monadic equivalence is recovered at the equality relation
    [forall A,  m A -> m A -> Prop]
   *)
  Definition eqm {m : typ -> typ} `{@EqmR m} {A: typ} := eqmR (equalE A).

End EqmR.

(* YZ: I don't think [A] should be maximally inserted, but putting it back as is for now for retro-compatibility *)
Arguments eqm {m _ A}.
Arguments eqmR {_ _ _ _}.
Infix "≈" := eqm (at level 70) : monad_scope.

Section EqmRRel.
  Context (m : typ -> typ).
  Context {EqMR : EqmR m}.

  Import RelNotations.
  Local Open Scope relationH_scope.
  
  (* Requirements of well-formedness of [eqmR] *)
  Class EqmR_OK : Type :=
    {
    (* [eqmR] should transport elementary structures of the relation [R] *)
    (* Question: should it transport anti-symmetry? *)

      eqmR_transport_symm :>  forall {A : typ} (R : relationH A A), Symmetric R  -> Symmetric (eqmR R);
      eqmR_transport_trans :> forall {A : typ} (R : relationH A A), Transitive R -> Transitive (eqmR R);

      (* [eqmR] is associative by composing the underlying relationHs *)
      eqmR_rel_trans : forall {A B C : typ} (R1 : relationH A B) (R2 : relationH B C)
                         (ma : m A) (mb : m B) (mc : m C),
          eqmR R1 ma mb ->
          eqmR R2 mb mc ->
          eqmR (R2 ∘ R1) ma mc;

      eqmR_lift_transpose : forall {A B : typ} (R : relationH A B), eq_rel (eqmR †R) (†(eqmR R));

      (* [eqmR] respects extensional equality of the underlying relationH
         and [eqm] on both arguments over the monad *)
      (* SAZ: We need to restrict this to only Proper relations R, otherwise even
         the identity monad doesn't work.  
         - option 1 : change relationH to be A -=-> B -=-> Prop_type
           keep the old fully-general version

         - option 2 : restrict eqmR_Proper as shown:
      *)
      eqmR_Proper :> forall {A B : typ}
          (R : relationH A B),
          Proper (equalE A ==> equalE B ==> iff) R ->
          Proper (eqmR (equalE A) ==> eqmR (equalE B) ==> iff) (@eqmR _ _ A B R);

      (* [eqmR] is monotone as a morphism on relationHs *)
      eqmR_Proper_mono :> forall {A B},
          Proper (@subrelationH _ _ ==> @subrelationH _ _) (@eqmR m _ A B);

    }.

End EqmRRel.

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
          - for PropT we can take the proposition (fun _ => False)
            which accepts no computations.  Then it is true that (ret a1) and (ret a2)
            are equi-accepted by that proposition, but there doesn't have to be any relation
            between

          - for StateT we can take the void state, which also cannot be inverted.
          
          - However, for some monads we do get the other direction:
            (itree E) and StateT S when S is non-void, for example.  So we
            break the other direction out into a different typeclass that
            can be instantiated differently.
       *)
      eqmR_ret : forall {A1 A2 : typ} (RA : A1 -> A2 -> Prop) (a1:A1) (a2:A2),
        RA a1 a2 -> eqmR RA (ret @ a1) (ret @ a2);

      eqmR_bind_ProperH : forall {A1 A2 B1 B2 : typ}
                            (RA : A1 -> A2 -> Prop)
                            (RB : B1 -> B2 -> Prop)
                            ma1 ma2
                            (kb1 : A1 -=-> m B1) (kb2 : A2 -=-> m B2),
          eqmR RA ma1 ma2 ->
          (forall a1 a2, RA a1 a2 -> eqmR RB (kb1 @ a1) (kb2 @ a2)) ->
          eqmR RB (bind kb1 @ ma1) (bind kb2 @ ma2);

    (* Question: The following helps _proving_ [eqmR _ (bind _ _)].
       Should we require something to invert such an hypothesis?
    eqmR_Proper_bind :> forall {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop),
        (Proper (eqmR RA ==> (RA ==> (eqmR RB)) ==> eqmR RB) bind);
     *)

    eqmR_bind_ret_l : forall {A B : typ}
                        (f : A -=-> m B)
                        (a : A)
                        (a_OK : a ∈ A),
        equalE (m B) (bind f @ (ret @ a)) (f @ a);

    eqmR_bind_ret_r : forall {A B : typ}
                        (ma : m A)
                        (ma_OK : ma ∈ m A),
        equalE (m A) (bind ret @ ma) ma;

       (* forall (a b c : obj) (f : C a (M b)) (g : C b (M c)), bind f >>> bind g ⩯ bind (f >>> bind g) *)
    eqmR_bind_bind : forall {A B C : typ}
                       (ma : m A)
                       (ma_OK : ma ∈ m A)
                       (f : A -=-> m B)
                       (g : B -=-> m C),
        equalE (m C) ((bind f >>> bind g) @ ma) (bind (f >>> bind g) @ ma)
    }.

  Class EqmRMonadInverses :=
    {
    eqmR_ret_inv : forall {A1 A2 : typ} (RA : A1 -> A2 -> Prop) (a1:A1) (a2:A2),
        eqmR RA (ret @ a1) (ret @ a2) -> RA a1 a2
    }.
  
End EqmRMonad.

Arguments eqmR_bind_ret_l {_ _ _ _}.

Section Laws.

  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.
  
  Local Open Scope monad_scope.

  Global Instance monad_eqmR : MonadLaws Mm.
  Proof.
    split; intros.
    - intros x y H. cbn.
      pose proof eqmR_bind_ret_l as Hbr.
      specialize (Hbr a b f).
      assert (x == x). etransitivity; [ | symmetry ]; eassumption.
      specialize (Hbr _ H0); clear H0.
      rewrite <- H.
      apply Hbr.
    - intros x y H. cbn.
      rewrite eqmR_bind_ret_r. apply H. apply EqmRm. eauto. unfold contains.
      etransitivity; [ | symmetry ]; eassumption.
    - repeat intro.
      pose proof eqmR_bind_bind.
      rewrite H.
      unfold contains in H0.
      assert (x == x). etransitivity; [ | symmetry ]; eassumption.
      specialize (H0 m _ _ _ _ _ _ _ H1 f g). rewrite <- H.
      apply H0.
    - repeat intro. rewrite H0.
      pose proof (eqmR_bind_ProperH).
      specialize (H1 _ _ _ _ a a b b equal equal x0 y0 x y).
      rewrite eqmR_equal in H1. specialize (H1 H0).
      rewrite eqmR_equal in H1.
      rewrite <- H0 at 1.
      apply H1. intros. rewrite H2. apply Proper_typ_proper_app.
      apply H. etransitivity ; [ symmetry | ]; eassumption.
  Qed.

End Laws.


Section Domain.

  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.
  Context {EqMRI: EqmRMonadInverses m}.

  Definition domain {A:typ} (m : m A) : A -> A -> Prop :=
    fun x y =>
      forall (R : A -> A -> Prop), PER R -> eqmR R m m -> R x y.


  Global Instance domain_symmetric {A} (ma : m A) : Symmetric (domain ma).
  Proof.
    repeat red.
    intros.
    unfold domain in H. symmetry. apply (H R); tauto.
  Qed.

  Global Instance domain_transitive {A} (ma : m A) : Transitive (domain ma).
  Proof.
    repeat red.
    intros.
    unfold domain in *.
    eapply transitivity. apply H; eauto. apply H0; eauto.
  Qed.
  
  Lemma domain_least {A} (ma : m A) (R : A -> A -> Prop) `{PER _ R} : eqmR R ma ma -> subrelationH (domain ma) R.
  Proof.
    intros G.
    repeat red.
    unfold domain.
    intros.
    apply (H0 R); tauto.
  Qed.

  (* A sanity check about the domains: *)
  Definition singletonR {A:typ} (x:A) : A -> A -> Prop := (fun (a b : A) => a = b /\ a = x).

  Global Instance singletonR_symetric {A:typ} (x:A) : Symmetric (singletonR x).
  Proof.
    repeat red. intros. unfold singletonR in H.
    destruct H; subst; tauto.
  Qed.

  Global Instance singletonR_transitive {A:typ} (x:A) : Transitive (singletonR x).
  Proof.
      repeat red. intros. unfold singletonR in *.
      destruct H, H0; subst; tauto.
  Qed.

  Global Instance singletonR_PER {A:typ} (x:A) : PER (singletonR x).
  Proof.
    split; typeclasses eauto.
  Qed.

  Lemma ret_domain {A:typ} (x:A) : eq_rel (domain (ret @ x)) (singletonR x).
  Proof.
    split.
    - repeat red. intros. 
      unfold domain in H.
      specialize (H (singletonR x) _).
      assert (eqmR (singletonR x) (ret @ x) (ret @ x)).
      { apply eqmR_ret. typeclasses eauto. repeat red. tauto. }
      apply H in H0. red in H0. assumption.
    - repeat red. intros.
      unfold singletonR in H. destruct H; subst.
      eapply eqmR_ret_inv; eauto.
  Qed.

  (*
  Lemma domain_eqmR {A} (m : m A) (R : A -> A -> Prop) `{PER _ R} : eqmR R m m -> eqmR (domain m) m m.
  Proof.
    intros EQ.

    eqmR R m1 m2 -> eqmR S m1 m2 -> eqmR (R /\ S) m1 m2
    
    specialize (eqmR_Proper_mono M (domain m) R (domain_least m R EQ)).
    intros S.
    unfold superrelationH in S. repeat red in S.
   *)
End Domain.


