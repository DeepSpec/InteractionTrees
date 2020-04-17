(** * Monad laws and associated typeclasses *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ExtLib Require Export
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.HeterogeneousRelations
     Basics.Function.
(* end hide *)

Set Primitive Projections.

(* We consider heterogeneous relations on computations parameterized by a relation on the return types *)
(* Rq: if we make [EqMR] a singleton class, the type checker tends to craft dumb instances for itself behind our back.
   I wrapped it up in a record, it seems to prevent this behavior.
 *)
Class EqmR (m:Type -> Type) : Type :=
  { eqmR : forall A B (R : relation A B), relation (m A) (m B)}.

Arguments eqmR {m _} [A B].

(*
  The more traditional notion of monadic equivalence is recovered at the equality relation
  [forall A,  m A -> m A -> Prop]
*)
Definition eqm {m:Type -> Type} `{EqmR m} {A} := eqmR (@eq A).

(* YZ: I don't think [A] should be maximally inserted, but putting it back as is for now for retro-compatibility *)
Arguments eqm {m _ A}.
Infix "≈" := eqm (at level 70) : monad_scope.

Section EqmRRel.
  Context (m : Type -> Type).
  Context {EqMR : EqmR m}.

  Import RelNotations.
  Local Open Scope relation_scope.

  (* Requirements of well-formedness of [eqmR] *)
  Class EqmR_OK : Type :=
    {
    (* [eqmR] should transport elementary structures of the relation [R] *)
    (* Question: should it transport anti-symmetry? *)

      eqmR_transport_refl :>  forall {A} (R : relation A A), Reflexive R  -> Reflexive (eqmR R);
      eqmR_transport_symm :>  forall {A} (R : relation A A), Symmetric R  -> Symmetric (eqmR R);
      eqmR_transport_trans :> forall {A} (R : relation A A), Transitive R -> Transitive (eqmR R);

      (* [eqmR] is associative by composing the underlying relations *)
      eqmR_rel_trans : forall {A B C} (R1 : relation A B) (R2 : relation B C)
                         (ma : m A) (mb : m B) (mc : m C),
          eqmR R1 ma mb ->
          eqmR R2 mb mc ->
          eqmR (R2 ∘ R1) ma mc;

      eqmR_lift_transpose : forall {A B} (R : relation A B), eq_rel (eqmR †R) (†(eqmR R));

      (* [eqmR] respects extensional equality of the underlying relation
         and [eqm] on both arguments over the monad *)
      eqmR_Proper :> forall {A B},
          Proper (eq_rel ==> eqmR eq ==> eqmR eq ==> iff) (@eqmR _ _ A B);

      (* [eqmR] is monotone as a morphism on relations *)
      eqmR_Proper_mono :> forall {A B},
          Proper (@inclusion _ _ ==> @inclusion _ _) (@eqmR m _ A B)
    }.

End EqmRRel.

(* In particular, well-formedness of [eqmR] recovers that [eqm] is an equivalence relation *)
Instance eqm_equiv (m:Type -> Type) `{EqmR m} `{EqmR_OK m}
  : forall A, Equivalence (@eqm m _ A).
Proof.
  unfold eqm; split; typeclasses eauto.
Qed.

Section EqmRMonad.
  Context (m : Type -> Type).
  Context {EqMRm : EqmR m}.
  Context {Mm : Monad m}.

  (* Generalization of monadic laws.
     These are of two quite distinct natures:
     * Heterogeneous generalizations of the usual three monad laws
     * Reasoning principles relating [eqmR R] to [R]
   *)
  Class EqmRMonad :=
    {
    eqmR_ret : forall {A1 A2} (RA : A1 -> A2 -> Prop) (a1:A1) (a2:A2),
        RA a1 a2 <-> eqmR RA (ret a1) (ret a2);

    (* YZ: [eqmR_bind] is _exactly_ (well, with order of arguments reshuffled) the same as [eqmR_Proper_bind].
       Commenting it out for now, to remove later.
     *)

    (*
    eqmR_bind : forall {A1 A2 B1 B2}
                  (RA : A1 -> A2 -> Prop)
                  (RB : B1 -> B2 -> Prop)
                  ma1 ma2 (kb1 : A1 -> m B1) (kb2 : A2 -> m B2),
        eqmR RA ma1 ma2 ->
        (forall a1 a2, RA a1 a2 -> eqmR RB (kb1 a1) (kb2 a2)) ->
        eqmR RB (bind ma1 kb1) (bind ma2 kb2);
     *)

    (* Question: The following helps _proving_ [eqmR _ (bind _ _)].
       Should we require something to invert such an hypothesis?
     *)
    eqmR_Proper_bind :> forall {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop),
        (Proper (eqmR RA ==> (RA ==> (eqmR RB)) ==> eqmR RB) bind);

    eqmR_bind_ret_l : forall {A B}
                        (RA : A -> A -> Prop)
                        (RB : B -> B -> Prop)
                        (f : A -> m B)
                        (f_OK : Proper (RA ==> (eqmR RB)) f)
                        (a : A)
                        (a_OK : RA a a),
        eqmR RB (bind (ret a) f) (f a);


    eqmR_bind_ret_r : forall {A}
                        (RA : A -> A -> Prop)
                        (ma : m A)
                        (ma_OK : eqmR RA ma ma),
        eqmR RA (bind ma (fun y => ret y)) ma;

    eqmR_bind_bind : forall {A B C}
                       (RA : A -> A -> Prop)
                       (RB : B -> B -> Prop)
                       (RC : C -> C -> Prop)
                       (f : A -> m B)
                       (f_OK : Proper (RA ==> (eqmR RB)) f)
                       (g : B -> m C)
                       (g_OK : Proper (RB ==> (eqmR RC)) g)
                       (ma : m A)
                       (ma_OK : eqmR RA ma ma),
        eqmR RC (bind (bind ma f) g)  (bind ma (fun y => bind (f y) g))
    }.

End EqmRMonad.

Section Laws.

  Context (m : Type -> Type).
  Context {EqMR : EqmR m}.
  Context {Mm : Monad m}.

  Local Open Scope monad_scope.

  Class MonadLaws :=
    { bind_ret_l : forall a b (f : a -> m b) (x : a), bind (ret x) f ≈ f x
    ; bind_ret_r : forall a (x : m a), bind x (fun y => ret y) ≈ x
    ; bind_bind : forall a b c (x : m a) (f : a -> m b) (g : b -> m c), bind (bind x f) g ≈ bind x (fun y => bind (f y) g)
    ; Proper_bind :> forall {a b},
        (Proper (eqm (A := a) ==> pointwise_relation _ (eqm (A := b)) ==> eqm (A := _)) bind)
    }.

End Laws.

Arguments bind_ret_l {m _ _ _} [a b] f x.
Arguments bind_ret_r {m _ _ _} [a] x.
Arguments bind_bind {m _ _ _} [a b c] x f g.
Arguments Proper_bind {m _ _ _} [a b].

Section MONAD.

  Local Open Scope monad_scope.

  Global Instance monad_eqmR {m} `{EqmRm: EqmRMonad m} {EqmROKm: EqmR_OK m} : MonadLaws m.
  Proof.
    split; intros.

    - unfold eqm. apply eqmR_bind_ret_l with (RA := eq); auto.
      repeat intro; subst; reflexivity.
    - unfold eqm. apply eqmR_bind_ret_r with (RA := eq); auto.
      reflexivity.
    - unfold eqm. apply eqmR_bind_bind with (RA := eq)(RB := eq); auto.
      repeat intro; subst; reflexivity.
      repeat intro; subst; reflexivity.
      reflexivity.
    - repeat intro.
      rewrite H.
      (* Interesting (or annoying I guess):
         if [EqMR] is defined as a singleton class, then here [eapply eqmR_Proper_bind]
         leads the type checker to happily craft its own stupid relation as an instance:
         [(fun (A B : Type) (_ : A -> B -> Prop) (_ : m A) (_ : m B) => @bind m Mm a b y x0 ≈ @bind m Mm a b y y0)]
         where of course we would have expected it to pick the [EqMRm: EqMR m] that we have in the context.
         If we make [eqmR] a proper class with a single field however, it works as expected.
       *)
      eapply eqmR_Proper_bind; eauto.
      reflexivity.
      repeat intro; subst; apply H0.
  Qed.

End MONAD.
