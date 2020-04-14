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


Class EqMR (m:Type -> Type) : Type :=
  eqmR : forall a b (r : a -> b -> Prop), m a -> m b -> Prop.

Arguments eqmR {m _ _ _}.

(* 
 forall a,  m a -> m a -> Prop
*)
Definition eqm {m:Type -> Type} `{EqMR m} {A} := @eqmR _ _ A A eq.

Arguments eqm {m _ _}.
Infix "≈" := eqm (at level 70) : monad_scope.

Section EqmRRel.
  Context (m : Type -> Type).
  Context {EqMR : @EqMR m}.

  Import RelNotations.
  Local Open Scope relation_scope.

  Class EqmR_OK : Type :=
    {
      eqmR_transport_refl :>  forall {A} (R : A -> A -> Prop), Reflexive R -> Reflexive (eqmR R);
      eqmR_transport_symm :>  forall {A} (R : A -> A -> Prop), Symmetric R -> Symmetric (eqmR R);
      eqmR_transport_trans :> forall {A} (R : A -> A -> Prop), Transitive R -> Transitive (eqmR R);
      eqmR_rel_trans :> forall {A B C} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) (ma : m A) (mb : m B) (mc : m C), eqmR R1 ma mb -> eqmR R2 mb mc -> eqmR (R2 ∘ R1) ma mc;

      (* Could be generalized with some relation compositions? *)
      (* This may follow from eqmR_Proper_mono. *)
      eqmR_Proper :> forall {A B},
          Proper (@eq_rel A B ==> eqmR eq ==> eqmR eq ==> iff) (eqmR);

      eqmR_Proper_mono :> forall {A B},
          Proper (inclusion ==> inclusion) (@eqmR m _ A B)
    }.

End EqmRRel.


Instance eqm_equiv (m:Type -> Type) `{EqMR m} `{@EqmR_OK m _} : forall a, Equivalence (@eqm m _ a).
unfold eqm. split; typeclasses eauto.
Defined.

Section EqmRMonad.
  Context (m : Type -> Type).
  Context {EqMR : @EqMR m}.
  Context {Mm : Monad m}.


Class EqmRMonad :=
  {
    eqmR_ret : forall {A1 A2} (RA : A1 -> A2 -> Prop) (a1:A1) (a2:A2),
      RA a1 a2 <-> eqmR RA (ret a1) (ret a2);

    eqmR_bind : forall {A1 A2 B1 B2}
                  (RA : A1 -> A2 -> Prop)
                  (RB : B1 -> B2 -> Prop)
                  ma1 ma2 (kb1 : A1 -> m B1) (kb2 : A2 -> m B2),
        eqmR RA ma1 ma2 ->
        (forall a1 a2, RA a1 a2 -> eqmR RB (kb1 a1) (kb2 a2)) ->
        eqmR RB (bind ma1 kb1) (bind ma2 kb2);

    eqmR_Proper_bind :> forall {A B}
                     (RA : A -> A -> Prop) (RB : B -> B -> Prop),
        (@Proper (m A%type -> (A -> m B) -> m B)
                 (eqmR RA ==> (RA ==> (eqmR RB)) ==> eqmR RB)
                 bind);
    
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
  Context {EqMR : @EqMR m}.
  Context {Mm : Monad m}.
  
  Local Open Scope monad_scope.

  Class MonadLaws :=
    { bind_ret_l : forall a b (f : a -> m b) (x : a), bind (ret x) f ≈ f x
    ; bind_ret_r : forall a (x : m a), bind x (fun y => ret y) ≈ x
    ; bind_bind : forall a b c (x : m a) (f : a -> m b) (g : b -> m c), bind (bind x f) g ≈ bind x (fun y => bind (f y) g)
    ; Proper_bind :> forall {a b},
        (@Proper (m a%type -> (a -> m b) -> m b)
         (eqm ==> pointwise_relation _ eqm ==> eqm)
         bind)
    }.

End Laws.

Arguments bind_ret_l {m _ _ _ _ _}.
Arguments bind_ret_r {m _ _ _ _ _}.
Arguments bind_bind {m _ _ _ _ _}.
Arguments Proper_bind {m _ _ _ _ _}.

Section MONAD.

  Local Open Scope monad_scope.

  Global Instance monad_eqmR
         {m : Type -> Type} `{Monad m} `{@EqMR m} `{@EqmR_OK m _} `{@EqmRMonad m _ _} :
    @MonadLaws m _ _.
  Proof.
    split; intros.

    - unfold eqm. apply eqmR_bind_ret_l with (RA := eq). assumption.
      repeat red. intros. rewrite H3. reflexivity. reflexivity.
    - unfold eqm. apply eqmR_bind_ret_r with (RA := eq). assumption.
      repeat red. intros. reflexivity.
    - unfold eqm. apply eqmR_bind_bind with (RA := eq)(RB := eq); auto.
      repeat red. intros. rewrite H3. reflexivity.
      repeat red. intros. rewrite H3. reflexivity.
      reflexivity.
    - repeat red.
      intros.
      specialize (@eqmR_Proper_bind m _ _ _ a b eq eq).
      intros. apply H5. assumption.
      repeat red.
      intros.
      unfold pointwise_relation in H4.
      rewrite H6.
      apply H4.
Defined.
End MONAD.



