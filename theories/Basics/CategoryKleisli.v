(** * Kleisli category *)

(** The category of "effectful functions", of type [a -> m b],
  for some monad [m]. *)

(** Note that this is not quite a Kleisli category over the
  category [Fun], as the notion of morphism equivalence is
  different. The category [Fun] uses pointwise equality,
  [eq ==> eq], while [Kleisli m] uses pointwise equivalence,
  [eq ==> eqm], for an equivalence relation [eqm] associated
  with the monad [m]. The right underlying category for [Kleisli]
  would be a category of setoids and respectful functions, but
  this seems awkward to program with. Investigating this
  question further is future work.
 *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.

From ITree Require Import
     Typ
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
     Basics.Monad
     Basics.HeterogeneousRelations
.

Import CatNotations.
Open Scope cat_scope.


Implicit Types m : typ -> typ.
Implicit Types a b c : typ.

Definition Kleisli m a b : Type := a -=-> m b.

(* SAZ: We need to show how these are intended to be used. *)
(** A trick to allow rewriting in pointful contexts. *)
(* Definition Kleisli_arrow {m a b} : (a -> m b) -> Kleisli m a b := fun f => f. *)
Definition Kleisli_apply {m a b} : Kleisli m a b -> (a -> m b) := typ_proper_app.

Section Pure.
  Context {m : typ -> typ}.
  Context {m_Monad : Monad typ_proper m}.

  (* We go back to our EqmR definition, which is necessary if we want a notion
   * of "agrees" for our bind function.
   *
   * EqmRMonad is defined using typ's and fufills [CategoryMonad] monad laws.
   *)
  Context {EqM: EqmR m} {EqmR : EqmR_OK m} {EqmRMonad : EqmRMonad m}.

  Definition pure_ {a b} (f : a -=-> b) : a -> m b :=
    fun x => ret @ (f @ x).

  Program Definition pure {a b} (f : a -=-> b) : Kleisli m a b :=
    -=->! (pure_ f) _.
  Next Obligation.
    repeat intro.
    apply eqmR_equal, eqmR_ret; eauto.
    rewrite H. simpl; reflexivity.
  Qed.

End Pure.

Section Instances.
  Context {m : typ -> typ}.
  Context {m_Monad : Monad typ_proper m}.

  (* We go back to our EqmR definition, which is necessary if we want a notion
   * of "agrees" for our bind function.
   *
   * EqmRMonad is defined using typ's and fufills [CategoryMonad] monad laws.
   *)
  Context {EqM: EqmR m} {EqmR : EqmR_OK m} {EqmRMonad : EqmRMonad m}.

  (* IY: Why doesn't coercion work here?*)
  Global Instance Eq2_Kleisli : Eq2 (Kleisli m) :=
    fun (a:typ) (b:typ) f g => pointwise_relation _ (↓ (eqm (m := m) (A := b))) (` f) (` g).

  Definition cat_ a b c (u : (Kleisli m a b)) (v : Kleisli m b c) : a -> m c := 
    fun (x:a) => (@bind _ _ m m_Monad _ _ v) @ (u @ x).

  Program Definition catK : Cat (Kleisli m) :=
    fun a b c (u : (Kleisli m a b)) (v : Kleisli m b c) =>
      -=->! (cat_ a b c u v) _.
  Next Obligation.
    do 2 red.
    unfold cat_.
    intros.
    rewrite H.
    apply Proper_typ_proper_app.
    - apply eq2_Reflexive.
    - destruct u. red. destruct (m b). cbn in *. eapply p.  PER_reflexivity.
  Qed.

  Global Instance Cat_Kleisli : Cat (Kleisli m) := catK.

  Definition map {a b c} (g:b -=-> c) (ab : Kleisli m a b) : Kleisli m a c :=
     cat ab (pure g).

  Program Definition initialK : Initial (Kleisli m) bot_typ :=
    fun a => -=->! (fun v => match _ : False with end) _.
  Next Obligation.
    repeat red. intros. destruct H.
  Qed.

  Global Instance Initial_Kleisli : Initial (Kleisli m) bot_typ :=
    initialK.

  Global Instance Id_Kleisli : Id_ (Kleisli m) :=
    fun a => pure (id_ a).

  Program Definition caseK : Case (Kleisli m) sum_typ :=
    fun _ _ _ l r => (case_typ_proper l r).

  Global Instance Inl_Kleisli : Inl (Kleisli m) sum_typ :=
    fun _ _ => pure inl_typ_proper.

  Global Instance Inr_Kleisli : Inr (Kleisli m) sum_typ :=
    fun _ _ => pure inr_typ_proper.

  Print Graph.

  (* IY TODO: Category theory version (or typ version) of Basics? *)
  Class MonadIter (M : typ -> typ) :=
    iter : forall {R I: typ}, (I -=-> M (I ⨥ R)%type) -> (I -=-> M R).

  Global Instance Iter_Kleisli {MI: MonadIter m} : Iter (Kleisli m) sum_typ :=
    fun a b =>  iter (I := a) (R := b).

End Instances.
