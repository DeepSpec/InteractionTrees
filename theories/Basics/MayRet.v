From ExtLib Require Import
     Structures.Monad.
From ITree Require Import
     ITree
     Eq.Eq
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.HeterogeneousRelations
     Basics.Monad.

From Paco Require Import paco.

From Coq Require Import Morphisms
     Program.Equality
     Classes.RelationClasses
     Relation_Definitions
.


(*
  Possible way to define mayRet based on impurity?
*)

Section MayRet.

  Context {m : Type -> Type}.
  Context {M : Monad m}.
  Context {E : EqmR m}.
  Context {ML : MonadLaws m}.
  Context {EQM : EqmRMonad m}.

  Definition impure {A} (ma : m A) := ~exists a, eqm ma (ret a).

  Inductive mayRet  : forall A, (m A) -> A -> Prop :=
  | mayRet_ret : forall A (a:A), mayRet A (ret a) a
  | mayRet_bind : forall A B (mb : m B) (k : B -> m A) a b,
      mayRet B mb b -> mayRet A (k b) a -> impure mb ->
      mayRet A (bind mb k) a.

  Definition atomic {A} (ma : m A) :=
    (forall B (mb : m B) (k : B -> m A),
        eqm ma (bind mb k) -> impure mb -> (forall (v:B), mayRet B mb v -> ~impure (k v)))
    /\ impure ma.

  Instance mayRet_Proper {A} : Proper (@eqm m E A ==> eq ==> iff) (mayRet A).
  Proof.
  Admitted.

  Lemma mayret_fmap {A B} :
    forall (ma : m A) (f: A -> B) x,
      mayRet A ma x -> mayRet B (Functor.fmap f ma) (f x).
  Proof.
    intros.
    generalize dependent f.
    induction H.
    - intros f. cbn. unfold liftM.
      rewrite bind_ret_l.
      constructor.
    - intros f. cbn in *. unfold liftM in *.
      rewrite bind_bind.
      eapply mayRet_bind. eassumption.
      eapply IHmayRet2. apply H1.
  Qed.

  Lemma mayret_fmap_ {A B} :
    forall (ma : m A) (f: A -> B) x,
      mayRet B (Functor.fmap f ma) (f x) -> mayRet A ma x.
  Proof.
    intros.
    remember (Functor.fmap f ma) as fm.
    remember (f x) as fx.
    generalize dependent x. generalize dependent ma.
    induction H.
    - intros. subst. cbn in Heqfm. unfold liftM in Heqfm.
      pose proof bind_ret_l.
      specialize (H _ _ (fun x : A => ret (f x)) x).
      cbn in H. rewrite Heqfm in H.
      assert (forall (k : A -> m A0), bind (ret x) k ≈ bind ma k -> (ret x) ≈ ma).
      admit. (* IY: Do we want this "bind inversion"? *)
      specialize (H0 _ H). rewrite <- H0. constructor.
    - intros. subst. cbn in Heqfm. unfold liftM in Heqfm.
      unfold impure, not in H1.
      pose proof bind_bind.
  Admitted. (* IY: absurd: doesn't work unless f is injective. *)

End MayRet.

(*  ------------------------------------------------------------------------- *)
(*
   Misc. notes from discussion:

  (* Class Triggerable (M : (Type -> Type) -> Type -> type := *)
  (*                            { trigger : forall E, E ~> M E }. *)

  Trying to prove this relation between fmap and mayRet:

     mayRet ma x <->
     mayRet (fmap f ma) (f x)


  Test theorems for the state monad:
  impure (get)
  impure (set 3)
  atomic (get)
  atomic ma -> eqmR eq ma (get) \/ exists x, eqmR ma (set x)

  More general case analysis for monadic compuations:
  monadic_cases : forall (ma : m A),
        (exists B, (p : m B) (k : B -> m A), atomic p /\ eqm ma (bind p k))
      \/ exists (a:A), eqm ma (ret a).



        Diverges m := eqmR (fun a b => False) m m
        Halts m := exists k1 k2 : A -> m bool, ~ eqm (bind m k1) (bind m k2)
        Fails m := forall k, eqm m (bind m k)
*)
