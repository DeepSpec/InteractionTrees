(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)
Require Import ITree.ITree.
Require Import ITree.Effect.

Require Import ExtLib.Structures.Monad.

Module Type FixSig.
  Section Fix.
    (* the ambient effects *)
    Context {E : Type -> Type}.

    Context {dom : Type}.
    Variable codom : dom -> Type.

    Definition fix_body : Type :=
      forall m, Monad m ->
           (forall t, itree E t -> m t) ->
           (forall x : dom, m (codom x)) ->
           forall x : dom, m (codom x).

    Parameter mfix : fix_body -> forall x : dom, itree E (codom x).

    Axiom mfix_unfold : forall (body : fix_body) (x : dom),
        mfix body x = body (itree E) _ (fun t => id) (mfix body) x.

  End Fix.
End FixSig.

Module FixImpl : FixSig.
  Section Fix.
    (* the ambient effects *)
    Variable E : Type -> Type.

    Variable dom : Type.
    Variable codom : dom -> Type.

    (* the fixpoint effect, used for representing recursive calls *)
    Inductive fixpoint : Type -> Type :=
    | call : forall x : dom, fixpoint (codom x).

    Section mfix.
      (* this is the body of the fixpoint. *)
      Variable f : forall x : dom, itree (sum1 E fixpoint) (codom x).

      Local CoFixpoint homFix {T : Type}
            (c : itree (sum1 E fixpoint) T)
        : itree E T :=
        match c with
        | Ret x => Ret x
        | Vis (inl e) k =>
          Vis e (fun x => homFix (k x))
        | Vis (inr e) k =>
          match e in fixpoint X return (X -> _) -> _ with
          | call x => fun k =>
                       Tau (homFix (bind (f x) k))
          end k
        | Tau x => Tau (homFix x)
        end.

      Definition _mfix (x : dom) : itree E (codom x) :=
        homFix (f x).

      Definition eval_fixpoint T (X : sum1 E fixpoint T) : itree E T :=
        match X with
        | inl e => Vis e Ret
        | inr f0 =>
          match f0 with
          | call x => Tau (_mfix x)
          end
        end.

      Theorem homFix_is_hom : forall {T} (c : itree _ T),
          homFix c = hom eval_fixpoint c.
      Proof. Admitted.

      Theorem _mfix_unroll : forall x, _mfix x = homFix (f x).
      Proof. reflexivity. Qed.

    End mfix.

    Section mfixP.
      (* The parametric representation allows us to avoid reasoning about
       * `homFix` and `eval_fixpoint`. They are (essentially) replaced by
       * beta reduction.
       *
       * The downside, is that the type of the body is a little bit more
       * complex, though one could argue that it is a more abstract encoding.
       *)
      Definition fix_body : Type :=
        forall m, Monad m ->
             (forall t, itree E t -> m t) ->
             (forall x : dom, m (codom x)) ->
             forall x : dom, m (codom x).

      Variable body : fix_body.

      Definition mfix
      : forall x : dom, itree E (codom x) :=
        _mfix
          (body (itree (E +' fixpoint)) _ (fun t : Type => hoist (fun X : Type => inl))
                (fun x0 : dom => Vis (inr (call x0)) Ret)).

      Theorem mfix_unfold : forall x,
          mfix x = body (itree E) _ (fun t => id) mfix x.
      Proof. Admitted.
    End mfixP.
  End Fix.
End FixImpl.

Export FixImpl.