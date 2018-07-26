Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Contextual Implicit.

(** An [itree E R] is the denotation of a program as coinductive
    (possibly infinite) tree where the leaves [Ret] are labeled with
    [R] and every node is either a [Tau] node with one child, or a
    branching node [Vis] with a visible effect [E X] that branches
    on the values of [X]. *)

(** This is almost exactly the kind of more powerful free monad I needed *)
CoInductive itree (E : Type -> Type) (R : Type) :=
| Ret (r : R)
| Vis {X : Type} (e : E X) (k : X -> itree E R)
| Tau (t : itree E R)
.

Arguments Ret {E R}.
Arguments Vis {E R X}.
Arguments Tau {E R}.

(* [id_itree] as a notation makes it easier to
   [rewrite <- match_itree]. *)
Notation id_itree t :=
  match t with
  | Ret r => Ret r
  | Vis e k => Vis e k
  | Tau t => Tau t
  end.

Lemma match_itree : forall E R (t : itree E R), t = id_itree t.
Proof. destruct t; auto. Qed.

Arguments match_itree {E R} t.

Module Core.

  Section bind.
    Context {E : Type -> Type} {T U : Type}.
    Variable k : T -> itree E U.

    CoFixpoint bind' (c : itree E T) : itree E U :=
      match c with
      | Ret r => k r
      | Vis e k' => Vis e (fun x => bind' (k' x))
      | Tau t => Tau (bind' t)
      end.
  End bind.

  Definition bind {E T U}
             (c : itree E T) (k : T -> itree E U)
  : itree E U :=
    bind' k c.

  Definition bindTau {E T U}
             (c : itree E T) (k : T -> itree E U)
  : itree E U :=
    match c with
    | Ret r => Tau (k r)
    | Vis e k' => Vis e (fun x => bind (k' x) k)
    | Tau x => Tau (bind x k)
    end.

End Core.

(* note(gmm): There needs to be generic automation for monads to simplify
 * using the monad laws up to a setoid.
 * this would be *really* useful to a lot of projects.
 *
 * this will be especially important for this project because coinductives
 * don't simplify very nicely.
 *)


Definition liftE {E : Type -> Type} {X : Type}
           (e : E X) : itree E X :=
  Vis e Ret.

(** Functorial map ([fmap]) *)
Local Definition map {E R S} (f : R -> S) : itree E R -> itree E S :=
  cofix go t :=
    match t with
    | Ret r => Ret (f r)
    | Vis e k => Vis e (fun x => go (k x))
    | Tau t => Tau (go t)
    end.

Instance Functor_itree {E} : Functor (itree E) :=
{ fmap := @map E }.

Instance Applicative_itree {E} : Applicative (itree E) :=
{ pure := @Ret E
; ap _ _ f x := Core.bind f (fun f => Core.bind x (fun x => Ret (f x)))
}.

Global Instance Monad_itree {E} : Monad (itree E) :=
{ ret  := @Ret E
; bind := @Core.bind E
}.


(** Ignore the result of a tree. *)
Definition ignore {E R} : itree E R -> itree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E R} : itree E R := Tau spin.

Definition forever {E R S} (t : itree E R) : itree E S :=
  cofix forever_t := Core.bindTau t (fun _ => forever_t).


(* this definition exists in ExtLib (or should because it is
 * generic to Monads)
 *)
Definition when {E}
           (b : bool) (body : itree E unit) : itree E unit :=
  if b then body else ret tt.
