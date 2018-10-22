From ExtLib.Structures Require Import
     Functor Applicative Monad.

From ITree Require Export Effect.

Set Implicit Arguments.
Set Contextual Implicit.

(** An [itree E R] is the denotation of a program as coinductive
    (possibly infinite) tree where the leaves [Ret] are labeled with
    [R] and every node is either a [Tau] node with one child, or a
    branching node [Vis] with a visible effect [E X] that branches
    on the values of [X]. *)
CoInductive itree (E : Effect) (R : Type) :=
| Ret (r : R)
| Vis (e : E) (k : reaction e -> itree E R)
| Tau (t : itree E R)
.

Arguments Ret {E R}.
Arguments Vis {E R}.
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

Section bind.
  Context {E : Effect} {T U : Type}.
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

(* note(gmm): There needs to be generic automation for monads to simplify
 * using the monad laws up to a setoid.
 * this would be *really* useful to a lot of projects.
 *
 * this will be especially important for this project because coinductives
 * don't simplify very nicely.
 *)

Definition liftE {E : Effect} (e : E) : itree E (reaction e) :=
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

(* Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
   [pure] and [ret] to make the extracted code respect OCaml's
   value restriction. *)
Instance Applicative_itree {E} : Applicative (itree E) :=
{ pure _ := Ret
; ap _ _ f x := bind f (fun f => bind x (fun x => Ret (f x)))
}.

Global Instance Monad_itree {E} : Monad (itree E) :=
{ ret _ := Ret
; bind := @bind E
}.

(** Ignore the result of a tree. *)
Definition ignore {E R} : itree E R -> itree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E R} : itree E R := Tau spin.

(** Repeat a computation infinitely. *)
Definition forever {E R S} (t : itree E R) : itree E S :=
  cofix forever_t := bind t (fun _ => Tau forever_t).

(* this definition exists in ExtLib (or should because it is
 * generic to Monads)
 *)
Definition when {E}
           (b : bool) (body : itree E unit) : itree E unit :=
  if b then body else ret tt.
