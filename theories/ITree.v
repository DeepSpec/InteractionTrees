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
| Tau (t : itree E R)
| Vis (e : E) (k : reaction e -> itree E R)
.

Arguments Ret {E R}.
Arguments Tau {E R}.
Arguments Vis {E R}.

(* [id_itree] as a notation makes it easier to
   [rewrite <- match_itree]. *)
Notation id_itree t :=
  match t with
  | Ret r => Ret r
  | Tau t' => Tau t'
  | Vis e k => Vis e k
  end.

Lemma match_itree : forall E R (t : itree E R), t = id_itree t.
Proof. destruct t; auto. Qed.

Arguments match_itree {E R} t.

Section bind.
  Context {E : Effect} {T U : Type}.
  Variable k : T -> itree E U.

  (* The [match] in the definition of bind. *)
  Definition bind_match
             (bind : itree E T -> itree E U)
             (c : itree E T) : itree E U :=
    match c with
    | Ret r => k r
    | Tau t => Tau (bind t)
    | Vis e h => Vis e (fun x => bind (h x))
    end.

  CoFixpoint bind' : itree E T -> itree E U :=
    bind_match bind'.

End bind.

(* Monadic [>>=]: tree substitution, sequencing of computations. *)
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

(** Functorial map ([fmap]) *)
Definition map {E R S} (f : R -> S) : itree E R -> itree E S :=
  cofix go t :=
    match t with
    | Ret r => Ret (f r)
    | Tau t => Tau (go t)
    | Vis e k => Vis e (fun x => go (k x))
    end.

(* Sometimes it's more convenient to work without the type classes
   Monad, etc. When functions using type classes are specialized,
   they simplify easily, so lemmas without classes are easier
   to apply than lemmas with.

   We can also make ExtLib's [bind] opaque, in which case it still
   doesn't hurt to have these notations around.
 *)
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.

Notation "t1 >>= k2" := (bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Definition liftE {E : Effect} (e : E) : itree E (reaction e) :=
  Vis e Ret.

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

(* Basic facts *)

(* Force [bind] for one step. This has the advantage over
   [match_itree] of not leaving an extra [id_itree] in the bind
   case.
 *)
Lemma match_bind {E R S} (t : itree E R) (k : R -> itree E S) :
  (t >>= k)%itree = bind_match k (fun t' => bind t' k) t.
Proof.
  rewrite (match_itree (bind _ _)); simpl;
    destruct t; auto.
  - rewrite <- match_itree; auto.
Qed.
