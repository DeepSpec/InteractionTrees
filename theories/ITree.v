Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Section itree.

  Context {E : Type -> Type} {R : Type}.

  Inductive itreeF {itree : Type} :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {u} (e : E u) (k : u -> itree)
  .
  Arguments itreeF _ : clear implicits.

  (** An [itree E R] is the denotation of a program as coinductive
    (possibly infinite) tree where the leaves [Ret] are labeled with
    [R] and every node is either a [Tau] node with one child, or a
    branching node [Vis] with a visible effect [E X] that branches
    on the values of [X]. *)
  CoInductive itree : Type := do
  { observe : itreeF itree }.

  Definition Ret (x : R) : itree := do (RetF x).
  Definition Vis {u} (e : E u) (k : u -> itree) : itree :=
    do (VisF e k).
  Definition Tau (t : itree) : itree := do (TauF t).

End itree.

Arguments itreeF _ _ : clear implicits.
Arguments itree _ _ : clear implicits.

Section bind.
  Context {E : Type -> Type} {T U : Type}.
  Variable k : T -> itree E U.

  (* The [match] in the definition of bind. *)
  Definition bind_match
             (bind : itree E T -> itree E U)
             (c : itree E T) : itree E U :=
    match c.(observe) with
    | RetF r => k r
    | TauF t => Tau (bind t)
    | VisF e h => Vis e (fun x => bind (h x))
    end.

  CoFixpoint bind' (t : itree E T) : itree E U :=
    bind_match bind' t.

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
    match t.(observe) with
    | RetF r => Ret (f r)
    | TauF t => Tau (go t)
    | VisF e k => Vis e (fun x => go (k x))
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

Definition liftE {E : Type -> Type} {X : Type}
           (e : E X) : itree E X :=
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

Lemma observe_bind : forall {E T U} c (k : T -> itree E U),
    observe (bind c k) = match c.(observe) with
                         | RetF r => (k r).(observe)
                         | TauF t => TauF (bind t k)
                         | VisF e h => VisF e (fun x => bind (h x) k)
                         end.
Proof.
  unfold bind, bind', bind_match. unfold observe.
  intros.
  (* note(gmm): i wasn't able to find any way to pattern match on this goal. *)
  change (let z := observe c in
          observe match z with
                  | RetF r => k r
                  | TauF t =>
                    Tau
                      ((cofix bind' (t0 : itree E T) : itree E U :=
                          match observe t0 with
                          | RetF r => k r
                          | TauF t1 => Tau (bind' t1)
                          | @VisF _ _ _ u e h => Vis e (fun x : u => bind' (h x))
                          end) t)
                  | @VisF _ _ _ u e h =>
                    Vis e
                        (fun x : u =>
                           (cofix bind' (t : itree E T) : itree E U :=
                              match observe t with
                              | RetF r => k r
                              | TauF t0 => Tau (bind' t0)
                              | @VisF _ _ _ u0 e0 h0 => Vis e0 (fun x0 : u0 => bind' (h0 x0))
                              end) (h x))
                  end =
          match z with
          | RetF r => observe (k r)
          | TauF t =>
            TauF
              ((cofix bind' (t0 : itree E T) : itree E U :=
                  match observe t0 with
                  | RetF r => k r
                  | TauF t1 => Tau (bind' t1)
                  | @VisF _ _ _ u e h => Vis e (fun x : u => bind' (h x))
                  end) t)
          | @VisF _ _ _ u e h =>
            VisF e
                 (fun x : u =>
                    (cofix bind' (t : itree E T) : itree E U :=
                       match observe t with
                       | RetF r => k r
                       | TauF t0 => Tau (bind' t0)
                       | @VisF _ _ _ u0 e0 h0 => Vis e0 (fun x0 : u0 => bind' (h0 x0))
                       end) (h x))
          end
         ).
  destruct z; try reflexivity.
Defined.
