Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Contextual Implicit.

(* Naming conventions:
   - [python_case] definitions
   - [CamelCase] constructors and classes

   Variables:
   - [E E1 E2 F F1 F2 : Type -> Type] effect types
   - [X Y Z : Type] effect output types
   - [e : E X] effects
   - [R S : Type] return/result types ([Ret : R -> itree E R])
   - [t u : itree E R] itrees
   - [k h : R -> itree E S] itree continuations (iforests?)
 *)

(** An [itree E R] is the denotation of a program as coinductive
    (possibly infinite) tree where the leaves [Ret] are labeled with
    [R] and every node is either a [Tau] node with one child, or a
    branching node [Vis] with a visible effect [E X] that branches
    on the values of [X]. *)
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


Global Instance Monad_itree {E} : Monad (itree E) :=
{ ret := @Ret E
; bind := @Core.bind E
}.


Definition liftE (E : Type -> Type) (X : Type)
           (e : E X) : itree E X :=
  Vis e Ret.

Definition sequ {E R S}
           (t : itree E R) (u : itree E S) : itree E S :=
  bind t (fun _ => u).

(** Functorial map ([fmap]) *)
Definition map {E R S} (f : R -> S) : itree E R -> itree E S :=
  cofix go t :=
    match t with
    | Ret r => Ret (f r)
    | Vis e k => Vis e (fun x => go (k x))
    | Tau t => Tau (go t)
    end.

(** Ignore the result of a tree. *)
Definition ignore {E R} : itree E R -> itree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E R} : itree E R := Tau spin.

Definition forever {E R S} (t : itree E R) : itree E S :=
  cofix forever_t := Core.bindTau t (fun _ => forever_t).

(* Homomorphisms between effects *)
Definition eff_hom (E E' : Type -> Type) : Type :=
  forall t, E t -> itree E' t.

(* Stateful homomorphisms between effects *)
Definition eff_hom_s (s : Type) (E E' : Type -> Type) : Type :=
  forall t, E t -> s -> itree E' (s * t).

(** If we can interpret the effects of a tree as computations in
    another, we can extend that interpretation to the whole tree. *)
Definition hom {E F : Type -> Type}
           (f : eff_hom E F) (R : Type)
: itree E R -> itree F R :=
  cofix hom_f t :=
    match t with
    | Ret r => Ret r
    | Vis e k => Core.bindTau (f _ e) (fun x => hom_f (k x))
    | Tau t => Tau (hom_f t)
    end.
Arguments hom {E F} _ [R] _.

(* todo: We should probably export this using a state transformer.
 *)
Definition hom_state {E F : Type -> Type} {S : Type}
           (f : eff_hom_s S E F) (R : Type)
: itree E R -> S -> itree F (S * R) :=
  cofix homState_f t s :=
    match t with
    | Ret r => Ret (s, r)
    | Vis e k => Core.bindTau (f _ e s) (fun '(s',x) => homState_f (k x) s')
    | Tau t => Tau (homState_f t s)
    end.
Arguments hom_state {_ _} _ [_] _.

(** With a mapping from one effect to one single other effect,
    a more economical mapping is possible, using [Vis] instead
    of [bind]. *)
Definition hoist {E F R}
           (f : forall X, E X -> F X) :
  itree E R -> itree F R :=
  cofix hoist_f m :=
    match m with
    | Ret r => Ret r
    | Vis e k => Vis (f _ e) (fun x => hoist_f (k x))
    | Tau n => Tau (hoist_f n)
    end.

Definition when {E}
           (b : bool) (body : itree E unit) : itree E unit :=
  if b then body else ret tt.
