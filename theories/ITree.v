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

(* [itree] is a monad, with the monadic [Core.bind] defined
   by substitution of [Ret] leaves. However, many generic
   recursive constructions fail the productivity checker,
   hence we will wrap [Core.bind] to work around those issues. *)
Module Core.
(** [itree E] forms a [Monad] *)
Definition bind_body {E R S}
           (t : itree E R)
           (go : itree E R -> itree E S)
           (k : R -> itree E S) : itree E S :=
  match t with
  | Ret r => k r
  | Vis e h => Vis e (fun x => go (h x))
  | Tau t => Tau (go t)
  end.

Definition bind {E R S} (t : itree E R) (k : R -> itree E S) :
  itree E S :=
  (cofix bind_ (t : itree E R) :=
      bind_body t bind_ k) t.

Lemma bind_def_core : forall {E R S} t (k : R -> itree E S),
    bind t k = bind_body t (fun t' => bind t' k) k.
Proof.
  intros.
  rewrite (match_itree (bind _ _)).
  destruct t; auto.
  simpl.
  rewrite <- (match_itree (k r)).
  reflexivity.
Qed.

End Core.

Definition liftE (E : Type -> Type) (X : Type)
           (e : E X) : itree E X :=
  Vis e Ret.

(** Monadic return *)
Definition ret : forall {E R}, R -> itree E R := @Ret.

(** Monadic bind *)
(* We insert a [Tau] in the [Ret] case to make programs/specifications
   neater. This makes [itree] no longer a monad structurally,
   but it remains one in a looser sense as long as [Tau] is
   interpreted as the identity. *)
Definition bind {E R S}
           (t : itree E R) (k : R -> itree E S) : itree E S :=
  Core.bind t (fun r => Tau (k r)).

(* A lemma to unfold [bind]. *)
Lemma bind_def E R S :
  forall t (k : R -> itree E S),
    bind t k =
    Core.bind_body t (fun t' => bind t' k) (fun r => Tau (k r)).
Proof.
  unfold bind.
  intros s k.
  rewrite Core.bind_def_core.
  auto.
Qed.

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
  cofix forever_t := sequ t forever_t.

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
    | Vis e k => bind (f _ e) (fun x => hom_f (k x))
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
    | Vis e k => bind (f _ e s) (fun '(s',x) => homState_f (k x) s')
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

Module ItreeNotations.

Delimit Scope itree_scope with itree.

Notation "c >>= f" := (bind c f)
(at level 50, left associativity) : itree_scope.

Notation "f =<< c" := (bind c f)
(at level 51, right associativity) : itree_scope.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
(at level 100, c1 at next level, right associativity) : itree_scope.

Notation "e1 ;; e2" := (_ <- e1%itree ;; e2%itree)%itree
(at level 100, right associativity) : itree_scope.

Open Scope itree_scope.

End ItreeNotations.
