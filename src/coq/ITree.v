Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

(** An [M E X] is the denotation of a program as coinductive (possibly
    infinite) tree where the leaves are labeled with [X] and every node
    is either a [Tau] node with one child, or a branching node [Vis]
    with a visible effect [E Y] that branches on the values of [Y]. *)
CoInductive M (Effect : Type -> Type) X :=
| Ret (x:X)
| Vis {Y: Type} (e : Effect Y) (k : Y -> M Effect X)
| Tau (k: M Effect X)
.

Arguments Ret {Effect X}.
Arguments Vis {Effect X Y}.
Arguments Tau {Effect X}.

(* [idM] as a notation makes it easier to [rewrite <- matchM]. *)
Notation idM i :=
  match i with 
  | Ret x => Ret x
  | Vis e k => Vis e k
  | Tau k => Tau k
  end.

Lemma matchM : forall {E X} (i: M E X), i = idM i.
Proof. destruct i; auto. Qed.

Module Core.
(** [M E] forms a [Monad] *)
Definition bind_body {E X Y}
           (s : M E X)
           (go : M E X -> M E Y)
           (t : X -> M E Y) : M E Y :=
  match s with
  | Ret x => t x
  | Vis e k => Vis e (fun y => go (k y))
  | Tau s' => Tau (go s')
  end.

Definition bind {E X Y} (s : M E X) (t : X -> M E Y) : M E Y :=
  (cofix bind_ (s : M E X) :=
      bind_body s bind_ t) s.

Lemma bind_def_core : forall {E X Y} s (t : X -> M E Y),
    bind s t = bind_body s (fun s => bind s t) t.
Proof.
  intros.
  rewrite matchM.
  destruct s; auto.
  simpl.
  rewrite (@matchM _ _ (t x)) at 2.
  auto.
Qed.

End Core.

Definition liftE (Effect : Type -> Type) (X : Type)
           (e : Effect X) : M Effect X :=
  Vis e Ret.

(** Monadic return *)
Definition ret {Effect X} (x : X) : M Effect X := Ret x.

(** Monadic bind *)
(* We insert a Tau in the Ret case to make programs/specifications
   neater. This makes [M] no longer a monad structurally,
   but it remains one in a looser sense as long as Tau is
   interpreted as the identity. *)
Definition bind {E X Y} (t : M E X) (k : X -> M E Y) : M E Y :=
  Core.bind t (fun x => Tau (k x)).

(* A lemma to unfold [bind]. *)
Lemma bind_def E X Y :
  forall t (k : X -> M E Y),
    bind t k =
    Core.bind_body t (fun t' => bind t' k) (fun x => Tau (k x)).
Proof.
  unfold bind.
  intros s k.
  rewrite Core.bind_def_core.
  auto.
Qed.

Definition sequ {E X Y} (s : M E X) (t : M E Y) : M E Y :=
  bind s (fun _ => t).

(** Functorial map ([fmap]) *)
Definition map {E X Y} (f : X -> Y) : M E X -> M E Y :=
  cofix go (t : M E X) :=
    match t with
    | Ret x => Ret (f x)
    | Vis e k => Vis e (fun y => go (k y))
    | Tau t => Tau (go t)
    end.

(** Ignore the result of a tree. *)
Definition ignore {E X} : M E X -> M E unit := map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E} {X} : M E X := Tau spin.

(** The void type is useful as a return type to [M] to enforce
    infinite programs *)
Inductive void : Type := .

CoFixpoint forever {E} {X} (x : M E X) : M E void :=
  sequ x (forever x).

(** If we can interpret the effects of a tree as computations in
    another, we can extend that interpretation to the whole tree. *)
Definition hom {E F : Type -> Type} {X : Type}
           (f : forall Z, E Z -> M F Z) :
  M E X -> M F X :=
  cofix hom_f t :=
    match t with
    | Ret x => Ret x
    | Vis e k => bind (f _ e) (fun x => hom_f (k x))
    | Tau t => Tau (hom_f t)
    end.

(** With a mapping from one effect to one single other effect,
    a more economical mapping is possible, using [Vis] instead
    of [bind]. *)
Definition hoist {E F X}
           (f : forall Z, E Z -> F Z) :
  M E X -> M F X :=
  cofix hoist_f m :=
    match m with
    | Ret x => Ret x
    | Vis e k => Vis (f _ e) (fun z => hoist_f (k z))
    | Tau n => Tau (hoist_f n)
    end.

Definition when {E} (b : bool) (body : M E unit)
  : M E unit :=
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
