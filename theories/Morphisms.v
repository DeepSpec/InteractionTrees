(** The semantics of an interaction tree [itree E ~> M] can be
    derived from semantics given for every individual effect
    [E ~> M].

    We define the following terminology for this library.
    Other sources may have different usages for the same or related
    words.

    The notation [E ~> F] means [forall T, E T -> F T]
    (in [ITree.Basics]).
    It can mean many things, including the following.

    - The semantics of itrees are given as monad morphisms
      [itree E ~> M], also called "interpreters".

    - "Itree interpreters" (or "itree morphisms") are monad morphisms
      [itree E ~> itree F]. Most interpreters in this library are
      actually itree interpreters.

    This module provides various ways of defining interpreters
    from effect handlers and other similar structures.

    - "Effect handlers" are functions [E ~> M] where [M] is a monad.

    - "Itree effect handlers" are functions [E ~> itree F].

    Categorically, this boils down to saying that [itree] is a free
    monad (not quite, but close enough).
 *)

From ExtLib Require
     Structures.Monoid.

From ITree Require Import
     Basics
     Core
     Effect.Sum.

Open Scope itree_scope.

(** [itreeF] eliminator, where the codomain is in the [itree]
    monad, a building block for itree monad morphisms. *)
Definition handleF {E F : Type -> Type} {I R : Type}
           (tau : I -> itree F R)
           (vis : forall U, E U -> (U -> I) -> itree F R)
           (ot : itreeF E R I) : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t' => Tau (tau t')
  | VisF e k => vis _ e k
  end.
Hint Unfold handleF.

(** A variant of [handleF] that treats [inr1] effects like [Tau]. *)
Definition handleF1 {E F : Type -> Type} {I R : Type}
           (tau : I -> itree F R)
           (vis : forall U, E U -> (U -> I) -> itree F R)
           (ot : itreeF (E +' F) R I) : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t' => Tau (tau t')
  | VisF ef k =>
    match ef with
    | inl1 e => vis _ e k
    | inr1 f => Vis f (fun x => tau (k x))
    end
  end.
Hint Unfold handleF1.

(** Shallow effect handling: pass the first [Vis] node to the
    given handler [h]. *)
Definition handle {E F : Type -> Type} {R : Type}
           (h : forall U, E U -> (U -> itree E R) -> itree F R) :
  itree E R -> itree F R :=
  cofix handle_ t := handleF handle_ h (observe t).
Hint Unfold handle.

(** An itree effect handler [E ~> itree F] defines an
    itree morphism [itree E ~> itree F]. *)
Definition interp {E F : Type -> Type} (h : E ~> itree F) :
  itree E ~> itree F := fun R =>
  cofix interp_ t :=
    handleF interp_
            (fun _ e k => Tau (ITree.bind (h _ e)
                                          (fun x => interp_ (k x))))
            (observe t).
(* N.B.: the guardedness of this definition relies on implementation
   details of [bind]. *)

(** Interpret the first effect [E] in a sum [E +' F] into
    the rest of the sum [F].

    Compared to [interp], this inserts fewer [Tau] nodes, which
    allows a few equations to be bisimularities ([eq_itree]) instead
    of up-to-tau equivalences ([eutt]).
 *)
Definition interp1 {E F : Type -> Type} (h : E ~> itree F) :
  itree (E +' F) ~> itree F := fun R =>
  cofix interp1_ t :=
    handleF interp1_
            (fun _ ef k =>
               match ef with
               | inl1 e => Tau (ITree.bind (h _ e)
                                           (fun x => interp1_ (k x)))
               | inr1 f => Vis f (fun x => interp1_ (k x))
               end)
            (observe t).

(** A plain effect morphism [E ~> F] defines an itree morphism
    [itree E ~> itree F]. *)
Definition translate {E F : Type -> Type} (h : E ~> F) :
  itree E ~> itree F := fun R =>
  cofix translate_ t :=
    handleF translate_
            (fun _ e k => Vis (h _ e) (fun x => translate_ (k x)))
            (observe t).

(** Effects [E, F : Type -> Type] and itree [E ~> itree F] form a
    category. *)
(* TODO: check that [itree] is a monad, so that category is its
   Kleisli category. *)

(* todo(gmm): it would be good to have notation for this.
 * - if there was a "category" class like in Haskell, then we could
 *   get composition from something like that.
 *)
Definition eh_compose {A B C} (g : B ~> itree C) (f : A ~> itree B) :
  A ~> itree C :=
  fun _ e => interp g _ (f _ e).

Definition eh_id {A} : A ~> itree A := @ITree.liftE A.

(** Standard interpreters *)

Import ITree.Basics.Monads.

(* TODO: refactor these three... *)

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

Definition interp_state {E F S} (h : E ~> stateT S (itree F)) :
  itree E ~> stateT S (itree F) :=
  fun R =>
    cofix interp_state_ t s :=
      match t.(observe) with
      | RetF r => Ret (s, r)
      | VisF e k =>
        Tau (ITree.bind (h _ e s) (fun sx =>
               interp_state_ (k (snd sx)) (fst sx)))
      | TauF t => Tau (interp_state_ t s)
      end.

Definition interp1_state {E F S} (h : E ~> stateT S (itree F)) :
  itree (E +' F) ~> stateT S (itree F) :=
  fun R =>
    cofix interp1_state_ t s :=
      match t.(observe) with
      | RetF r => Ret (s, r)
      | VisF ef k =>
        match ef with
        | inl1 e =>
          let sx := h _ e s in
          Tau (ITree.bind (h _ e s) (fun sx =>
                 interp1_state_ (k (snd sx)) (fst sx)))
        | inr1 f => Vis f (fun x => interp1_state_ (k x) s)
        end
      | TauF t => Tau (interp1_state_ t s)
      end.

Definition translate1_state {E F S} (h : E ~> state S) :
  itree (E +' F) ~> stateT S (itree F) :=
  fun R =>
    cofix translate1_state_ t s :=
      match t.(observe) with
      | RetF r => Ret (s, r)
      | VisF ef k =>
        match ef with
        | inl1 e => let sx := h _ e s in
                    Tau (translate1_state_ (k (snd sx)) (fst sx))
        | inr1 f => Vis f (fun x => translate1_state_ (k x) s)
        end
      | TauF t => Tau (translate1_state_ t s)
      end.

(** The "reader" and "writer" variants are specializations
    of the above stateful morphisms when the state cannot
    be changed or read (i.e., append only). *)

Definition interp_reader {E F R} (h : R -> E ~> itree F) :
  R -> itree E ~> itree F :=
  fun r => interp (h r).

Definition interp1_reader {E F R} (h : R -> E ~> itree F) :
  R -> itree (E +' F) ~> itree F :=
  fun r => interp1 (h r).

Definition translate1_reader {E F R} (h : R -> E ~> identity) :
  R -> itree (E +' F) ~> itree F :=
  fun r => interp1 (fun _ e => Ret (h r _ e)).

Import ExtLib.Structures.Monoid.

Definition map_fst {A A' B} (f : A -> A') : A * B -> A' * B :=
  fun '(a, b) => (f a, b).

Definition interp_writer {E F W} {Monoid_W : Monoid W} (h : E ~> writerT W (itree F)) :
  itree E ~> writerT W (itree F) :=
  fun _ t =>
    interp_state
      (fun _ e s => ITree.map (map_fst (monoid_plus Monoid_W s)) (h _ e))
      _ t (monoid_unit Monoid_W).

(* todo(gmm): this can be stronger if we allow for a `can_returnE` *)
Inductive can_return {E : Type -> Type} {t : Type} : itree E t -> t -> Prop :=
| can_return_Ret {x} : can_return (Ret x) x
| can_return_Tau {tr x} (_ : can_return tr x) : can_return (Tau tr) x
| can_return_Vis {u e k} {x: u} {res} (_ : can_return (k x) res)
  : can_return (Vis e k) res.

(** A propositional "interpreter"
    This can be useful for non-determinism.
 *)
Section interp_prop.
  Context {E F : Type -> Type}.

  Definition eff_hom_prop : Type :=
    forall t, E t -> itree F t -> Prop.

  CoInductive interp_prop (f : eff_hom_prop) (R : Type)
  : itree E R -> itree F R -> Prop :=
  | ipRet : forall x, interp_prop f R (Ret x) (Ret x)
  | ipVis : forall {T} {e : E T} {e' : itree F T}
              (k : _ -> itree E R) (k' : T -> itree F R),
      f _ e e' ->
      (forall x,
          can_return e' x ->
          interp_prop f R (k x) (k' x)) ->
      interp_prop f R (Vis e k) (ITree.bind e' k')
  | ipDelay : forall a b, interp_prop f R a b ->
                     interp_prop f R (Tau a) (Tau b).

End interp_prop.
Arguments eff_hom_prop _ _ : clear implicits.

(** An extensional stateful handler *)
Section eff_hom_e.
  Context {E F : Type -> Type}.

  (* note(gmm): you should be able to add effects here
   * using a monad transformer. In that case, the type
   * of `eval` is:
   *
   *   forall t, E t -> m (itree F) (t * eff_hom_e)
   *
   * but you have the usual conditions on strictly positive uses
   *)
  CoInductive eff_hom_e : Type :=
  { eval : forall t, E t -> itree F (eff_hom_e * t) }.

  CoFixpoint interp_e (h : eff_hom_e) : itree E ~> itree F :=
    fun R t =>
      handleF (interp_e h _)
              (fun _ e k => ITree.bind (h.(eval) _ e)
                     (fun '(h', x) => Tau (interp_e h' _ (k x))))
              (observe t).

End eff_hom_e.

Section into.
  Context {E F : Type -> Type}.

  Definition into (h : E ~> itree F) : (E +' F) ~> itree F :=
    fun _ e =>
      match e with
      | inl1 e => h _ e
      | inr1 e => ITree.liftE e
      end.

  Definition into_state {s} (h : E ~> stateT s (itree F)) :
    (E +' F) ~> stateT s (itree F) :=
    fun _ e s =>
      match e with
      | inl1 e => h _ e s
      | inr1 e => Vis e (fun x => Ret (s, x))
      end.

  Definition into_reader {R} (h : R -> E ~> itree F) :
    R -> E +' F ~> itree F :=
    fun r _ e =>
      match e with
      | inl1 e => h r _ e
      | inr1 e => ITree.liftE e
      end.

  Definition into_writer {W} (Monoid_W : Monoid W)
             (h : E ~> writerT W (itree F))
    : E +' F ~> writerT W (itree F) :=
    fun _ e =>
      match e with
      | inl1 e => h _ e
      | inr1 e => Vis e (fun x => Ret (monoid_unit Monoid_W, x))
      end.

  (* todo(gmm): is the a corresponding definition for `eff_hom_p`? *)

End into.
