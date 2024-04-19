(** * General-purpose definitions *)

(** Not specific to itrees. *)

(* begin hide *)
From Coq Require Import
     RelationClasses.

From stdpp Require Export
  prelude.

Set Primitive Projections.
(* end hide *)


(** ** Parametric functions *)

(** A notation for a certain class of parametric functions.
    Some common names of things that can be represented by such a type:

    - Natural transformations (functor morphisms)
    - Monad morphisms
    - Event morphisms (if [E] and [F] are simply
      indexed types with no particular structure)
    - Event handlers (if [F] is a monad)
 *)
Notation "E ~> F" := (forall T, E T -> F T)
  (at level 99, right associativity, only parsing) : type_scope.
(* The same level as [->]. *)
(* This might actually not be such a good idea. *)

(** Identity morphism. *)
Definition idM {E : Type -> Type} : E ~> E := fun _ e => e.

(** [void] is a shorthand for [Empty_set]. *)
Notation void := Empty_set.

(* Canonical equivalence relation for a unary type family. *)
Class Eq1 (M : Type -> Type) : Type :=
  eq1 : forall A, M A -> M A -> Prop.

Arguments eq1 {M _ _}.
Declare Scope monad_scope.
Open Scope monad_scope.
Infix "≈" := eq1 (at level 70) : monad_scope.

Class App (T : Type → Type) := ap : ∀ {A B}, T (A → B) → T A → T B.

(* Proof that [eq1] is an equivalence relation. *)
Class Eq1Equivalence (M : Type -> Type) `{Eq1 M} :=
  eq1_equiv : forall A, Equivalence (eq1 (A := A)).

#[global] Existing Instance eq1_equiv.

(* Monad laws up to [M]'s canonical equivalence relation. *)
Class MonadLawsE (M : Type -> Type) `{@Eq1 M, MRet M, MBind M} : Prop :=
  { bind_ret_l : forall A B (f : A -> M B) (x : A), mret x ≫= f ≈ f x
  ; bind_ret_r : forall A (x : M A), x ≫= (fun y => mret y) ≈ x
  ; bind_bind : forall A B C (x : M A) (f : A -> M B) (g : B -> M C),
      (x ≫= f) ≫= g ≈ x ≫= (fun y => f y ≫= g)
  ; Proper_bind : forall {A B},
      (@Proper ((A -> M B) -> M A -> M B)
         (pointwise_relation _ eq1 ==> eq1 ==> eq1)
         mbind)
  }.

#[global] Existing Instance Proper_bind.

Arguments bind_ret_l {M _ _ _ _}.
Arguments bind_ret_r {M _ _ _ _}.
Arguments bind_bind {M _ _ _ _}.
Arguments Proper_bind {M _ _ _ _}.
(** ** Common monads and transformers. *)

Section Monads.

(* id *)
Definition identity (a : Type) : Type := a.

#[global] Instance FMap_identity : FMap identity
  := fun _ _ f => f.

#[global] Instance MRet_identity : MRet identity
  := fun _ a => a.

#[global] Instance MBind_identity : MBind identity
  := fun _ _ k c => k c.

(* either *)
Definition either (e a : Type) : Type := sum e a.

#[global] Instance FMap_either {e} : FMap (either e)
  := fun _ _ f ea => match ea with | inl e => inl e | inr a => inr (f a) end.

#[global] Instance MRet_either {e} : MRet (either e)
  := fun _ a => inr a.

#[global] Instance MBind_either {e} : MBind (either e)
  := fun _ _ k c => match c with | inl e => inl e | inr a => k a end.

(* state *)
Definition state (s a : Type) := s -> prod s a.

#[global] Instance FMap_state {s} : FMap (state s)
  :=  fun _ _ f run s => (fun sa => (fst sa, f (snd sa))) (run s).

#[global] Instance MRet_state {s} : MRet (state s)
  := fun _ a s => (s, a).

#[global] Instance MBind_state {s} : MBind (state s) :=
  fun _ _ k c => fun s => let sa := c s in
                    k (snd sa) (fst sa).

(* reader *)
Definition reader (r a : Type) := r -> a.

#[global] Instance FMap_reader {r} : FMap (reader r)
  :=  fun _ _ f run r => f (run r).

#[global] Instance MRet_reader {r} : MRet (reader r)
  := fun _ a _ => a.

#[global] Instance MBind_reader {r} : MBind (reader r) :=
  fun _ _ k c => fun r => k (c r) r.

(* writer *)
Definition writer := prod.

(* optionT *)

Definition optionT (m : Type -> Type) (a : Type) : Type :=
  m (option a).

#[global] Instance FMap_optionT {m} {Fm : FMap m} : FMap (optionT m)
  := fun _ _ f c => (fun x => match x with | None => None | Some x => Some (f x) end ) <$> c.

#[global] Instance MRet_optionT {m} {Fm : MRet m} : MRet (optionT m)
  := fun _ a => mret (Some a).

#[global] Instance MBind_optionT {m} `{MRet m, MBind m} : MBind (optionT m) :=
  fun _ _ k c => mbind (M := m) (fun oa => match oa with
                                     | None   => mret (M := m) None
                                     | Some a => k a
                                     end) c.

Definition run_optionT {m a} (x : optionT m a) : m (option a)%type := x.

Definition liftOption {a f} `{FMap f} (fa : f a) : optionT f a :=
  Some <$> fa.

(* eitherT *)
Definition eitherT (e : Type) (m : Type -> Type) (a : Type) : Type := m (sum e a).

#[global] Instance FMap_eitherT {e m} `{FMap m} : FMap (eitherT e m)
  := fun _ _ f c => (fun ea => match ea with | inl e => inl e | inr a => inr (f a) end) <$> c.

#[global] Instance MRet_eitherT {e m} `{MRet m} : MRet (eitherT e m)
  := fun _ a => mret (inr a).

#[global] Instance MBind_eitherT {e m} `{MRet m, MBind m} : MBind (eitherT e m)
  := fun _ _ f => mbind (M := m) (fun ea => match ea with | inl e => mret (inl e) | inr a => f a end).

Definition runEither {e m a} (x : eitherT e m a) : m (sum e a) := x.

Definition liftEither {e f a} `{FMap f} (fa : f a) : eitherT e f a := inr <$> fa.

(* stateT *)
Definition stateT (s : Type) (m : Type -> Type) (a : Type) : Type :=
  s -> m (prod s a).

#[global] Instance FMap_stateT {m s} {Fm : FMap m} : FMap (stateT s m)
  :=  fun _ _ f run s => fmap (fun sa => (fst sa, f (snd sa))) (run s).

#[global] Instance MRet_stateT {m s} {Fm : MRet m} : MRet (stateT s m)
  := fun _ a s => mret (s, a).

#[global] Instance MBind_stateT {m s} {Fm : MBind m} : MBind (stateT s m) :=
  fun _ _ k c => fun s => sa ← c s ;
                    k (snd sa) (fst sa).

Definition run_stateT {s m a} (x : stateT s m a) : s -> m (s * a)%type := x.

Definition liftState {s a f} `{FMap f} (fa : f a) : stateT s f a :=
  fun s => pair s <$> fa.

(* readerT *)
Definition readerT (r : Type) (m : Type -> Type) (a : Type) : Type :=
  r -> m a.

#[global] Instance FMap_readerT {m r} {Fm : FMap m} : FMap (readerT r m)
  :=  fun _ _ f run r => fmap f (run r).

#[global] Instance MRet_readerT {m r} {Fm : MRet m} : MRet (readerT r m)
  := fun _ a _ => mret a.

#[global] Instance MBind_readerT {m r} {Fm : MBind m} : MBind (readerT r m) :=
  fun _ _ k c => fun r => v ← c r ;
                    k v r.

Definition run_readerT {r m a} (x : readerT r m a) : r -> m a%type := x.

Definition liftReader {r a f} `{FMap f} (fa : f a) : readerT r f a :=
  fun _ => fa.

(* writerT *)
Definition writerT (w : Type) (m : Type -> Type) (a : Type) : Type :=
  m (prod w a).

End Monads.

(** ** Loop operator *)

(** [iter]: A primitive for general recursion.
    Iterate a function updating an accumulator [I], until it produces
    an output [R].
 *)
Polymorphic Class MonadIter (M : Type -> Type) : Type :=
  iter : forall {R I: Type}, (I -> M (I + R)%type) -> I -> M R.

#[global] Hint Mode MonadIter ! : typeclass_instances.

(** *** Transformer instances *)

(** And the standard transformers can lift [iter].

    Quite easily in fact, no [Monad] assumption needed.
 *)

#[global] Polymorphic Instance MonadIter_stateT {M S} `{MRet M, MBind M, MonadIter M}
  : MonadIter (stateT S M) :=
  fun _ _ step i s =>
    iter (fun si =>
            let s := fst si in
            let i := snd si in
            si' ← step i s;
            mret match snd si' with
              | inl i' => inl (fst si', i')
              | inr r => inr (fst si', r)
              end) (s, i).

#[global] Instance MonadIter_readerT {M S} {AM : MonadIter M} : MonadIter (readerT S M) :=
  fun _ _ step i => fun r =>
    iter (fun i => run_readerT (step i) r) i.

#[global] Instance MonadIter_optionT {M} `{MRet M, MBind M, MonadIter M}
  : MonadIter (optionT M) :=
  fun _ _ step i =>
    iter (fun i =>
            oi ← step i ;
            mret match oi with
              | None => inr None
              | Some (inl i) => inl i
              | Some (inr r) => inr (Some r)
              end) i.

#[global] Instance MonadIter_eitherT {M E} `{MRet M, MBind M, MonadIter M} {AM : MonadIter M}
  : MonadIter (eitherT E M) :=
  fun _ _ step i =>
    iter (fun i =>
            ei ← step i ;
            mret match ei with
              | inl e => inr (inl e)
              | inr (inl i) => inl i
              | inr (inr r) => inr (inr r)
              end) i.

(** And the nondeterminism monad [_ -> Prop] also has one. *)
From stdpp Require Import propset.

Inductive iter_Prop {R I : Type} (step : I -> propset (I + R)) (i : I) (r : R)
  : Prop :=
| iter_done
  : propset_car (step i) (inr r) -> iter_Prop step i r
| iter_step i'
  : propset_car (step i) (inl i') ->
    iter_Prop step i' r ->
    iter_Prop step i r
.

#[global] Polymorphic Instance MonadIter_Prop : MonadIter propset :=
  fun _ _ step i => PropSet (iter_Prop step i).

(* Elementary constructs for predicates. To be moved in their own file eventually *)
(* TODO: should they be entirely replaced with constructions in [propset]? *)
Definition equiv_pred {A : Type} (R S: A -> Prop): Prop :=
  forall a, R a <-> S a.

Definition sum_pred {A B : Type} (PA : A -> Prop) (PB : B -> Prop) : A + B -> Prop :=
  fun x => match x with | inl a => PA a | inr b => PB b end.

Definition prod_pred {A B : Type} (PA : A -> Prop) (PB : B -> Prop) : A * B -> Prop :=
  fun '(a,b) => PA a /\ PB b.

Definition TT {A : Type} : A -> Prop := fun _ => True.
Global Hint Unfold TT sum_pred prod_pred: core.

#[global] Instance equiv_pred_refl  {A} : Reflexive (@equiv_pred A).
Proof.
  split; auto.
Qed.
#[global] Instance equiv_pred_symm  {A} : Symmetric (@equiv_pred A).
Proof.
  red; intros * EQ; split; intros; eapply EQ; auto.
Qed.
#[global] Instance equiv_pred_trans {A} : Transitive (@equiv_pred A).
Proof.
  red; intros * EQ1 EQ2; split; intros; (apply EQ1,EQ2 || apply EQ2,EQ1); auto.
Qed.
#[global] Instance equiv_pred_equiv {A} : Equivalence (@equiv_pred A).
Proof.
  split; typeclasses eauto.
Qed.
