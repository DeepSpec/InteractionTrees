From Paco Require Import paco.

From Coq Require Import
     Relations
     RelationClasses
     Program.
     

From ExtLib.Structures Require Import 
     Monad
     Functor
     Applicative.
     
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Import MonadNotation.
Local Open Scope monad_scope.


(* Fuctorial presentation of the itrees constructors. *)
Variant itreeF (E : Type -> Type) (R : Type) (X : Type) :=
  | RetF (r : R)                         (* computation terminating with value r *)
  | TauF (t : X)                         (* "silent" tau transition with child t *)
  | VisF {A} (e : E A) (k : A -> X).     (* visible effect e yielding answer of type A *)
Arguments itreeF _ : clear implicits.

(* The itree datatype ties the knot coinductively *)
CoInductive itree (E : Type -> Type) (R : Type) : Type := 
  go { observe : itreeF E R (itree E R) }.

Arguments itreeF _ _ : clear implicits.
Arguments itree _ _ : clear implicits.


Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).


Inductive void : Type :=.

Section IO.

  Inductive IO : Type -> Type :=
  | Input  : IO nat
  | Output : nat -> IO unit.

  CoFixpoint echo : itree IO void :=
    Vis Input (fun x => Vis (Output x) (fun _ => echo)).

  CoFixpoint spin : itree IO void := Tau spin.

End IO.


Module Monad.
(* Apply the continuation s to the Ret nodes of the itree t *)
Definition bind_match {E : Type -> Type} {R S : Type} (s : R -> itree E S)
           (F : itree E R -> itree E S)
           (t : itree E R) : itree E S :=
  match t.(observe) with
  | RetF r => s r
  | TauF t => Tau (F t)
  | VisF e k => Vis e (fun x => F (k x))
  end.

(* Coinductively tie the knot. *)
Definition bind' {E} {R S} (s : (R -> itree E S)) : itree E R -> itree E S :=
  (cofix bind t := bind_match s bind t).

(* More convenient packaging of the arguments. *)
Definition bind {E R S} (t : itree E R) (k : R -> itree E S) : itree E S :=
  bind' k t.

Definition ret {E R} x : itree E R := Ret x.

(** Repeat a computation infinitely. 

    Note: this definition cannot be moved outside the Monad module because
    the productivity checker can't see the definitions of bind/bind'.
*)
Definition forever {E R S} (t : itree E R) : itree E S :=
  cofix forever_t := bind t (fun _ => Tau forever_t).


End Monad.

Notation "x <- t1 ;; t2" := (Monad.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.


Global Instance Monad_itree {E} : Monad (itree E) :=
{| ret := @Monad.ret E
;  bind := @Monad.bind E
|}.


Notation "t1 >>= k2" := (bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 100, t1 at next level, p pattern, right associativity) : itree_scope.



Definition itree_fmap {E R S} (f : R -> S)  (t : itree E R) : itree E S :=
  bind t (fun x => Ret (f x)).

Definition liftE {E : Type -> Type} {X : Type} (e : E X) : itree E X :=
  Vis e (fun x => Ret x).

(*
(** Ignore the result of a tree. *)
Definition ignore {E R} : itree E R -> itree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E R} : itree E R := Tau spin.
 *)




Instance Functor_itree {E} : Functor (itree E) :=
{ fmap := @itree_fmap E }.

(* Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
   [pure] and [ret] to make the extracted code respect OCaml's
   value restriction. *)
Instance Applicative_itree {E} : Applicative (itree E) :=
{ pure := fun _ x => Ret x
; ap := fun _ _ f x =>
          Monad.bind f (fun f => Monad.bind x (fun x => Ret (f x)))
}.

Lemma bind'_to_bind {E R U} : forall (t: itree E U) (k: U -> itree E R),
    Monad.bind' k t = Monad.bind t k.
Proof. reflexivity. Qed.

Ltac fold_bind := rewrite !bind'_to_bind in *.




Section eq_itree.
  Context {E : Type -> Type} {R : Type}.

  Inductive eq_itreeF (sim : relation (itree E R)) : relation (@itreeF E R (itree E R)) :=
  | EqRet : forall x, eq_itreeF sim (RetF x) (RetF x)
  | EqTau : forall m1 m2
      (REL: sim m1 m2), eq_itreeF sim (TauF m1) (TauF m2)
  | EqVis : forall {u} (e : E u) k1 k2
      (REL: forall v, sim (k1 v) (k2 v)),
      eq_itreeF sim (VisF e k1) (VisF e k2)
  .
  Hint Constructors eq_itreeF.

  Global Instance Reflexive_eq_itreeF sim
  : Reflexive sim -> Reflexive (@eq_itreeF sim).
  Proof.
    red. destruct x; eauto.
  Qed.

  Global Instance Symmetric_eq_itreeF sim 
  : Symmetric sim -> Symmetric (@eq_itreeF sim).
  Proof.
    red. inversion 2; eauto.
  Qed.

  Global Instance Transitive_eq_itreeF sim
  : Transitive sim -> Transitive (@eq_itreeF sim).
  Proof.
    red. inversion 2; inversion 1; eauto.
    subst. dependent destruction H6. dependent destruction H7. eauto.
  Qed.

  Definition eq_itree' (sim: relation (itree E R)) : relation (itree E R) :=
    fun t1 t2 => eq_itreeF sim (observe t1) (observe t2).
  Hint Unfold eq_itree'.

  Lemma eq_itree'_mono : forall x0 x1 r r'
    (IN: @eq_itree' r x0 x1) (LE: forall x2 x3, (r x2 x3 : Prop) -> r' x2 x3 : Prop), eq_itree' r' x0 x1.
  Proof. pmonauto.

  Lemma eq_itreeF_mono : monotone2 eq_itreeF.
  Proof. do 2 red. pmonauto. Qed.

  Definition peq_itree r := paco2 eq_itreeF r.

  Definition eq_itree : relation (itree E R) := peq_itree bot2.

End eq_itree.

