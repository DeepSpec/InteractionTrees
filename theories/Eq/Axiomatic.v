(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Shallow.

Import ITreeNotations.
Local Open Scope itree.

(* We consider inductive trees to only allow finite proofs of axiomatic equations *)
Inductive ttree (E : Type -> Type) (t : Type) : Type :=
| RetT (_ : t)
| VisT {A} (_ : E A) (_ : A -> ttree E t).
Arguments RetT {E t}.
Arguments VisT {E t A}.

(* We want to have a special bind that imposes on the left hand side to be finite *)
Fixpoint tbind {t u E} (c : ttree E t) (k : t -> ttree E u) : ttree E u :=
  match c with
  | RetT x => k x
  | VisT e g => VisT e (fun x => (tbind (g x) k))
  end.

(* We want to have a special bind that imposes on the left hand side to be finite *)
Fixpoint ubind {t u E} (c : ttree E t) (k : t -> itree E u) : itree E u :=
  match c with
  | RetT x => k x
  | VisT e g => Vis e (fun x => (ubind (g x) k))
  end.

Variant productive {E t}: ttree E t -> Prop :=
 | NotRet: forall {X} (e: E X) k, productive (VisT e k).

Section eqit.

  (* Example just to help think about it, to be moved *)
  Variant CellE: Type -> Type :=
  | ReadE: CellE nat
  | WriteE (n: nat): CellE unit.

  Inductive axiomatic_Cell: forall X, ttree CellE X -> ttree CellE X -> Prop :=
  | write_write: forall n m, axiomatic_Cell unit (VisT (WriteE n) (fun _ => VisT (WriteE m) (fun _ => RetT tt)))
                                       (VisT (WriteE m) (fun _ => RetT tt))
  | write_read: forall n, axiomatic_Cell nat (VisT (WriteE n) (fun _ => VisT ReadE (fun n => RetT n)))
                                      (RetT n).

  Context {E : Type -> Type} {A A': Type} {RA: A -> A' -> Prop}.
  Variable (axioms : forall {t1 t2}, ttree E t1 -> ttree E t2 -> (t1 -> t2 -> Prop) -> Prop).
  Arguments axioms {t1 t2} _ _ _.

  (* Finite proofs of equivalence of [ttree] derived from a set of axioms [axioms] *)

  Variant ImpState : Type -> Type :=
  | GetVar (x : string) : ImpState nat
  | SetVar (x : string) (v : nat) : ImpState unit.

  Inductive Raxiom: ttree E A -> ttree E A' -> Prop :=
  (* | TTrefl: forall t t', RA t t' -> Raxiom t t' *)
  | TTbin {B B': Type}
          (b: ttree E B) (b': ttree E B') (RB: B -> B' -> Prop)
          (k: B -> ttree E A) (k': B' -> ttree E A'):
          axioms b b' RB ->
          (forall x y, RA x y -> Raxiom RA (k x) (k' y)) ->
          Raxiom (tbind a k) (tbind a' k')
  | TTVis {A' B} (e: E B) (k: B -> ttree E A) (k': B -> ttree E A'):
      (forall x, Raxiom (k x) (k' x)) ->
      Raxiom (VisT e k) (VisT e k').

  Variant eqitF (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqitF sim (Ret r1) (Ret r2)
  | EqTau m1 m2
          (REL: sim m1 m2):
      eqitF sim (Tau m1) (Tau m2)
  | EqBind {A A'} (t1: ttree E A) (t2: ttree E A') (k1: A -> itree E _) (k2: A' -> itree E _)
           (RAX: Raxiom t1 t2)
           (REL: forall v, sim (k1 v) (k2 v) : Prop):
      eqitF sim (ubind t1 k1) (ubind t2 k2)
  .
  Hint Constructors eqitF.

  Definition eqit_ b1 b2 vclo sim :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eqitF b1 b2 vclo sim (observe t1) (observe t2).
  Hint Unfold eqit_.

  Definition eqit b1 b2 : itree E R1 -> itree E R2 -> Prop :=
    paco2 eqit_ bot2.



forall a b, R' a b -> |> (k a ~R k' b)
c ~~R' c'
productive c \/ productive c'
------------------------ ("new" Vis bisimulation rule)
 thn c k ~R thn c' k'
