From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
     (* Logic.IndefiniteDescription *)
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     ITrace.EuttEv
     Divergence
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant EvAns (E : Type -> Type) : Type -> Type :=
  | evans : forall {A : Type} (ev : E A) (ans : A), EvAns E unit
  (*if you can prove there is no answers, don't need to proved one*)
  | evempty : forall {A : Type} (Hempty : A -> void) (ev : E A), EvAns E void
.

Arguments evans {E}.
Arguments evempty {E}.

Definition itrace (E : Type -> Type) (R : Type) := itree (EvAns E) R.

Definition itrace' (E : Type -> Type) (R : Type) := itree' (EvAns E) R.

Definition ev_stream (E : Type -> Type) := itrace E unit.

Definition Nil {E : Type -> Type} : ev_stream E := Ret tt.

Definition ev_list (E : Type -> Type) := list (EvAns E unit).

Fixpoint ev_list_to_stream {E : Type -> Type} (l : ev_list E) : ev_stream E :=
  match l with
  | nil => Ret tt
  | e :: t => Vis e (fun _ => ev_list_to_stream t) end.

(*one append for traces and streams, get associativity for free from bind_bind*)
Definition append {E R} (s : itrace E unit) (b : itrace E R) :=
  ITree.bind s (fun _ => b).

Notation "s ++ b" := (append s b).

Variant REvRef (E : Type -> Type) : forall (A B : Type), EvAns E A -> E B -> Prop := 
  | rer {A : Type} (e : E A) (a : A) : REvRef E unit A (evans A e a) e
  | ree {A : Type} (e : E A) (Hempty : A -> void) : REvRef E void A (evempty A Hempty e) e
.
Hint Constructors REvRef.

(*shouldn't need an empty case*)
Variant RAnsRef (E : Type -> Type) : forall (A B : Type), EvAns E A -> A -> E B -> B -> Prop :=
  | rar {A : Type} (e : E A) (a : A) : RAnsRef E unit A (evans A e a) tt e a.
Hint Constructors RAnsRef.

Definition trace_refine {E R}  (t : itree E R) (b : itrace E R)  := 
   euttEv (REvRef E) (RAnsRef E) eq b t.


Notation "b ⊑ t" := (trace_refine t b) (at level 70).

Variant must_divergeF {E : Type -> Type} {A : Type} (F : itree E A -> Prop) : itree' E A -> Prop :=
  | MDivTau (t : itree E A) : F t -> must_divergeF F (TauF t)
  | MDivVis (B : Type) (k : B -> itree E A) (e : E B) : 
      (forall b, F (k b)) -> must_divergeF F (VisF e k).
Hint Constructors must_divergeF.

Definition must_diverge_ {E A} (sim : itree E A -> Prop) t := must_divergeF sim (observe t).

Lemma must_divergeF_mono {E A} (sim sim' : itree E A -> Prop) t
      (IN : must_divergeF sim t)
      (LE : sim <1= sim') : must_divergeF sim' t.
Proof.
  induction IN; eauto. 
Qed.

Lemma must_divergeF_mono' {E A} : monotone1 (@must_diverge_ E A).
Proof.
  unfold must_diverge_.
  red. intros. eapply must_divergeF_mono; eauto.
Qed.
Hint Resolve must_divergeF_mono' : paco. 

Definition must_diverge {E A} := paco1 (@must_diverge_ E A) bot1.

Inductive can_converge {E : Type -> Type} {A : Type} (a : A) : itree E A -> Prop :=
| conv_ret (t : itree E A) : t ≈ Ret a -> can_converge a t
| conv_vis (t : itree E A ) {B : Type} (e : E B) (k : B -> itree E A) (b : B) : 
    t ≈ Vis e k -> can_converge a (k b) -> can_converge a t.
Hint Constructors can_converge.

Definition finite {E : Type -> Type} (s : ev_stream E) : Prop := can_converge tt s.

Global Instance itrace_eq {E} : Eq1 (itrace E) := ITreeMonad.Eq1_ITree.
