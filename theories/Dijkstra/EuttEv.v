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
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(*





*)
Section EuttEvF.

Context {E1 E2 : Type -> Type}.
Context {R1 R2 : Type}.
Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop ).
Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop ).
Context (RR : R1 -> R2 -> Prop).
Arguments REv {A} {B}.
Arguments RAns {A} {B}.

Inductive euttEvF 
          (vclo : (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop)
          (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2), RR r1 r2 -> euttEvF vclo sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2), sim m1 m2 -> euttEvF vclo sim (TauF m1) (TauF m2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      euttEvF vclo sim (observe t1) ot2 -> euttEvF vclo sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      euttEvF vclo sim ot1 (observe t2) -> euttEvF vclo sim ot1 (TauF t2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B ) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> vclo sim (k1 a) (k2 b) : Prop) -> euttEvF vclo sim (VisF e1 k1) (VisF e2 k2).
(*what if RE is empty? this definition seems to have serious problems*) 
Hint Constructors euttEvF.
Definition euttEv_ (vclo : (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop )
           (sim : itree E1 R1 -> itree E2 R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E2 R2) :=
  euttEvF vclo sim (observe t1) (observe t2).
Hint Unfold euttEv_.
Lemma euttEv_monot (vclo : (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop): 
  (monotone2 vclo) -> monotone2 (euttEv_ vclo).
Proof.
  intros. red in H. red. intros. red. red in IN. induction IN; eauto.
Qed.

Hint Resolve euttEv_monot.

Lemma euttEv_id_monot : monotone2 (@id (itree E1 R1 -> itree E2 R2 -> Prop) ).
Proof. auto. Qed.
 
Hint Resolve euttEv_id_monot.

Definition euttEv : itree E1 R1 -> itree E2 R2 -> Prop := paco2 (euttEv_ id) bot2.

End EuttEvF.


