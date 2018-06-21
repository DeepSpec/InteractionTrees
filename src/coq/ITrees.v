Require Import Coq.Init.Specif.
From Coq Require Export Morphisms RelationClasses Setoid.
Require Import ProofIrrelevance.

Set Implicit Arguments.
Set Contextual Implicit.

(** An [M E X] is the denotation of a program as coinductive (possibly
    infinite) tree where the leaves are labeled with [X] and every node
    is either a [Tau] node with one child, or a branching node [Vis]
    with a visible event [E Y] that branches on the values of [Y]. *)
CoInductive M (Event : Type -> Type) X := 
| Ret (x:X)
| Vis {Y: Type} (e : Event Y) (k : Y -> M Event X)
| Tau (k: M Event X)
.

Definition idM {E X} (i: M E X) :=
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
  | Tau k => Tau (go k)
  end.

Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  (cofix go (s : M E X) :=
      bind_body s go t) s.


Lemma bind_def_core : forall {E X Y} s (k : X -> M E Y),
    bindM s k = bind_body s (fun s => bindM s k) k.
Proof.
  intros.
  rewrite matchM.
  destruct s; auto.
  simpl.
  rewrite (@matchM _ _ (k x)) at 2.
  auto.
Qed.

End Core.

