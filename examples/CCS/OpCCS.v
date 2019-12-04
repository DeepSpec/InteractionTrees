From ITree Require Import
     ITree
     ITreeDefinition.

From Coq Require Import
     Lists.ListSet
     Lists.List
     Program.Equality
     List
     Arith.PeanoNat.

Import ListNotations.
Set Implicit Arguments.


(* Operational Semantics for CCS without Hide or Bang. *)

Section ccs_op.

Variable A: Type.

Variant Label : Type :=
| In (l : A) : Label
| Out (l : A) : Label
.

Inductive ccs : Type :=
| Done : ccs
| Action : Label -> ccs -> ccs
| Choice : ccs -> ccs -> ccs
| Par : ccs -> ccs -> ccs
.

Inductive step {l : A} : option Label -> ccs -> ccs -> Prop :=
| step_Send (t : ccs) :
    step (Some (In l)) (Action (In l) t) t
| step_Recv (t : ccs) :
    step (Some (Out l)) (Action (Out l) t) t
| step_Choice_L (u v u' : ccs) (A' : option Label) :
    step A' u u' -> step A' (Choice u v) u'
| step_Choice_R (u v v' : ccs) (A' : option Label) :
    step A' v v' -> step A' (Choice u v) v'
| step_Par_L (u v u' : ccs) (A' : option Label) :
    step A' u u' -> step A' (Par u v) (Par u' v)
| step_Par_R (u v v' : ccs) (A' : option Label) :
    step A' v v' -> step A' (Par u v) (Par u v')
| step_Par_Comm1 (u v u' v' : ccs) :
    step (Some (In l)) u u' -> step (Some (Out l)) v v' ->
    step None u' v'
| step_Par_Comm2 (u v u' v' : ccs) :
    step (Some (Out l)) u u' -> step (Some (In l)) v v' ->
    step None u' v'
.

End ccs_op.

Arguments Done {_}.

(* Example Labelled Transition Systems. *)
Definition ex1 : ccs nat :=
  Choice (Par Done Done) (Action (In 1) Done).

Definition ex2 : ccs nat :=
  Par (Action (In 1) Done) (Action (Out 1) Done).

Lemma label_nat_dec_eq :
  forall x y : Label nat, {x = y} + {x <> y}.
Proof.
  intros. pose proof Nat.eq_dec.
  destruct x, y.
  Admitted.

Arguments empty_set {_}.

(* Trace Semantics. *)

Fixpoint trace (c : ccs nat) (acc : list (Label nat)) : set (list (Label nat)) :=
  match (c : ccs nat) with
  | Action A c1 => trace c1 (A :: acc)
  | Par c1 c2 =>
    set_inter (list_eq_dec label_nat_dec_eq) (trace c1 acc) (trace c2 acc)
  | Choice c1 c2 =>
    set_union (list_eq_dec label_nat_dec_eq) (trace c1 acc) (trace c2 acc)
  | Done => set_add (list_eq_dec label_nat_dec_eq) acc empty_set
end.

