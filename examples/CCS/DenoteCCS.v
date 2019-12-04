From ITree Require Import
     ITree
     ITreeDefinition.

From Coq Require Import
     Program.Equality
     List.

(** * Modeling Concurrency with ITrees (CCS)

    We want to reason about concurrency with ITrees.

    For modeling concurrency, we use Milner's calculus of communicating systems(#)
    (CCS), a predecessor to π-calculus. In CCS, participating processes of a
    concurrent system have indivisible communications that can be composed in
    parallel.

    The primitive in the calculus is a _process_ that can have input and output
    _actions_ in which processes can communicate. Each action has a corresponding
    label, and can act as either an input or output (but not both).
    Processes can only communicate through complementary actions with the same
    label (i.e. same labels with actions of opposing polarity, such that process
    with input action `a` can communicate with a process with output action `a`).


    (#) Milner, R., Communication and Concurrency, 1989.
*)

Import ListNotations.
Set Implicit Arguments.

Section ccs.

  (** CCS Operators:

      P := ∅          Empty Process
         | A = P1     Process Identifier *** (TODO)
         | a.P1       Action
         | P1 + P2    Choice (Sum type)
         | P1 ∥ P2    Parallel Composition *** (WIP)
         | P1 ∖ a     Restriction *** (TODO)

      * Empty Process
      * Process Identifier: Identifier A refers to process P1. Allows
                            recursive definitions.
      * Action: Process P1 performs an action a. This could be a send or
                receive, depending on the polarity of the action a.
      * Choice : either P1 or P2 will be processed.
      * Parallel Composition: Processes P1 and P2 exist simultaneously
      * Restriction: Hides port a in process P1.
  *)

(* We need a decidable equality on labels for the Restriction and Parallel
   Composition operator. Indexing labels by nat gives an easy decidable
   equality for now. *)
Variant Label : nat -> Type :=
| In (n : nat) : Label n
| Out (n : nat) : Label n.

(* Denotation of CCS Operators as ITree events. *)
Variant ccsE : Type -> Type :=
| Or (n : nat): ccsE nat (* Note: choices are zero-indexed. *)
| Act (n : nat) : Label n -> ccsE unit.

Definition ccs := itree ccsE unit.

(** Denotation of basic operations in CCS.
    For now, we reason about finitary ITrees. *)

(* The empty process. *)
Definition zero : ccs := Ret tt.

(* Action operators, where n denotes the label. *)
Definition send (n : nat) (k : ccs) : ccs := Vis (Act (In n)) (fun _ => k).

Definition recv (n : nat) (k : ccs) : ccs := Vis (Act (Out n)) (fun _ => k).

(* Choose operator, where n is the number of choices. *)
Definition pick (n: nat) (k : nat -> ccs) : ccs := Vis (Or n) k.

(* Parallel composition operator (#).

   (#) Follows denotation of CCS parallel composition operator from
       Section 5 Rule IV. (p. 269) of:
       M. Henessy & G. Plotkin, A Term Model for CCS, 1980. *)
CoFixpoint par (p1 p2 : ccs) : ccs :=
  match p1, p2 with
  | (Vis (Or n1) k1), (Vis (Or n2) k2) =>
      Vis (Or 3) (fun n0 : nat =>
        if beq_nat n0 0 then Vis (Or n1) (fun n11 : nat => par_left (k1 n11) p2)
        else if beq_nat n0 1 then Vis (Or n2) (fun n21 : nat => par_right p1 (k2 n21))
        else Vis (Or n1) (fun n12 : nat => Vis (Or n2)
                 (fun n22 => par_comm (k1 n12) (k2 n22))))
  | _, _ => zero
  end
with par_left (p1 p2 : ccs) : ccs :=
  match p1, p2 with
  | (Vis (Act x) k), _ => Vis (Act x) (fun _ => par (k tt) p2)
  | Tau t1, _ => Tau (par t1 p2)
  | _, _ => zero
  end
with par_right (p1 p2 : ccs) : ccs :=
  match p1, p2 with
  | _, (Vis (Act x) k) => Vis (Act x) (fun _ => par p1 (k tt))
  | _, Tau t1 => Tau (par p1 t1)
  | _, _ => zero
  end
with par_comm (p1 p2 : ccs) : ccs :=
  match p1, p2 with
  | (Vis (Act (In n1)) k1), (Vis (Act (Out n2)) k2) =>
    if beq_nat n1 n2 then Tau (par (k1 tt) (k2 tt)) else zero
  | (Vis (Act (Out n1)) k1), (Vis (Act (In n2)) k2) =>
    if beq_nat n1 n2 then Tau (par (k1 tt) (k2 tt)) else zero
  | _, _ => zero
  end.


(*-------------------- Notes -------------------------*)
(* Nov. 26, 2019. *)
(* Example finitary ccs trees. *)

Inductive finitary : ccs -> Type :=
| ZeroFin : finitary zero
| SendFin (n : nat) (k : ccs): finitary (send n k)
| RecvFin (n : nat) (k : ccs) : finitary (recv n k)
| ChoiceFin (k : bool -> ccs) (finL: finitary (k true))
            (finR: finitary (k false)):
    finitary (pick k)
| TauFin (k : ccs) (finK: finitary k) : finitary (Tau k)
.
Example ccs1 (n : nat) : ccs := pick (fun _ => send n zero).

Example finite1 (n : nat) : Type := finitary (ccs1 n).

Eval cbv in finite1 1.

Example ccs2 (n : nat) : ccs := pick (fun b => if b
                                     then send n zero
                                     else recv n zero).

Example finite2 (n : nat) : Type := finitary (ccs2 1).

(* ✠ Question: Do we need finitary? Aren't all of these trees built from our
   operators going to be finite? *)

(* Helper function for choose --
   Crawling over possible labels in the ccs tree and flattening them as a list. *)
Program Fixpoint label_list (p : ccs) (D : finitary p) : list ccs := _.
Next Obligation.
  dependent induction D.
  - exact [].
  - exact [send n k].
  - exact [recv n k].
  - exact (List.app IHD1 IHD2).
  - exact IHD.
Defined.

(* Here is a convoluted attempt at going forward and trying to define the
   parallel composition operator... It is bad.*)
(* Wrong. *)
CoFixpoint choose1 (p1 p2 : list ccs) : bool -> ccs :=
  match p1 with
  | [] => match p2 with
         | [] => fun b => zero
         | h :: t => fun b => pick (choose [] t)
         end
  | h1 :: t1 => match p2 with
        | [] => fun b => zero
        | h2 :: t2 =>
          fun b =>
          match b with
          | true => pick (choose t1 p2)
          | false => pick (choose p1 t2)
          end
        end
  end.

(* Parallel composition operator. Wrong. *)
Definition par1 (p1 p2 : ccs) (pf1 : finitary p1) (pf2 : finitary p2) : ccs :=
  pick (choose (label_list pf1) (label_list pf2)).

(* These don't work because it doesn't reason about any of the labels in a
   meaningful way. It nests the choose operators, but in a totally non-
   sensical manner. We stare at the label lists again, to see how this is useful
   and what we could do. *)

(* Example label lists. *)

(* A ccs tree of depth 1. *)
Example label_list12 :=
  fun (n : nat) => label_list
                   (ChoiceFin (fun b => if b then send n zero
                                        else recv n zero)
                              (SendFin n zero)
                              (RecvFin n zero)).

Eval cbv in label_list12 1.
(* cbv is not the right reduction strategy, because we don't want it to unfold
   all the way. We need information about the polarity of labels. *)

(* A ccs tree of depth 2. *)
Example label_list2 :=
  fun (n1 n2 : nat) => label_list
                (ChoiceFin (fun b => if b then @send n1 zero
                                       else pick (fun _ => @send n2 zero))
                           (SendFin n1 zero)
                           (ChoiceFin (fun _ => @send n2 zero)
                                       (SendFin n2 zero)
                                       (SendFin n2 zero))).

Eval cbv in label_list2.


(* Woo! Our crawling operator is working as expected. Now, we think about
   how we can actually construct the parallel composition combinator.

   Let's start looking at an example to gain some intuition.
   What should the denotation of `(a.P + b.Q) ∥ (ā.∅ ∥ b̄.∅)` be? *)

(* Label lists of the components we're combining with the parallel combinator. *)
Example ex_label_list1 :=
  fun (n1 n2 : nat) (P Q : ccs) => label_list
                                (ChoiceFin (fun b => if b then @recv n1 P
                                                  else @recv n2 Q)
                                           (RecvFin n1 P)
                                           (RecvFin n2 Q)).

Eval cbv in ex_label_list1 1 2.

Example ex_label_list2 :=
  fun (n1 : nat) => label_list
                 (SendFin n1 zero).

Eval cbv in ex_label_list2 1.

Example ex_label_list3 :=
  fun (n2 : nat) => label_list
                 (SendFin n2 zero).

Eval cbv in ex_label_list3 2.

(* The possible transitions from `(a.P + b.Q) ∥ (ā.∅ ∥ b̄.∅)` are:
    1)  -(τ)⟶ P ∥ (∅ ∥ b̄.∅) -(b̄)⟶ P ∥ (∅ ∥ ∅)
    2)  -(τ)⟶ Q ∥ (ā.∅ ∥ ∅) -(ā)⟶ Q ∥ (∅ ∥ ∅) *)

(* ✠ Question: Does `∅ ∥ ∅` transition to anything?
   There are no applicable transition strategy in
   LTS (Labeled Transition System) for this agent expression. *)

(* Sub-example : (ā.∅ ∥ b̄.∅)
    1)  -(ā)⟶ (∅ ∥ b̄.∅) -(b̄)⟶ (∅ ∥ ∅)
    2)  -(b̄)⟶ (ā.∅ ∥ ∅) -(ā)⟶ (∅ ∥ ∅)
   This is an example where there are no complementary actions for a parallel
   composition.

   We can try defining a parallel composition operator with a straight-forward
   type declaration:
   > Definition par (p1 p2 : ccs) (pf1 : finitary p1) (pf2 : finitary p2): ccs.
   p1 := ā.∅
   p2 := b̄.∅
   par p1 p2 ≈ (āb̄, ∅ ∥ ∅) + (b̄ā, ∅ ∥ ∅)
             ≈ pick (fun b => if b then @send a (@send b ∅)
                                   else @send b (@send a ∅))
*)

End ccs.
