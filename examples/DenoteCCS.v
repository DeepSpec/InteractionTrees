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
    _ports_ in which processes can communicate. Each port is labeled and can
    take either input or output (but not both), and processes can only communicate
    through a port with the same label with opposing polarity (i.e. a process with
    input port `a` can communicate with a process with output port `a`).


    (#) Milner, R., Communication and Concurrency, 1989.
*)

Import ListNotations.
Set Implicit Arguments.

Section ccs.

  (** CCS Operators:

      P := ∅          Empty process
         | A = P1     Process identifier *** (TODO)
         | a.P1       Action
         | P1 + P2    Choice (Sum type)
         | P1 ∥ P2    Parallel composition *** (WIP)
         | P1 ∖ a     Restriction *** (TODO)

      * Empty process
      * Process identifier: Identifier A refers to process P1. Allows
                            recursive definitions.
      * Action: Process P1 performs an action a. This could be a send or
                receive, depending on the polarity of the action a.
      * Choice : either P1 or P2 will be processed.
      * Parallel composition: Processes P1 and P2 exist simultaneously
      * Restriction: Hides port a in process P1.
  *)

(* Labels. *)
Variable A : Type.

(* Labels with polarity. *)
Variant Label : Prop :=
| In (a : A)
| Out (a : A).

(* Denotation of CCS Operators as ITree events *)
Variant ccsE : Type -> Type :=
| Or : ccsE bool
| Act : A -> ccsE unit.

Definition ccs := itree ccsE unit.

(** Denotation of basic operations in CCS.
    For now, we reason about finitary ITrees. *)

(* NB: The denotation of zero should be of type *unit* not void.
   For now, we'll reason about finitary (but still possibly nonterminating!)
   ITrees. *)
(* The empty process. *)
Definition zero : ccs := Ret tt.

(* Action operator. *)
Definition act {a : A} (H: Label) (k : ccs) : ccs := Vis (Act a) (fun _ => k).

Definition send {a : A} (k : ccs) : ccs := @act a (In a) k.

Definition recv {a : A} (k : ccs) : ccs := @act a (Out a) k.

(* Choose operator *)
Definition pick (k : bool -> ccs) : ccs := Vis Or k.

(* Representation of finitary ccs. *)
Inductive finitary : ccs -> Type :=
| ZeroFin : finitary zero
| SendFin (a : A) (k : ccs): finitary (@send a k)
| RecvFin (a : A) (k : ccs) : finitary (@recv a k)
| ChoiceFin (k : bool -> ccs) (finL: finitary (k true))
            (finR: finitary (k false)):
    finitary (pick k)
| TauFin (k : ccs) (finK: finitary k) : finitary (Tau k)
.

(* Example finitary ccs trees. *)

Example ccs1 (a : A) : ccs := pick (fun _ => @send a zero).

Example finite1 (a : A) : Type := finitary (ccs1 a).

Eval cbv in finite1.

Example ccs2 (a : A) : ccs := pick (fun b => if b
                                     then @send a zero
                                     else @recv a zero).

Example finite2 (a : A) : Type := finitary (ccs2 a).

(* ✠ Question: Do we need finitary? Aren't all of these trees built from our
   operators going to be finite? *)

(* Helper function for choose --
   Crawling over possible labels in the ccs tree and flattening them as a list. *)
Program Fixpoint label_list (p : ccs) (D : finitary p) : list ccs := _.
Next Obligation.
  dependent induction D.
  - exact [].
  - exact [@send a k].
  - exact [@recv a k].
  - exact (List.app IHD1 IHD2).
  - exact IHD.
Defined.

(* Here is a convoluted attempt at going forward and trying to define the
   parallel composition operator... It is bad.*)
(* Wrong. *)
CoFixpoint choose (p1 p2 : list ccs) : bool -> ccs :=
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
Definition par (p1 p2 : ccs) (pf1 : finitary p1) (pf2 : finitary p2) : ccs :=
  pick (choose (label_list pf1) (label_list pf2)).

(* These don't work because it doesn't reason about any of the labels in a
   meaningful way. It nests the choose operators, but in a totally non-
   sensical manner. We stare at the label lists again, to see how this is useful
   and what we could do. *)

(* Example label lists. *)

(* A ccs tree of depth 1. *)
Example label_list1 :=
  fun (a : A) => label_list
                   (ChoiceFin (fun b => if b then @send a zero
                                        else @recv a zero)
                              (SendFin a zero)
                              (RecvFin a zero)).

Eval cbv in label_list1.
(* cbv is not the right reduction strategy, because we don't want it to unfold
   all the way. We need information about the polarity of labels. *)

(* A ccs tree of depth 2. *)
Example label_list2 :=
  fun (a : A) => label_list
                (ChoiceFin (fun b => if b then @send a zero
                                       else pick (fun _ => @send a zero))
                           (SendFin a zero)
                           (ChoiceFin (fun _ => @send a zero)
                                       (SendFin a zero)
                                       (SendFin a zero))).

Eval cbv in label_list2.

(* Woo! Our crawling operator is working as expected. Now, we think about
   how we can actually construct the parallel composition combinator.

   Let's start looking at an example to gain some intuition.
   What should the denotation of `(a.P + b.Q) ∥ (ā.∅ ∥ b̄.∅)` be? *)

(* Label lists of the components we're combining with the parallel combinator. *)
Example ex_label_list1 :=
  fun (a1 a2 : A) (P Q : ccs) => label_list
                                (ChoiceFin (fun b => if b then @recv a1 P
                                                  else @recv a2 Q)
                                           (RecvFin a1 P)
                                           (RecvFin a2 Q)).

Eval cbv in ex_label_list1.

Example ex_label_list2 :=
  fun (a1 : A) => label_list
                 (SendFin a1 zero).

Eval cbv in ex_label_list2.

Example ex_label_list3 :=
  fun (a2 : A) => label_list
                 (SendFin a2 zero).

Eval cbv in ex_label_list3.

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
             ≈ pick (fun b => if b then @send a (@send b (par ∅ ∅))
                                   else @send b (@send a (par ∅ ∅)))
             ≈ (* Stuck. Do we need a parallel event of empty processes? *)
*)

(* The above Sub-example motivates the need for a parallel event of empty
   processes. We modify our original definition of CCS events. *)
Variant ccsE' : Type -> Type :=
| Or' : ccsE' bool
| Act' : A -> ccsE' unit
| Par' : ccsE' bool.


End ccs.
