From ITree Require Import
     ITree
     ITreeDefinition. 

From Coq Require Import
     Program.Equality
     List.

(** * Modeling Concurrency with ITrees (CCS)

    We want to reason about concurrency with ITrees.

    For modeling concurrency, we use Milner's calculus of communicating systems(#) (CCS),
    a predecessor to π-calculus. In CCS, participating processes of a concurrent system
    have indivisible communications that can be composed in parallel.

    The primitive in the calculus is a _process_ that can have input and output _ports_
    in which processes can communicate. Each port is labeled and can take either input
    or output (but not both), and processes can only communicate through a port with
    the same label with opposing polarity (i.e. a process with input port `a` can
    communicate with a process with output port `a`).


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
         | P1 ∥ P2    Parallel composition
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
Variable X : A -> Prop.

Definition In (a : A) := X a.

(*Definition Out (a : A) := (not (X a))%type. *) 

(* Denotation of CCS Operators as ITree events *)
Variant ccsE : Type -> Type :=
| Or : ccsE bool
| Act : A -> ccsE unit.

Definition ccs := itree ccsE unit.

(** Denotation of basic operations in CCS.
    For now, we reason about finitary ITrees. *)

(* NB: The denotation of zero should be of type *unit* not void.
   For now, we're reason about finitary (but still possibly nonterminating!)
   ITrees. *)
(* The empty process. *)
Definition zero : ccs := Ret tt.

(* Send operator. *)
Definition send (a : A) (k : ccs) (H := In a) := Vis (Act a) (fun _ => k).

(* Receive operator. *)
Definition recv (a : A) (k : ccs) (H := not (In a)) : ccs := Vis (Act a) (fun _ => k).

(* Choose operator *)
Definition pick (k : bool -> ccs) : ccs := Vis Or k.

(* Representation of finitary ccs. *)
Inductive finitary : ccs -> Type :=
| SendFin (a: A) (k : ccs): finitary (send a k)
| RecvFin (a: A) (k : ccs): finitary (recv a k)
| ChoiceFin (k : bool -> ccs) (finL: finitary (k true)) (finR: finitary (k false)): finitary (pick k)
| TauFin (k : ccs) (finK: finitary k) : finitary (Tau k)
.

(* Helper function for choose --
   Crawling over possible ports in the ccs tree and flattening them as a list. *)
Program Fixpoint ports (p : ccs) (D : finitary p) : list ccs := _.
Next Obligation.
  dependent induction D.
  - exact [send a k].
  - exact [recv a k]. 
  - exact (List.app IHD1 IHD2).
  - exact IHD.
Defined.

(* IY: Is co-recursion necessary here? *)
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

(* Parallel composition operator *)
Definition par (p1 p2 : ccs) (pf1 : finitary p1) (pf2 : finitary p2) : ccs := pick (choose (ports pf1) (ports pf2)).

End ccs.
