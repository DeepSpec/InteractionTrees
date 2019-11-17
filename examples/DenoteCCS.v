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
         | a.P1       Input action 
         | ̄a.P1      Output action 
         | P1 + P2    Choice (Sum type) 
         | P1 ∥ P2    Parallel composition 
         | P1 ∖ a     Restriction *** (TODO)

      * Input action: process P1 *receives* an input through port a.
      * Output action: process P2 *sends* an output through port a. 
      * Choice : either P1 or P2 will be processed. 
      * Parallel composition: processes P1 and P2 exist simultaneously
      * Restriction: hides port a in process P1. 
  *)
  
Variable A : Type.

(* Denotation of CCS Operators *)
Variant ccsE : Type -> Type :=
| Or : ccsE bool
| In : A -> ccsE unit
| Out : A -> ccsE unit. 
                 
Definition ccs := itree ccsE unit.

(** Denotation of basic operations in CCS. 
    For now, we reason about finitary ITrees. *)

(* NB: The denotation of zero should be of type *unit* not void.
   For now, we're reason about finitary (but still possibly nonterminating!)
   ITrees. *)
Definition zero : ccs := Ret tt. 

(* Send (input) operator *)
Definition send (a : A) (k : ccs) : ccs := Vis (Out a) (fun _ => k).

(* Receive (output) operator *)
Definition recv (a : A) (k : ccs) : ccs := Vis (In a) (fun _ => k).

(* Choose operator *)
Definition pick (k : bool -> ccs) : ccs := Vis Or k.

(* Representation of finitary ccs. *)
Inductive finitary : ccs -> Type :=
| RecvFin (a : A) (k : ccs): finitary (recv a k)
| SendFin (a : A) (k : ccs): finitary (send a k)
| ChoiceFin (k : bool -> ccs) (finL: finitary (k true)) (finR: finitary (k false)): finitary (pick k)
| TauFin (k : ccs) (finK: finitary k) : finitary (Tau k)
. 

(* Helper function for choose -- 
   Crawling over possible ports in the ccs tree and flattening them as a list. *)
Program Fixpoint ports (p : ccs) (D : finitary p) : list ccs := _.  
Next Obligation.
  dependent induction D.
  - exact [recv a k].
  - exact [send a k].
  - exact (List.app IHD1 IHD2). 
  - exact IHD.
Defined.

(* Helper function for par -- 
   Gives a co-recursive choice function based on two ccs lists. *)
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
