From ITree Require Import
     ITree
     ITreeDefinition. 

From Coq Require Import
     Program.Equality
     List.

(** *Concurrency 
    
    We want to reason about concurrency with ITrees. 
    
    A simple calculus to model is the Calculus of Communication Systems (CCS). 
    
*)





(** Denotation of CCS *)

Import ListNotations.

Set Implicit Arguments.

Section ccs.
  
Variable A : Type.

Variant ccsE : Type -> Type :=
| Or : ccsE bool
| In : A -> ccsE unit
| Out : A -> ccsE unit. 
                 
Definition ccs := itree ccsE unit. 

(* NB:  *)
Definition zero : ccs := Ret tt. 

Definition send (a : A) (k : ccs) : ccs := Vis (Out a) (fun _ => k).

Definition recv (a : A) (k : ccs) : ccs := Vis (In a) (fun _ => k).

Definition pick (k : bool -> ccs) : ccs := Vis Or k.

(* Representation of finitary ccs. *)
Inductive finitary : ccs -> Type :=
| RecvFin (a : A) (k : ccs): finitary (recv a k)
| SendFin (a : A) (k : ccs): finitary (send a k)
| ChoiceFin (k : bool -> ccs) (finL: finitary (k true)) (finR: finitary (k false)): finitary (pick k)
| TauFin (k : ccs) (finK: finitary k) : finitary (Tau k)
. 
         
Program Fixpoint ports (p : ccs) (D : finitary p) : list ccs := _.  
Next Obligation.
  dependent induction D.
  - exact [recv a k].
  - exact [recv a k].
  - exact (List.app IHD1 IHD2). 
  - exact IHD.

Definition par {A} (p1 p2 : ccs A) : ccs A := 
  
End ccs. 
