Require Import Logic.Eqdep.
Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module ITREE.

CoInductive itree (E : Type -> Type) (R : Type) :=
| Ret (r : R)
| Vis {X : Type} (e : E X) (k : X -> itree E R)
| Tau (t : itree E R)
.
      
(* Questions:
   - Fork is _both_ threads running at the same time
   - can they communicate?
*)
(* | Fork (t1 : itree E R) (t2 : itree E R) *)

(* Choice:
   - semantically is one _or_ the other of the itrees
   - the difference between Fork & Choice is in how
     they relate to _other_ trees via simulation:
     Fork would require the other tree to have _both_ behaviors
     Choice would require the other tree to have _one_ behavior
*)
(* | Choice (t1 : itree E R) (t2 : itree E R) *)

(* 
  Not expressible in Coq:
  | BigChoice : (itree E R -> Prop) -> itree E R  

  See Adam's trick for how to make something like this work:
   - but, it isn't quantifying over possible trees.

*)



(* [id_itree] as a notation makes it easier to
   [rewrite <- match_itree]. *)
Notation id_itree t :=
  match t with
  | Ret r => Ret r
  | Vis e k => Vis e k
  | Tau t => Tau t
  end.

Lemma match_itree : forall E R (t : itree E R), t = id_itree t.
Proof. destruct t; auto. Qed.

Arguments match_itree {E R} t.


End ITREE.

Module Ex1.
  Import ITREE.
  
  Inductive IO : Type -> Type :=
  | Out : forall A, A -> IO unit
  | In  : forall A, IO A
  .

  Inductive C : Type -> Type :=
  | Choice : forall A, C (A -> Prop)
  .

  Definition T := itree IO unit.
  
  (* Property that all values sent have been received: "Send after Receive" *)
  CoInductive sar : T -> list nat -> Prop :=
  | sar_ret : forall l, sar (Ret tt) l
  | sar_out : forall l x k, List.In x l -> sar (k tt) l -> sar (Vis (Out x) k) l
  | sar_in  : forall l k (H:forall n, sar (k n) (n::l)), sar (Vis In k) l
  | sar_tau : forall l t, sar t l -> sar (Tau t) l
  .

  CoFixpoint echo : T :=
    Vis In (fun (n:nat) => Vis (Out n) (fun _ => echo)).

  Lemma sar_echo : forall l, sar echo l.
  Proof.
    cofix CH.
    rewrite (match_itree echo). simpl.
    intros l.
    constructor. intros.
    constructor. apply List.in_eq.
    apply CH.
  Qed.
                             
End Ex1.  

Module RITREE.
  (* This definition is based on Adam's suggestion about including a nondeterministic choice via Prop. *)
  (* What is the right definition of bind? *)
  (* What about refinement / composition? *)
  
CoInductive itree (E : Type -> Type) (R : Type) :=
| Ret (r : R)
| Vis {X : Type} (e : E X) (k : X -> itree E R)
| Tau (t : itree E R)
| Huh {X : Type} (P: X -> Prop) (k : X -> itree E R)
.

Section bind.
  Context {E : Type -> Type} {T U : Type}.
  Variable k : T -> itree E U.
  
  CoFixpoint bind' (c : itree E T) : itree E U :=
    match c with
    | Ret r => k r
    | Vis e k' => Vis e (fun x => bind' (k' x))
    | Tau t => Tau (bind' t)
    | Huh P k' =>  Huh P (fun x => bind' (k' x))
    end.
End bind.

  Definition bind {E T U}
             (c : itree E T) (k : T -> itree E U)
  : itree E U :=
    bind' k c.


End RITREE.  

(* The following is probably obsolete *)

CoInductive related E R : RITREE.itree E R -> ITREE.itree E R -> Prop :=
| rel_Ret : forall r, related (RITREE.Ret r) (ITREE.Ret r)
| rel_Vis : forall X (e: E X) k1 k2 (H:forall x, related (k1 x) (k2 x)), related (RITREE.Vis e k1) (ITREE.Vis e k2)
| rel_Tau : forall t1 t2, related t1 t2 -> related (RITREE.Tau t1) (ITREE.Tau t2)
| rel_Huh : forall X (P : X -> Prop) k1 x t, (P x) -> related (k1 x) t -> related (RITREE.Huh P k1) t
.                                                                       

(* We might say that an ITree _satisfies_ a (less determined) specification if for every Huh node
   in the spec, there _exists_ an x such that the determined tree 
 *)

CoInductive satisfies E R : ITREE.itree E R -> RITREE.itree E R -> Prop :=
| sat_Ret : forall r, satisfies (ITREE.Ret r) (RITREE.Ret r) 
| sat_Vis : forall X (e: E X) k1 k2 (H:forall x, satisfies (k1 x) (k2 x)), satisfies (ITREE.Vis e k1) (RITREE.Vis e k2)
| sat_Tau : forall t1 t2, satisfies t1 t2 -> satisfies (ITREE.Tau t1) (RITREE.Tau t2) 
| sat_Huh : forall X (P : X -> Prop) k1 x t, (P x) -> satisfies t (k1 x) -> satisfies t (RITREE.Huh P k1)
.                                                                       

Module MITREE.
CoInductive itree M (E : Type -> Type) (R : Type) :=
| Ret (r : R)
| Vis {X : Type} (e : E X) (k : X -> itree M E R)
| Tau (t : itree M E R)
| Huh {X : Type} (P: M X) (k : X -> itree M E R)
.

End MITREE.

(* Adding a "nondeterminism effect" by direct addition of the the proposition. *)
Definition ritree (E:Type -> Type) R := ITREE.itree (fun X => (E X) + (X -> Prop))%type R.


(* Disallowing visible effects by excluding constructors *)
Definition citree (E:Type -> Type) R := ITREE.itree (fun X => False) R.

  

(* Questions:

- What shape is your tree?
 * ITree 


- What representation?

* Coinductive Coq Itrees:
  Functorized itrees:

*)

Module FUNCTOR_ITREE.

(* X ~ F E A X *)
Inductive F (E : Type -> Type) (A:Type) (X:Type) : Type :=
| Ret : A -> F E A X
| Vis : forall {Y : Type}, E Y -> (Y -> X) -> F E A X
| Tau : X -> F E A X
| Huh : forall {Y : Type}, ((Y -> Prop) -> X) -> F E A X
.

CoInductive cofix_itree E A := { ctr : F E A (cofix_itree E A) }.

Inductive finite_itree E A :=
  | Ctr : (F E A (finite_itree E A)) -> finite_itree E A.

(*
 * transition systems
 *)

(* Defined using an existential. *)
(* What is the "shape" functor here? *)
Definition transition (E : Type -> Type) (A : Type) : Type := 
  {S:Type & S -> (F E A S) }.

(* Coinductively *)
CoInductive semantics (E : Type -> Type) :=
  { step : forall A, E A -> A * (semantics E) }.

End FUNCTOR_ITREE.

(* RTS: relational transition system *)
(* Jeremie's Propositional rehavior *)

(* The possible behaviors of each state in a RTS are as follows. *)
  Inductive behavior (E : Type -> Type) S :=
    | internal : S -> behavior E S
    | interacts : forall A, (E A) -> (A -> S) -> behavior E S
    | diverges
    | goes_wrong.

  Arguments behavior : clear implicits.

  (* Allows a "BigChoice" kind of semantics with 
     underspecification implemented by nondeterminism. *)
  Definition rts E S := S -> behavior E S -> Prop.

  
  (* Question: 
     What is the difference between the above and:
  *)
  Definition Prog E A := (ITREE.itree E A) -> Prop.

  (* The Prog version: harder for doing proofs because you have to resolve or
     deal with the nondeterminism "up front" as opposed to "step-wise"?  *)

  (* step : S -> S * F A *)
  (* step : S -> F (S * A) *)
  
  
  

  
(* Games? *)

(* Other axes:
- Computable vs. logical?
* extractability

 *)


(* Santiago's Example of nondterministic choice vs. all finite unrollings:

Consider this program, which uses oracular (angelic) nondeterminsm:

  n = choose int 
  while n > 0 
    n--
  explode

It is "safe" in the sense that,
  forall i, exists n, i-fold unrolling does not explode.

*)

  Inductive CH : Type -> Type :=
  | Choose : CH nat
  .

  Inductive result :=
  | Explode
  | Halt
  .

  Definition T := ITREE.itree CH result.
  
  Fixpoint loop (n:nat) : T :=
    match n with
    | O => ITREE.Ret Explode
    | S n => ITREE.Tau (loop n)
    end.

  Definition santiago : T :=
    ITREE.Vis Choose loop.


  Module Demonic.

  (* Uses universal quantification to get input from the environment. *)
    (* Note: forall vs. exists in the extermal interation *)
    CoInductive c_safe : T -> Prop :=
    | safe_ret : c_safe (ITREE.Ret Halt)
    | safe_tau : forall t, c_safe t -> c_safe (ITREE.Tau t)
    | safe_vis : forall {A} (e : CH A) (k : A -> T) (h:forall a, c_safe (k a)), c_safe (ITREE.Vis e k).
    
    Inductive safe : nat -> T -> Prop :=
    | safe_O: forall (t:T), t <> (ITREE.Ret Explode) -> safe 0 t
    | safe_S_tau : forall n t, safe n t -> safe (S n) (ITREE.Tau t)
    | safe_S_vis : forall {A} n (e : CH A) (k : A -> T), forall (h:forall a, safe n (k a)), safe (S n) (ITREE.Vis e k)
    .

  
    Lemma safe_c_safe : forall (t:T) (H: forall i, safe i t), c_safe t.
    Proof.
      cofix CH.
      destruct t.
      - intros H.  specialize H with (i:=O). inversion H. subst.
        destruct r. contradiction.
        constructor.
      - intros H. apply safe_vis. intros a.
        apply CH. intros i.
        specialize H with (i := S i).
        inversion H. subst.
        pose (projT2_eq H4). simpl in *. rewrite <- eq_rect_eq in e0.
        subst.
        apply h.
      - intros H. apply safe_tau.
        apply CH.
        intros i.
        specialize H with (i := S i).
        inversion H. assumption.
    Qed.
  End Demonic.
    
  Module Angelic.

    (* Uses _existential_ quantification to get the input from the environment *)
    CoInductive c_safe : T -> Prop :=
    | safe_ret : c_safe (ITREE.Ret Halt)
    | safe_tau : forall t, c_safe t -> c_safe (ITREE.Tau t)
    | safe_vis : forall {A} (e : CH A) (k : A -> T) (h:exists a, c_safe (k a)), c_safe (ITREE.Vis e k).
    
    Inductive safe : nat -> T -> Prop :=
    | safe_O: forall (t:T), t <> (ITREE.Ret Explode) -> safe 0 t
    | safe_S_tau : forall n t, safe n t -> safe (S n) (ITREE.Tau t)
    | safe_S_vis : forall {A} n (e : CH A) (k : A -> T), forall (h:exists a, safe n (k a)), safe (S n) (ITREE.Vis e k)
    .
    
    Lemma safe_loop : forall i, safe i (loop (S i)).
    Proof.
      induction i.
      - simpl. constructor. discriminate.
      - simpl. constructor. assumption.
    Qed.
    
    Lemma safe_c_safe : exists (t:T), (forall i, safe i t) /\  (c_safe t -> False).
    Proof.
      intros.
      exists santiago.
      unfold santiago.
      split.
      - destruct i.
        * constructor. discriminate.
        * econstructor. exists (S i). apply safe_loop.
      - intros.
        inversion H.
        * subst.  pose (projT2_eq H3). simpl in *. rewrite <- eq_rect_eq in e.
          destruct h. 
          subst. clear H H2 e0 H3.
          induction x.
          ** inversion H0.
          ** inversion H0. subst. apply IHx. assumption.
    Qed.           
      
  End Angelic.
