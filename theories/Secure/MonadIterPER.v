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
     Events.MapDefault
     Events.State
     Events.StateFacts
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section MonadIterPER.

Context {M : Type -> Type}.

Context {MonadM : Monad M}.
Context {MonadIterM : MonadIter M}.

Class HeteroPER (lift : forall (A B : Type), (A -> B -> Prop) -> M A -> M B -> Prop)  :=
  {
  heteroPER_sym : forall (A B : Type) (R : A -> B -> Prop) a b, lift _ _ R a b -> lift _ _ (flip R) b a;
  heteroPER_trans : forall (A B C : Type) (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) a b c,
      lift _ _ R1 a b -> lift _ _ R2 b c -> lift _ _ (rcompose R1 R2) a c;
  heteroPER_mon : forall (A B : Type) (R R' : A -> B -> Prop),
      R <2= R' -> lift _ _ R <2= lift _ _ R'
  
  }.
(* zig zag R a b -> R c d -> R c b -> ...  *)

Class MonadIterPER (lift : forall {A B : Type}, (A -> B -> Prop) -> M A -> M B -> Prop) :=
  {
   HPER : HeteroPER (@lift);
   respects_ret : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (r1 : R1) (r2 : R2),
       RR r1 r2 -> lift RR (ret r1) (ret r2);
   respects_bind : forall (R1 R2 S1 S2 : Type) (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) 
                     (m1 : M R1) (m2 : M R2) (k1 : R1 -> M S1) (k2 : R2 -> M S2),
       (lift RR m1 m2) -> (forall r1 r2, RR r1 r2 -> lift RS (k1 r1) (k2 r2)) ->
       lift RS (bind m1 k1) (bind m2 k2);

   respects_iter : forall (A1 A2 B1 B2 : Type) (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
                     (body1 : A1 -> M (A1 + B1) ) (body2 : A2 -> M (A2 + B2) )
                     (a1 : A1) (a2 : A2),
       RA a1 a2 -> 
       (forall a1 a2, RA a1 a2 -> lift (HeterogeneousRelations.sum_rel RA RB) (body1 a1) (body2 a2)) ->
       lift RB (iter body1 a1) (iter body2 a2);

   
  }.

  (* can lift to states by picking a relation RSt over states that preserves this structure,
     take fun RR => pointwise RSt (RSt * RR)
     in the eqit_secure case, it is low equivalence *)
End MonadIterPER.

Section MonadIterPERStateT.

  Context {M : Type -> Type}.
  Context (St : Type).
  Context (lift : forall {A B : Type}, (A -> B -> Prop) -> M A -> M B -> Prop).
  Context {MonadM : Monad M}.
  Context {MonadIterM : MonadIter M}.

  Context {MonadIterPERM : MonadIterPER lift}.

  Context (RS : St -> St -> Prop).

  Context (Hsym : Symmetric RS).
  Context (Htrans : Transitive RS).

  (* Context (HRS : ) *)

  Definition lift_state (A B : Type) (RR : A -> B -> Prop) (RS : St -> St -> Prop)  (m1 : stateT St M A) (m2 : stateT St M B) : Prop :=
    forall s1 s2, RS s1 s2 -> 
             lift _ _ (fun r1 r2 => RS (fst r1) (fst r2) /\ RR (snd r1) (snd r2)) (m1 s1) (m2 s2).

  Hint Unfold lift_state.

  Program Global Instance MonadIterPERStateT : MonadIterPER  (fun (A B : Type) (RR : A -> B -> Prop) m1 m2 => lift_state A B RR RS m1 m2).
  Next Obligation.
    constructor; unfold lift_state; intros.
    - unfold flip.
      set (R' := flip (fun  (r1 : St * A) (r2 : St * B) => (RS (fst r1) (fst r2) /\ R (snd r1) (snd r2) )) ).
      eapply heteroPER_mon with (R0 := R' ); unfold flip.
      +  intros ? ? [? ?]. split; auto.
      + eapply heteroPER_sym. eauto.
    - set (RM1 := fun (r1 : St * A) (r2 : St * B) => RS (fst r1) (fst r2) /\ R1 (snd r1) (snd r2) ). 
      set (RM2 := fun r1 r2 => RS (fst r1) (fst r2) /\ R2 (snd r1) (snd r2) ).
      eapply heteroPER_mon with (R := rcompose RM1 RM2).
      + intros [? ?] [? ?] ?. inv PR. unfold RM1 in *. unfold RM2 in *.
        destruct REL1. destruct REL2. cbn in *. split; auto. eapply Htrans; eauto. econstructor; eauto.
      + eapply heteroPER_trans; eauto.
    - eapply heteroPER_mon with (R0 := fun r1 r2 => (RS (fst r1) (fst r2) /\ R (snd r1) (snd r2) ) ); eauto.
      intros [? ?] [? ?] [? ?]. cbn in *. split; auto.
      Unshelve. all : eapply HPER. (* not sure why it could not infer this *)
  Qed.
  Next Obligation.
    red. intros. apply respects_ret. cbn. auto.
  Qed.
  Next Obligation.
   red. intros. eapply respects_bind; eauto. intros. cbn in H2. destruct H2 as [HRS HRR].
   apply H0 in HRR as HRS'. eauto.
     
  Qed.
  Next Obligation.
    red. intros. eapply respects_iter with (RA0 := fun '(s1, a1) '(s2, a2) => RA a1 a2 /\ RS s1 s2 ); eauto.
    intros [? ?] [? ?] [? ?]. cbn. apply H0 in H2 as Ha. red in Ha. apply Ha in H3 as Has. 
    clear Ha. eapply respects_bind; eauto.
    intros. cbn in H4. destruct r1. destruct r2. cbn. destruct s4; destruct s6; cbn in *;
    try (apply respects_ret; destruct H4; inv H5; constructor; auto).
 Qed.
    
End MonadIterPERStateT.
 
(* 
Variant stateE : Type -> Type :=
  | Get x : stateE S
  | Put x v : stateE unit


Definition handlestate A (e : stateE A) :=
    match e with
    | Get x => fun s => Ret (find x s, s)
    | Put x v => fun s => Ret (unit, update s x v)


Definition handlestate A (e : stateE A) :=
    match e with
    | Get x => fun s => trigger (Print (find x s) ) ;; Ret (find x s, s)
    | Put x v => fun s => Ret (unit, update s x v)


(stateE + IOE)



trigger : E A -> itree E A

: E E' -> E<= E' -> itree E' A


privacy := Public | Private

Inductive syntax := 
      
      | while b do c
      | print : privacy -> value
      | private_print
E

is_get x e : Prop

is_put xs

denote_while b c := 
    x <- denote b ;; iter (fun b => if b then denote c else ret (inr tt) ) x

denote : syntax -> itree (stateE + IOE)

let M := (itree (stateE + IOE) )

priv separates private cells from public cells and separates public prints from private prints

let lift := eqit_secure (stateE + IOE) Label priv l



let M' := stateT (var -> value) (itree IOE)


let lift := what we get from the typeclass


WTS

secure t -> secure (interp handlestate t)
*)
