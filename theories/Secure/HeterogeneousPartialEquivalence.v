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
 Import Basics.


From ITree Require Import
     ITree.
Import Eq.
Section HPE.
  Context (M : Type -> Type).
  Context (P : forall (R S: Type), (R -> S -> Prop) -> M R -> M S -> Prop ).
  Arguments P {R S}.
   
  Variant hpe_lift {R S : Type} (RR : R -> S -> Prop) (x : M R) (y : M S) : Prop :=
  | hpe_well_behaved : P RR x y -> hpe_lift RR x y
  | hpe_ill_behaved : 
      (* think carefully about these conditions, maybe they are not the ones I really want *)
      (forall RR1 : R -> R -> Prop, (forall x x' y, RR1 x x' -> RR x y -> RR x' y) -> ~ P RR1 x x ) ->
      (forall RR2 : S -> S -> Prop, (forall x y y', RR2 y y' -> RR x y -> RR x y') -> ~ P RR2 y y ) ->
      hpe_lift RR x y
  .

  Context (P_sym : forall (R S : Type) (RR : R -> S -> Prop ) r s, P RR r s -> P (flip RR) s r ).

  Context (P_trans : forall (R S T : Type) (RR1 : R -> S -> Prop) (RR2 : S -> T -> Prop) r s t,
              P RR1 r s -> P RR2 s t -> P (rcompose RR1 RR2) r t
          ).

  Context (P_mon : forall (R S : Type) (RR1 RR2 : R -> S -> Prop),
      (forall r s, RR1 r s -> RR2 r s) -> forall mr ms, P RR1 mr ms -> P RR2 mr ms).

  Lemma Proper_hpe_lift (R S : Type) RR RR1 RR2 : 
    (forall (x x' : R) (y : S), (RR1 x x' : Prop) -> (RR x' y : Prop) -> RR x y) ->
    (forall (x : R) (y y' : S), (RR2 y y' : Prop) -> RR x y' -> RR x y) ->
    Proper (P RR1 ==> P RR2 ==> flip impl) (P RR) ->
    Proper (hpe_lift RR1 ==> hpe_lift RR2 ==> flip impl) (P RR).
  Proof.
    intros HRR1 HRR2 Hprop. intros x x0 Hx y y0 Hy HRR.
    cbv in Hprop. destruct Hx as [Hx | Hx Hx0 ]; destruct Hy as [Hy | Hy Hy0 ].
    - eapply Hprop; eauto.
    - (* my intuition is that Hy and Hy0 contradict with HRR, y and y0 are both "bad" wrt their relations,
         which should mean that they are "bad" wrt P RR but HRR says that PRR relations y0 to something
       *)
      exfalso. apply P_sym in HRR as HRR'.
      assert (P (rcompose (flip RR) RR) y0 y0 ).
      { apply P_trans with (s := x0); auto. }
      eapply Hy0; eauto.
      intros. destruct H0. red in REL1.
      (* what if we assume RR1 and RR2 are PERs *)
      (* I think in order to usefully reason about hetero PERs we need some more assumptions  *)

      eapply Hy0 with (RR3 := rcompose RR2 (flip RR2)). 
      + intros. destruct H. unfold flip in REL1. admit.
      +

(* should be rcompose RR (flip RR) *)
      intros; subst; auto. admit.
      (* need to add condition that P is monotonic in RR and  *)
    - exfalso. eapply Hx with (RR2 := eq); intros; subst; auto.
      admit.
    - exfalso. eapply Hx with (RR2 := eq);
      intros; subst; auto. admit.
  Admitted.
  (* I think assuming P is proper with itself*)


End HPE.
