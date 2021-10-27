(* begin hide *)
From Paco Require Import paco.
From Coq Require Import Morphisms.
From ITree Require Import
     ITree
     Eq.Eq
     Basics.HeterogeneousRelations
     Interp.TranslateFacts.
Set Implicit Arguments.
Set Strict Implicit.
(* end hide *)

(** * Unary interpretation for [eutt]: a traditional program logic
 
  The weak bisimulation supported by [itree]s and the notions of 
  refinements we build upon it in the various monads we interpret into
  give us reasoning principles to establish the equivalence or refinement
  of computations.
  In particular, it can be seen as a relational program logic.

  We develop here some elementary theory for a unary program logic
  over itree-based computations.
  It is defined in terms of [eutt], simply taking its diagonal. 
  We prove that it respects the expected elemntary proof rules 
	w.r.t. to logical connectors.

	Most importantly, we derive a proof rule to leverage such unary 
	facts during a relational refinement proof: see [eutt_post_bind] 
	and [eutt_post_bind_gen].
	One can this way leverage functional properties of computations 
	during relational proofs without re-inlining the proof of 
	functional correctness everytime.

*)

(** The main predicate: an itree-computation [t] admits [Q] for
	  a postcondition.
    Defined as the diagonal of [eutt].
*)
Definition has_post {E X} (t : itree E X) (Q : X -> Prop) : Prop :=
  eutt (fun 'x _ => Q x) t t.

(** Note: the following formulation is equivalent. *)
Definition has_post_strong {E X} (t : itree E X) (Q : X -> Prop) : Prop :=
  eutt (fun 'x y => x = y /\ Q x) t t.

Lemma has_post_post_strong : forall {E X} (t : itree E X) Q,
    has_post t Q <-> has_post_strong t Q.
Proof.
  intros; split; intros HP.
  - apply eutt_conj; [reflexivity | auto].
  - eapply eqit_mon; eauto.
    intros * H; apply H.
Qed.

Module HasPostNotations.
	Notation "t ⤳ Q" := (has_post t Q) (at level 50).
End HasPostNotations.
Import HasPostNotations.

(** Proper instances *)
#[global] Instance has_post_eq_itree {E X} : 
	Proper (eq_itree eq ==> equiv_pred ==> iff) (@has_post E X).
Proof.
  repeat red; unfold has_post; intros * EUTT * EQ *; split; intros HP.
  - rewrite <- EUTT; eapply eutt_equiv; eauto.
    split; red; intros; apply EQ; auto.
  - rewrite EUTT; eapply eutt_equiv; eauto.
    split; red; intros; apply EQ; auto.
Qed.

#[global] Instance has_post_eutt {E X} : 
	Proper (eutt eq ==> equiv_pred ==> iff) (@has_post E X).
Proof.
  repeat red; unfold has_post; intros * EUTT * EQ *; split; intros HP.
  - rewrite <- EUTT; eapply eutt_equiv; eauto.
    split; red; intros; apply EQ; auto.
  - rewrite EUTT; eapply eutt_equiv; eauto.
    split; red; intros; apply EQ; auto.
Qed.

(** [has_post] logical primitives.
    Post-conditions can be established by means of usual proof 
		rules for elementary logical connectives
 *)

(* Conjunction introduction *)
Lemma has_post_conj : forall {E X} (t : itree E X) P Q,
    t ⤳ P ->
    t ⤳ Q ->
    t ⤳ (P /1\ Q).
Proof.
  intros * HP HQ.
  pose proof eutt_conj _ _ HP HQ.
  auto.
Qed.     

(* Left disjunction introduction *)
Lemma has_post_disj_l : forall {E X} (t : itree E X) P Q,
    t ⤳ P ->
    t ⤳ (P \1/ Q).
Proof.
  intros * HP.
  epose proof eutt_disj_l _ _ HP as H.
  apply H.
Qed.     

(* Right disjunction introduction *)
Lemma has_post_disj_r : forall {E X} (t : itree E X) P Q,
    t ⤳ Q ->
    t ⤳ (P \1/ Q).
Proof.
  intros * HQ.
  epose proof eutt_disj_r _ _ HQ as H.
  apply H.
Qed.     

(* Weakening *)
Lemma has_post_weaken : forall {E X} (t : itree E X) P Q,
    t ⤳ P ->
    P <1= Q ->
    t ⤳ Q.
Proof.
  intros * HP INCL.
  eapply eqit_mon; eauto.
  intros; apply INCL; auto.
Qed.     

(* Trivial postcondition *)
Lemma has_post_True : forall {E X} (t : itree E X),
    t ⤳ fun _ => True.
Proof.
  intros *.
  eapply eqit_mon; eauto.
  reflexivity.
Qed.     

(** Structural proof rules *)

(* The prefix can be ignored if the continuation universally satisfy the
 	 postcondition *)
Lemma has_post_bind_weak : forall {E X Y} (t : itree E X) (k : X -> itree E Y) Q,
    (forall x, k x ⤳ Q) ->
    ITree.bind t k ⤳ Q.
Proof.
  intros * POST.
  apply eutt_eq_bind; intros ?; apply POST.
Qed.

(* But the more interesting cut rule is of course valid *)
Lemma has_post_bind : forall {E X Y} (t : itree E X) (k : X -> itree E Y) S Q,
    t ⤳ S ->
    (forall x, S x -> k x ⤳ Q) ->
    ITree.bind t k ⤳ Q.
Proof.
  intros * POST1 POST2.
  apply eutt_clo_bind with (UU := fun x y => x = y /\ S x) ; [apply has_post_post_strong; exact POST1 |].
  intros ? ? [<- ?]; eapply POST2; eauto.
Qed.

(* Invariant-based loop rule *)
Lemma has_post_iter_strong :
  forall {E R I} (body : I -> itree E (I + R)) (entry : I) (Inv : I -> Prop) (Q : R -> Prop),
    (forall i, Inv i -> body i ⤳ sum_pred Inv Q) ->
    Inv entry ->
    ITree.iter body entry ⤳ Q.
Proof.
  intros * IND INIT.
  eapply (@KTreeFacts.eutt_iter_gen _ _ _ (fun x y => x = y /\ Inv x)); eauto.
  intros i ? [<- ?].
  specialize (IND i); apply has_post_post_strong in IND; auto.
  unfold has_post_strong in IND.
  eapply eqit_mon; try apply IND; auto.
  intros [] ? [<- ?]; eauto. 
Qed.

(* [translate] preserves postconditions *)
Lemma has_post_translate : forall {E F X} (t : itree E X) Q (h : E ~> F),
    t ⤳ Q ->
    translate h t ⤳ Q.
Proof.
  unfold has_post; intros * POST.
  apply eutt_translate_gen; auto.
Qed.

(** Enriched relational cut rule
    The main benefit of the approach: post-conditions can be leveraged 
		when performing a cut during relational proofs.
		This lemma generalizes [eutt_clo_bind]
 *)
Lemma eutt_post_bind :
  forall E R1 R2 RR S1 S2 SS Q1 Q2
    (t1 : itree E S1) (k1: S1 -> itree E R1) (t2 : itree E S2) (k2 : S2 -> itree E R2),
    t1 ⤳ Q1 ->
    t2 ⤳ Q2 ->
    eutt SS t1 t2 ->
    (forall u1 u2, SS u1 u2 -> Q1 u1 -> Q2 u2 -> eutt RR (k1 u1) (k2 u2)) ->
    eutt RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros * POST1 POST2 EQ KEQ.
  apply eutt_clo_bind with (UU := fun x y => SS x y /\ Q1 x /\ Q2 y).
  2: intros ? ? (? & ? & ?); apply KEQ; auto.
  clear KEQ.
  apply has_post_post_strong in POST1.
  apply has_post_post_strong in POST2.
  pose proof eqit_trans _ _ _ _ _ _ _ POST1 EQ as EQ1.
  pose proof eqit_trans _ _ _ _ _ _ _ EQ1 POST2 as EQ2.
  clear -EQ2.
  eapply eutt_equiv; eauto.
  split.
  - intros ? ? (? & ? & ?); do 2 econstructor; eauto. 
  - intros ? ? ?. inv H. inv REL1.
    destruct REL2 as [-> ?], REL0 as [<- ?]; eauto.
Qed.

(* Often useful particular case of identical prefixes *)
Lemma eutt_post_bind_eq : forall E R1 R2 RR U Q (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    t ⤳ Q ->
    (forall u, Q u -> eutt RR (k1 u) (k2 u)) -> 
    eutt RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros * POST ?.
  apply eutt_clo_bind with (UU := fun x y => x = y /\ Q x); [apply has_post_post_strong; exact POST |].
  intros ? ? [-> ?]; auto.
Qed.

(* A little oddity that can be useful when building bisimulations manually:
   an [eutt] hypothesis between a tree and itself can be refined into an
	 [eq_itree] one.

   This assumes UIP.
 *)
Lemma eutt_eq_itree {E X} (R : X -> X -> Prop) : forall (t : itree E X),
  eutt R t t -> eq_itree R t t.
Proof.
  enough (forall (t u : itree E X), eutt R t u -> eq_itree eq t u -> eq_itree R t u).
  { intros; apply H; [ auto | apply Reflexive_eqit_eq ]. }
  pcofix CIH.
  intros t u H EQ. pfold. red.
  rewrite (itree_eta t), (itree_eta u) in H.
  punfold EQ. destruct EQ; try discriminate; constructor.
  - rewrite <- eutt_Ret in H. auto.
  - pclearbot. right; apply CIH; [ | apply REL ].
    revert H; apply eqit_Tau.
  - pclearbot. right; apply CIH; [ | apply REL ].
    eapply eqit_inv_Vis with (1 := H).
Qed.

Lemma has_post_strong_to_eq_itree : forall {E X} (t : itree E X) (Q : X -> Prop),
    has_post_strong t Q ->
    eq_itree (fun x y => x = y /\ Q x) t t.
Proof.
  intros *; apply eutt_eq_itree.
Qed.

Lemma has_post_to_eq_itree : forall {E X} (t : itree E X) (Q : X -> Prop),
    has_post t Q ->
    eq_itree (fun x y => x = y /\ Q x) t t.
Proof.
  intros * H; apply has_post_strong_to_eq_itree, has_post_post_strong, H.
Qed.
