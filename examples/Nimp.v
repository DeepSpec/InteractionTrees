(* A nondeterministic Imp *)

From Coq Require Import
     Relations.

From ITree Require Import
     ITree
     ITreeFacts.

Import ITreeNotations.

Inductive com : Type :=
| loop : com -> com (* Nondeterministically, continue or stop. *)
| choose : com -> com -> com
| skip : com
| seq : com -> com -> com
.

Declare Scope com_scope.
Infix ";;" := seq (at level 61, right associativity) : com_scope.
Delimit Scope com_scope with com.
Open Scope com_scope.

Example one_loop : com := loop skip.
Example two_loops : com := loop (loop skip).
Example loop_choose : com := loop (choose skip skip).
Example choose_loop : com := choose (loop skip) skip.

(* Unlabeled small-step *)
Module Unlabeled.

Reserved Infix "-->" (at level 80, no associativity).

Inductive step : relation com :=
| step_loop_stop c :
    loop c --> skip
| step_loop_go c :
    loop c --> (c ;; loop c)
| step_choose_l c1 c2 :
    choose c1 c2 --> c1
| step_choose_r c1 c2 :
    choose c1 c2 --> c2
| step_seq_go c1 c1' c2 :
    c1 --> c2 ->
    (c1 ;; c2) --> (c1' ;; c2)
| step_seq_next c2 :
    (skip ;; c2) --> c2

where "x --> y" := (step x y).

CoInductive infinite_steps (c : com) : Type :=
| more c' : step c c' -> infinite_steps c' -> infinite_steps c.

Lemma infinite_simple_loop : infinite_steps one_loop.
Proof.
  cofix self.
  eapply more.
  { eapply step_loop_go. }
  eapply more.
  { eapply step_seq_next. }
  apply self.
Qed.

End Unlabeled.

Module Labeled.

Reserved Notation "s --> t" (at level 80, no associativity).
Reserved Notation "s ! b --> t" (at level 80, b at next level, no associativity).
Reserved Notation "s ? b --> t" (at level 80, b at next level, no associativity).

Variant label := tau | bit (b : bool).

Inductive step : label -> relation com :=
| step_loop_stop c :
    loop c ! true --> skip
| step_loop_go c :
    loop c ! false --> (c ;; loop c)
| step_choose_l c1 c2 :
    choose c1 c2 ! true --> c1
| step_choose_r c1 c2 :
    choose c1 c2 ! false --> c2
| step_seq_go b c1 c1' c2 :
    c1 ? b --> c2 ->
    (c1 ;; c2) ? b --> (c1' ;; c2)
| step_seq_next c2 :
    (skip ;; c2) --> c2

where "x --> y" := (step tau x y)
and  "x ! b --> y" := (step (bit b) x y)
and  "x ? b --> y" := (step b x y).

CoInductive infinite_steps (c : com) : Type :=
| more b c' : step b c c' -> infinite_steps c' -> infinite_steps c.

Lemma infinite_simple_loop : infinite_steps one_loop.
Proof.
  cofix self.
  eapply more.
  { eapply step_loop_go. }
  eapply more.
  { eapply step_seq_next. }
  apply self.
Qed.

End Labeled.

From Paco Require Import paco.

Module Tree.

Variant nd : Type -> Prop :=
| Or : nd bool.

Definition or {R : Type} (t1 t2 : itree nd R) : itree nd R :=
  Vis Or (fun b : bool => if b then t1 else t2).

(* Flip a coin *)
Definition choice {E} `{nd -< E} : itree E bool := trigger Or.

Definition eval_def : com -> itree (callE _ _ +' nd) unit := (fun (c : com) =>
    match c with
    | loop c =>
      (b <- choice;;
      if b : bool
      then Ret tt
      else (trigger (Call c);; trigger (Call (loop c))))%itree
    | choose c1 c2 =>
      (b <- choice;;
      if b : bool
      then trigger (Call c1)
      else trigger (Call c2))%itree
    | (t1 ;; t2)%com => (trigger (Call t1);; trigger (Call t2))%itree
    | skip => Ret tt
    end
  ).
Definition eval : com -> itree nd unit := rec eval_def.

(* [itree] semantics of [one_loop]. *)
Definition one_loop_tree : itree nd unit :=
  rec (fun _ : unit =>
    (* note: [or] is not allowed under [mfix]. *)
    b <- choice;;
    if b : bool then
      Ret tt
    else
      trigger (Call tt))%itree tt.

Import Coq.Classes.Morphisms.

Lemma eval_skip: rec eval_def skip ≈ Ret tt.
Proof.
  rewrite rec_as_interp. cbn. rewrite interp_ret. reflexivity.
Qed.

(* SAZ: the [~] notation for eutt wasn't working here. *)
Lemma eval_one_loop : eval one_loop ≈ one_loop_tree.
Proof.
  einit. ecofix CIH. edrop.
  setoid_rewrite rec_as_interp.
  setoid_rewrite interp_bind.
  setoid_rewrite interp_vis.
  setoid_rewrite tau_eutt.
  setoid_rewrite interp_ret.
  setoid_rewrite bind_bind.
  setoid_rewrite bind_ret_l.
  setoid_rewrite bind_vis.
  evis. intros.
  setoid_rewrite bind_ret_l.
  destruct v.
  - setoid_rewrite interp_ret. apply reflexivity.
  - setoid_rewrite interp_bind.
    setoid_rewrite interp_recursive_call.
    setoid_rewrite eval_skip.
    setoid_rewrite bind_ret_l.
    eauto with paco.
Qed.

End Tree.
