(* A nondeterministic Imp *)

From Coq Require Import
     Relations.

From ITree Require Import
     ITree
     Interp.Recursion
     Interp.RecursionFacts
     Interp.MorphismsFacts.

Import ITreeNotations.

Inductive com : Type :=
| loop : com -> com (* Nondeterministically, continue or stop. *)
| choose : com -> com -> com
| skip : com
| seq : com -> com -> com
.

Infix ";;" := seq (at level 100, right associativity) : com_scope.
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

Variant nd : Type -> Type :=
| Or : nd bool.

Definition or {R : Type} (t1 t2 : itree nd R) : itree nd R :=
  Vis Or (fun b : bool => if b then t1 else t2).

(* Flip a coin *)
Definition choice {E} `{nd -< E} : itree E bool := send Or.

Definition eval_def := (fun (c : com) =>
    match c with
    | loop c =>
      (b <- choice;;
      if b : bool
      then Ret tt
      else (send (Call c);; send (Call (loop c))))%itree
    | choose c1 c2 =>
      (b <- choice;;
      if b : bool
      then send (Call c1)
      else send (Call c2))%itree
    | (t1 ;; t2)%com => (send (Call t1);; send (Call t2))%itree
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
      send (Call tt))%itree tt.

Import Coq.Classes.Morphisms.

Lemma eval_skip: rec eval_def skip ≈ Ret tt.
Proof.
  rewrite rec_as_interp. cbn. rewrite interp_ret. reflexivity.
Qed.

(* SAZ: the [~] notation for eutt wasn't working here. *)
Lemma eval_one_loop : eval one_loop ≈ one_loop_tree.
Proof.
  wcofix CIH. unfold eval, one_loop_tree.
  setoid_rewrite rec_as_interp; setoid_rewrite interp_bind.
  wstep. wstep. repeat red. cbn. econstructor.
  wstep. repeat red. cbn. econstructor.
  left. rewrite !bind_ret_, !interp_ret, !bind_ret_.
  destruct x.
  - rewrite !interp_ret. apply reflexivity.
  - rewrite !send_is_vis_ret, interp_bind.
    setoid_rewrite interp_recursive_call.
    rewrite eval_skip. rewrite bind_tau, bind_ret.
    rewrite !tau_eutt. eauto with paco.
Qed.

End Tree.
