(* A nondeterministic Imp *)

From Coq Require Import
     Relations.

From ITree Require Import
     ITree.

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
Definition choice : itree nd bool := ITree.liftE Or.

Definition eval : com -> itree nd unit :=
  mfix1 (fun _ lift eval (c : com) =>
    match c with
    | loop c =>
      (* note: [or] is not allowed under [mfix]. *)
      (b <- lift _ choice;;
      if b : bool then Ret tt else (eval c;; eval (loop c)))%itree
    | choose c1 c2 =>
      (b <- lift _ choice;;
      if b : bool then eval c1 else eval c2)%itree
    | (t1 ;; t2)%com => (eval t1;; eval t2)%itree
    | skip => Ret tt
    end
  ).

(* [itree] semantics of [one_loop]. *)
Definition one_loop_tree : itree nd unit :=
  mfix0 (fun _ lift self  =>
    (* note: [or] is not allowed under [mfix]. *)
    b <- lift _ choice;;
    if b : bool then
      Ret tt
    else
      self)%itree.

Import Coq.Classes.Morphisms.

(* SAZ: the [~] notation for eutt wasn't working here. *)
Lemma eval_one_loop : eutt (eval one_loop) (one_loop_tree).
Proof.
  pupto2_init.
  pcofix self.
  pupto2 (eutt_clo_trans nd unit). econstructor.
  { unfold eval, mfix1.
    rewrite (mfix_unfold nd com (fun _ => unit)); cbn.
    unfold id, choice, ITree.liftE. rewrite vis_bind. reflexivity.
  }
  { unfold one_loop_tree, mfix0.
    rewrite (mfix_unfold nd unit (fun _ => unit)); cbn.
    unfold id, choice, ITree.liftE. rewrite vis_bind. reflexivity.
  }
  cbn.
  pfold.
  apply euttF1_euttF.
  constructor.
  constructor.
  intros b.
  pupto2 (eutt_clo_trans nd unit). econstructor.
  { rewrite ret_bind; reflexivity. }
  { rewrite ret_bind; reflexivity. }
  destruct b.
  (* true *)
  { apply grespectful2_incl. left.
    pfold. apply euttF1_euttF; repeat constructor. }
  (* false *)
  pupto2 (eutt_clo_trans nd unit). econstructor.
  { match goal with
    | [ |- eutt (ITree.bind ?t1 _) _ ] =>
      assert (Ht1 : eutt t1 (Ret tt))
    end.
    { pfold.
      apply euttF1_euttF.
      repeat (constructor; cbn).
    }
    rewrite Ht1.
    rewrite ret_bind.
    reflexivity.
  }
  { reflexivity. }
  apply grespectful2_incl. right.
  exact self.
Qed.

End Tree.
