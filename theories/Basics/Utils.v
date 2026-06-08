#[global] Set Warnings "-intuition-auto-with-star".

From Coinduction Require Import all.
Require Import Program.Tactics.

Ltac inv H := inversion H; clear H; subst; try easy.

(* [inv], [rewrite_everywhere], [..._except] are general purpose *)

Lemma hexploit_mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.
Ltac hexploit x := eapply hexploit_mp; [eapply x|].

Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).

Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                 match H with X => fail 1 | _ => rewrite lem in H end
             end); repeat rewrite lem).


Ltac copy h :=
  let foo := fresh "cpy" in
  assert (foo := h).

Global Tactic Notation "intros !" := repeat intro.

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

(* inv by name of the Inductive relation *)
Ltac invn f :=
    match goal with
    | [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

(* destruct by name of the Inductive relation *)
Ltac destructn f :=
    match goal with
    | [ id: f |- _ ] => destruct id
    | [ id: f _ |- _ ] => destruct id
    | [ id: f _ _ |- _ ] => destruct id
    | [ id: f _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => destruct id
    end.

(* apply by name of the Inductive relation *)
Ltac appn f :=
    match goal with
    | [ id: f |- _ ] => apply id
    | [ id: f _ |- _ ] => apply id
    | [ id: f _ _ |- _ ] => apply id
    | [ id: f _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => apply id
    end.

(* eapply by name of the Inductive relation *)
Ltac eappn f :=
    match goal with
    | [ id: f |- _ ] => eapply id
    | [ id: f _ |- _ ] => eapply id
    | [ id: f _ _ |- _ ] => eapply id
    | [ id: f _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => eapply id
    end.

Ltac break H :=
  repeat match type of H with
          | exists X, _  => destruct H
          |  _ /\ _ => destruct H
          |  _ \/ _ => destruct H
          |  _ /\ _ => split
          end.

Ltac crunch :=
  repeat match goal with
          | [ H : exists X, _ |- _ ] => destruct H
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : _ \/ _ |- _ ] => destruct H
          | [ |- _ /\ _ ] => split
          end.

Ltac saturate H :=
  match goal with
          | [ H1 : forall a b, ?R a b -> _,
              H2 : forall a b, ?R b a -> _,
                H : ?R ?A ?B  |- _ ] => pose proof (H1 A B H);
                                        pose proof (H2 B A H);
                                        clear H; crunch
          end.

(* [coinduction]-like tactics  *)

(* Until https://github.com/damien-pous/coinduction/pull/22 gets merge *)
Lemma pfp_gfp {X} {L : CompleteLattice X} (b : mon X): b (gfp b) <= (gfp b).
Proof. apply b_chain. Qed.

  (* in goal: elem -> b elem -> gfp b -> b gfp *)

Ltac step_ :=
  match goal with
  | |- gfp ?b ?x ?y ?z => apply ((gfp_fp b x y z))
  | |- elem ?R ?x ?y ?z => apply (b_chain R x y z)
  | |- gfp ?b ?x ?y => apply ((gfp_fp b x y))
  | |- elem ?R ?x ?y => apply (b_chain R x y)
  | |- gfp ?b ?x => apply ((gfp_fp b x))
  | |- elem ?R ?x => apply (b_chain R x)
  end.

Ltac step := match goal with
    | |- context [gfp ?b] => apply (pfp_gfp b)
    | |- context [elem ?R] => first [apply (b_chain R) | apply (gfp_bchain R)]
    end. 

Ltac step_in h :=
match type of h with
| context [gfp ?b] => apply (gfp_pfp b) in h
end.

Tactic Notation "step" "in" ident(h) := step_in h.

Ltac unstep :=
match goal with
| |- context [gfp ?b] => apply (gfp_pfp b)
end.

Ltac unstep_in h :=
match type of h with
| context [gfp ?b] => apply (pfp_gfp b) in h
end.

Tactic Notation "unstep" "in" ident(h) := unstep_in h.

(* Oft-used induction tactic for general IHs. *)
Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Ltac apply_leq := match goal with 
  | [H : _ <= _ |- _]=> intros; apply H 
  | [H : leq _ _ |- _]=> intros; apply H 
end.

(* nonlinear pattern works here *)
Ltac induct_on_premise := match goal with 
| H: context [?rel _] |- context [?rel ] => induction H
end. 

Create HintDb mono. 

Global Hint Extern 4 => apply_leq : mono.

Ltac monauto := (solve [
(* break `Proper`, introduce names and premises` *)
cbv; 
intros; 
(* find hypothesis matching goal and proceed by cases *)
induct_on_premise; 
(* break down each case as necessary. `solve` will backtrack in a helpful way.  *)
try econstructor; 
(* use monotonicity fact itself: [sim] <= [sim'] *)
try apply_leq; 
eauto] || fail "`monauto` could not solve this goal."). 

(* TODO: let user add a tactic db here *)
(* ----------------------------------------------------------------- *)

(* inf_closed automation *)
Ltac inf_closed_forall_auto :=
  repeat (apply inf_closed_all; intro).

Ltac inf_closed_impl_auto :=
  repeat (apply inf_closed_impl; [intros!; apply_leq; firstorder|]).

Ltac inf_closed_final_auto :=
  solve [repeat intro; try solve [firstorder]; try apply_leq ; firstorder].

Ltac inf_closed_auto :=
  repeat (inf_closed_forall_auto || inf_closed_impl_auto || inf_closed_final_auto).

(* tower induction always leaves the goal with the form `forall _ : Chain, ...` ; 
   match on this type and clear the old Chain *) 
Ltac clear_old_chain := match goal with 
  | c : ?T |- forall _ : ?T, _ => clear c; intro c end.

Ltac tower_induction := apply tower; [inf_closed_auto|clear_old_chain].
Tactic Notation "tower" "induction" := tower_induction.
