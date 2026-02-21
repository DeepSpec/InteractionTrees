#[global] Set Warnings "-intuition-auto-with-star".

From Coinduction Require Import all.
Require Import Program.Tactics.

From Paco Require Import paco.

Ltac inv H := inversion H; clear H; subst.

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

(* RTODO: Deprecate these *)

Lemma pacobot1 (T0 : Type) (gf : rel1 T0 -> rel1 T0) (r : rel1 T0)
  : paco1 gf bot1 <1= paco1 gf r.
Proof.
  intros x0 H. apply (paco1_mon _ H); contradiction.
Qed.

Lemma pacobot2 (T0 : Type) (T1 : T0 -> Type) (gf : rel2 T0 T1 -> rel2 T0 T1) (r : rel2 T0 T1)
  : paco2 gf bot2 <2= paco2 gf r.
Proof.
  intros x0 x1 H. eapply (paco2_mon _ H); contradiction.
Qed.

(* [coinduction]-like tactics  *)

(* A smarter version of this should be part of the [coinduction] library *)


Ltac step_ :=
match goal with
| |- gfp ?b ?x ?y ?z => apply ((gfp_fp b x y z))
| |- elem ?R ?x ?y ?z => apply (b_chain R x y z)
| |- gfp ?b ?x ?y => apply ((gfp_fp b x y))
| |- elem ?R ?x ?y => apply (b_chain R x y)
| |- gfp ?b ?x => apply ((gfp_fp b x))
| |- elem ?R ?x => apply (b_chain R x)
end.

Ltac step := first [step_ | red; step_ | Coinduction.tactics.step | 
match goal with 
| [|- gfp ?b _ _] => apply (gfp_fp b)
end ].

(* Technically, stepping in hypotheses in the direction shown below
should be backstepping, and vice versa.
This is something that we should choose on in a meeting. *)

Ltac step_in H :=
  match type of H with
  | gfp ?b ?x ?y ?z => apply (gfp_fp b x y z) in H
  | gfp ?b ?x ?y => apply (gfp_fp b x y) in H
  | gfp ?b ?x => apply (gfp_fp b x) in H
  | _ => red in H; step_in H
  end.
Tactic Notation "step" "in" ident(H) := step_in H.

Ltac backstep := 
  match goal with 
| [|- _ _ _ _ (gfp ?b) _ _]=> 
    apply (gfp_pfp b) 
| [|- _ _ _ _ (elem ?c) _ _ ]=>
    apply (gfp_bchain c)
end. 

Ltac backstep_in H := 
  match type of H with 
| _ _ _ _ (gfp ?b) _ _=> 
    apply (gfp_fp b) in H 
| _ _ _ _ (elem ?c) _ _ =>
    apply (gfp_bchain c) in H 
end. 

Tactic Notation "backstep" "in" ident(H) := backstep_in H.

(* Oft-used induction tactic for general IHs. *)
Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

