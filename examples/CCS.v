
Set Implicit Arguments.
Set Contextual Implicit.

(* CCS term with an open set of ports A and labels L referring to
   other processes. *)
Inductive ccs (A L : Type) : Type :=
| Done : ccs A L
| Action : A -> ccs A L -> ccs A L
| Choice : ccs A L -> ccs A L -> ccs A L
| Par : ccs A L -> ccs A L -> ccs A L
| Hide : A -> ccs A L -> ccs A L
(* Become process [L] (allows recursive definitions) *)
| Exec : L -> ccs A L
.

(* TODO: substitution, congruence, bisimulation *)

Inductive actions : Type :=
| Coin
| Tea
| Paper
.

Inductive labels : Type :=
| STU
| TM
.

Definition stu : ccs actions labels :=
  Action Paper (Action Coin (Action Tea (Exec STU))).

Definition tm : ccs actions labels :=
  Action Coin (Action Tea (Exec TM)).

(* LTS *)
Inductive step {A L : Type} (exec : L -> ccs A L) :
  option A -> ccs A L -> ccs A L -> Prop :=
| step_Action a t : step exec (Some a) (Action a t) t
| step_Exec l : step exec None (Exec l) (exec l)
(* Some definitions take a step in [u] or [v] at the same time,
   leading to different semantics if taus can be counted. *)
| step_Choice_L u v : step exec None (Choice u v) u
| step_Choice_R u v : step exec None (Choice u v) v
| step_Par_L oa u u' v :
    step exec oa u u' ->
    step exec oa (Par u v) (Par u' v)
| step_Par_R oa u v v' :
    step exec oa v v' ->
    step exec oa (Par u v) (Par u v')
| step_Par_Com a u u' v v' :
    step exec (Some a) u u' ->
    step exec (Some a) v v' ->
    step exec None (Par u v) (Par u' v')
| step_Hide_Tau a0 u u' :
    step exec None u u' ->
    step exec None (Hide a0 u) (Hide a0 u')
| step_Hide_Vis a a0 u u' :
    a <> a0 ->
    step exec (Some a) u u' ->
    step exec (Some a) (Hide a0 u) (Hide a0 u')
.

(* Structural congruence *)
Inductive ccs_eq {A L : Type} (exec : L -> ccs A L) :
  ccs A L -> ccs A L -> Prop :=
.

Inductive step2 {A L : Type} (exec : L -> ccs A L) :
  ccs A L -> ccs A L -> Prop :=
(* Some definitions take a step in [u] or [v] at the same time,
   leading to different semantics if taus can be counted. *)
| step2_Par_L u u' v :
    step2 exec u u' ->
    step2 exec (Par u v) (Par u' v)
| step2_Par_R u v v' :
    step2 exec v v' ->
    step2 exec (Par u v) (Par u v')
| step2_Hide_Tau a0 u u' :
    step2 exec u u' ->
    step2 exec (Hide a0 u) (Hide a0 u')
| step2_Par_Com a u1 u2 v1 v2 :
    step2 exec
          (Par (Choice (Action a u1) u2) (Choice (Action a v1) v2))
          (Par u1 v1)
.

(** Translation of LTS into ITrees *)
From ITree Require Import ITree
                          Interp.Interp
                          Interp.Handler.
From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.
Open Scope monad_scope.

Class DecEq (A : Type) : Type := {
  eqb : A -> A -> bool;
}.

(* Visible behavior is output actions and nondeterminism. *)
Inductive ccsE (A : Type) : Type -> Type :=
| Out : A -> ccsE A unit
.

(* Nondeterminism and failure *)
Inductive ndE : Type -> Type :=
| Choose : ndE bool
| Oops : ndE void
.

Definition action {A E} `{ccsE A -< E} : A -> itree E unit :=
  embed (@Out _).

Definition choose {E} `{ndE -< E} : itree E bool :=
  embed Choose.

Definition or {E R} `{ndE -< E} :
  itree E R -> itree E R -> itree E R :=
  fun u v =>
    b <- choose;; if b : bool then u else v.

(* Failure *)
Definition oops {E R} `{ndE -< E} : itree E R :=
  vis Oops (fun v => match v : void with end).

Definition assert {E} `{ndE -< E} : bool -> itree E unit :=
  fun b => if b then ret tt else oops.

Definition done {E} : itree E unit := ret tt.

Definition exec {L E} `{callE L unit -< E} : L -> itree E unit :=
  embed Call.

Definition hide {A E} `{DecEq A} :
  A -> itree (ccsE A) ~> itree (ccsE A +' E) :=
  fun a0 =>
    interp (fun _ e => match e in ccsE _ T return _ T with
                    | Out a => if eqb a0 a then ret tt else trigger (Out a)
                    end).

Definition flip {A B C} (f : A -> B -> C) : B -> A -> C :=
  fun y x => f x y.


(*
Definition handleOut {A E F} `{E -< F} {R}
           (h : A -> itree (ccsE A +' E) ~> itree F) :
  itree (ccsE A +' E) ~> itree F :=
  handle1 (fun _ e =>
             match e in ccsE _ T return (T -> _) -> _ with
             | Out a => fun k => h a (k tt)
             end).


(* Parallel interpretation of an ITree. *)
Definition par {A E F} `{DecEq A} `{ccsE A -< F} `{ndE -< F} `{E -< F}
           (u0 v0 : itree (ccsE A +' E) unit) :
  itree F unit :=
  flip rec (u0, v0) (fun '(u, v) =>
    or (or (* Step in u *)
           (flip handleOut u (fun a u' =>
            action a;; lift (Call (u', v))))
           (* Step in v *)
           (flip handleOut v (fun a v' =>
            action a;; lift (Call (u, v'))))
       )
       (* Synchronized step *)
       (flip handleOut u (fun au u' =>
        flip handleOut v (fun av v' =>
          assert (eqb au av);;
          lift (Call (u', v'))
        ))
       )
  ).
*)
