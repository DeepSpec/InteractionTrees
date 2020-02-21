From ITree Require Import
     ITree
     ITreeFacts
     ITreeDefinition
     Eq
     Divergence
.

From Paco Require Import paco.

From ExtLib Require Import
     Structures.Monad.

From Coq Require Import
     Arith.EqNat
     Arith.PeanoNat
     Lists.List
     Morphisms
     Program.Equality
     Setoid
     Strings.String
     RelationClasses
     Relations.Relation_Operators
     ZArith.Int.


Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Require Import PropT.

(** *Strongly Guarded CCS*
   - Strongly Guarded: for any summation, the top level process is a visible
                       action.

   We also attempted to impose an extra guardedness condition on the
   non-deterministic continuations: namely, that the immediate continuations
   must be an action event and cannot be a silent step.
   This constraint was a proposed work-around to the approach in [WeakCCS.v] and
   [ccs.org].
 *)


Import Monads.
Import MonadNotation.
Import ListNotations.
Local Open Scope monad_scope.

Section GuardedCCS.

  (** *Syntax *)

  (* Locally Nameless representation of variables. *)
  Variant idx : Type :=
  | I_string (s : string) : idx
  | I_nat (n : nat) : idx
  .
  Definition eq_idx : idx -> idx -> bool :=
    fun i1 i2 =>
      match i1 with
      | I_string s => match i2 with
                    | I_string s => true
                    | _ => false
                    end
      | I_nat n => match i2 with
                  | I_nat n => true
                  | _ => false
                  end
      end
  .

  Infix "≡?" := (eq_idx) (at level 70).

  (* CCS labels have polarity. *)
  Variant visible : Type :=
  | In (i : idx)
  | Out (i : idx)
  .
  Variant label : Type :=
  | Visible (vx : visible)
  | Silent
  .

  (* IY: These series of matches seem like they should have a nice functional
     combinator... *)
  Definition match_idx (target x : idx) : idx :=
    if x ≡? target then I_nat 0
    else match x with
         | I_string _ => x
         | I_nat i => I_nat (i + 1)
         end
  .
  Definition match_visible (target : idx) (x : visible) : visible :=
    match x with
    | In x1 => In (match_idx target x1)
    | Out x1 => Out (match_idx target x1)
    end
  .
  Definition match_action (target : idx) (x : label) : label :=
    match x with
    | Silent => Silent
    | Visible v => Visible (match_visible target v)
    end
  .

  (* Strong Guardedness Condition:
     Any sequence of labels under nondeterministic choice must be strongly guarded,
     i.e. the starting label must be an action. *)
  Inductive ccs : Type :=
  | Zero
  | Or (op oq : visible * ccs)
  | Act (l : label) (p : ccs)
  | Par (p q : ccs)
  | New (i : idx) (p : ccs)
  | Bang (p : ccs)
  .

  Class ProcessCongruence (R : ccs -> ccs -> Prop) :=
    {
      sum : forall (p q r : ccs) (x y : visible),
        R p q ->
        R (Or (x, p) (y, r)) (Or (x, q) (y, r));
      new : forall (p q : ccs) (i : idx),
          R p q ->
          R (New i p) (New i q);
      parL : forall (p q r : ccs),
          R p q ->
          R (Par p r) (Par q r);
      parR : forall (p q r : ccs),
          R r p ->
          R (Par r p) (Par r q)
    }.

  (* TODO: Show process congruence is an equivalence relation. *)

  (** *Structural Congruence *)
  Inductive bound : idx -> ccs -> Prop :=
  | B_ActIn (i : idx) (p : ccs):
      bound i (Act (Visible (In i)) p)
  | B_ActOut (i : idx) (p : ccs):
      bound i (Act (Visible (Out i)) p)
  | B_Act (i : idx) (x : label) (p : ccs):
      bound i p ->
      bound i (Act x p)
  | B_Or (i : idx) (p q : ccs) (vp vq : visible):
      bound i p \/ bound i q ->
      bound i (Or (vp, p) (vq, q))
  | B_Par (i : idx) (p q : ccs):
      bound i p \/ bound i q ->
      bound i (Par p q)
  | B_New (i j : idx) (p : ccs):
      bound i p -> not (i ≡? j) ->
      bound i (New j p)
  | B_Bang (i : idx) (p : ccs):
      bound i p ->
      bound i (Bang p)
  .

  Definition free (i : idx) (p : ccs) : Prop := not (bound i p).

  (* We don't get associativity of sum due to the guardedness condition. *)
  Inductive structural_congruence : ccs -> ccs -> Prop :=
  | SC_SumComm (op oq : visible * ccs):
      structural_congruence (Or op oq) (Or oq op)
  | SC_ParComm (p q : ccs):
      structural_congruence (Par p q) (Par q p)
  | SC_ParAssoc (p q r : ccs):
      structural_congruence (Par (Par p q) r) (Par p (Par q r))
  .

  (* TODO: Show structural congruence is a process congruence. *)

  (** *Structural Operational Semantics *)
  Inductive eval : label -> ccs -> ccs -> Prop :=
  | E_ParL (l : label) (p p' q : ccs):
      eval l p p' ->
      eval l (Par p q) (Par p' q)
  | E_ParR (l : label) (p q q' : ccs):
      eval l q q' ->
      eval l (Par p q) (Par p q')
  | E_ParC (i : idx) (p p' q q' : ccs):
      eval (Visible (In i)) p p' ->
      eval (Visible (Out i)) q q' ->
      eval Silent p' q'
  | E_Act (l : label) (p : ccs):
      eval l (Act l p) p
  | E_ResIn (i j : idx) (p p' : ccs):
      not (i ≡? j) ->
      eval (Visible (In i)) p p' ->
      eval (Visible (In i)) (New j p) (New j p')
  | E_ResOut (i j : idx) (p p' : ccs):
      not (i ≡? j) ->
      eval (Visible (Out i)) p p' ->
      eval (Visible (Out i)) (New j p) (New j p')
  | E_ResSilent (j : idx) (p p': ccs):
      eval Silent p p' ->
      eval Silent (New j p) (New j p')
  | E_Bang (p : ccs):
      eval Silent (Bang p) (Par p (Bang p))
  | E_Struct (l : label) (p q r: ccs):
      structural_congruence p q ->
      eval l q r ->
      eval l p r
  .

  (** *Strong Bisimulation *)
  Inductive strong_simulation : ccs -> ccs -> Prop :=
  | StrongSim (p q : ccs) :
      (forall a p', eval a p p' ->
      (exists q', eval a q q' /\ strong_simulation p' q')) ->
     strong_simulation p q
  .
  Inductive strong_bisimulation : ccs -> ccs -> Prop :=
  | StrongBisim (p q : ccs):
      strong_simulation p q -> strong_simulation q p ->
      strong_bisimulation p q
  .
  (** *Weak Bisimulation *)
  Inductive weak_silent_closure : ccs -> ccs -> Prop :=
  | WeakSilentRefl (p : ccs):
      weak_silent_closure p p
  | WeakSilentTrans (p q r : ccs):
      weak_silent_closure q r ->
      eval Silent p q ->
      weak_silent_closure p r
  .
  Inductive weak_visible_closure : ccs -> ccs -> Prop :=
  | WeakVisRefl x (p q r: ccs):
      weak_silent_closure q r ->
      eval (Visible x) p q ->
      weak_visible_closure p r
  | WeakVisTrans x (p q r: ccs):
      weak_visible_closure q r ->
      eval (Visible x) p q ->
      weak_visible_closure p r
  .
  Inductive weak_simulation : ccs -> ccs -> Prop :=
  | WeakSim (p q : ccs) :
      (forall p', eval Silent p p' ->
             exists q', weak_silent_closure q q' /\ weak_simulation p' q') ->
      (forall x p', eval (Visible x) p p' ->
               exists q', weak_visible_closure q q' /\ weak_simulation p' q') ->
      weak_simulation p q
  .
  Inductive weak_bisimulation : ccs -> ccs -> Prop :=
  | WeakBisim (p q : ccs):
      weak_simulation p q -> weak_simulation q p ->
      weak_bisimulation p q
  .

End GuardedCCS.

Section DenoteCCS.

  Infix "≡?" := (eq_idx) (at level 70).

  Inductive eff : Type -> Type :=
  | ActE (x : visible) : eff unit
  | OrE (n : nat) : eff nat
  | FailE : eff void
  .

  Definition ctree := itree eff unit.

  Definition fail : ctree :=
    x <- trigger FailE ;;
      match (x : void) with end.

  CoFixpoint par (p q : ctree) : ctree :=
    let par_left (p' q' : ctree) :=
       match p', q' with
        | Vis (ActE l) k, _ => trigger (ActE l) ;; par (k tt) q'
        | Tau tp', _ => par tp' q'
        | Ret _, _ => q'
        | Vis (OrE _) _, Vis (OrE _) _ => par p' q'
        | _, _ => fail
        end
    in
    let par_right (p' q' : ctree) : ctree :=
        match p', q' with
        | _, Vis (ActE l) k => trigger (ActE l) ;; par (k tt) p'
        | _, Tau tq' => par p' tq'
        | _, Ret _ => p'
        | Vis (OrE _) _, Vis (OrE _) _ => par p' q'
        | _, _ => fail
        end
    in
    let par_comm (p' q' : ctree) : ctree :=
        match p', q' with
        | Vis (ActE (In pl)) pk, Vis (ActE (Out ql)) qk
        | Vis (ActE (Out pl)) pk, Vis (ActE (In ql)) qk =>
          if pl ≡? ql then
            Tau (par (pk tt) (qk tt))
          else
            fail
        | Vis (OrE _) _, Vis (OrE _) _ => par p' q'
        | _, _ => fail
        end
    in
    match (observe p), (observe q) with
    | VisF (OrE n1) k1, VisF (OrE n2) k2 =>
      Vis (OrE (n1 + n2 + (n1 * n2))) (fun n0 : nat =>
        if beq_nat n0 n1
        then par_left (k1 n0) q
        else if beq_nat n0 (n2 + n2)
          then par_right p (k2 (n0 - n1))
          else par_comm (k1 ((n0 - n1 - n2) mod n2)) (k2 ((n0 - n1 - n2) / n1)))
    | _, _ =>
      Vis (OrE 3) (fun x : nat =>
      if beq_nat x 0 then par_left p q
      else if beq_nat x 1 then par_right p q
          else par_comm p q)
    end
  .

  (* Hiding function for denoting the `New` operator. *)
  Definition hide (x : idx) {E : Type -> Type} : eff ~> eff :=
    fun _ e =>
      match e with
      | ActE a =>
        ActE (match_visible x a)
      | x => x
      end.
  
  (* Anomaly "cannot define an evar twice." *)
  (* Definition bang (p : ctree) : ctree :=
    iter (C := Kleisli _) (fun prc => trigger p;;
                             ret (inl p)) p. *)

  Definition bang (p : itree eff unit): itree eff unit :=
      iter (a := ctree -> ctree)
         (b := unit)
         (C := Kleisli _) (fun (k : ctree -> ctree) =>
                             ret (inl (par (k p)))) (fun x => Ret tt).
  
  Lemma bang_unfold:
    forall p, (bang p) ≈ par p (bang p).
  Proof.
    intros. unfold bang at 1.
    match goal with
      |- iter ?body ?a ≈ _ => generalize (iter_unfold body);
                              intro eq; specialize (eq a)
    end.
    rewrite eq. cbn. rewrite bind_ret_l. cbn.  match goal with
      |- iter ?body ?a ≈ _ => generalize (iter_unfold body);
                              intro eq'; specialize (eq' a)
    end.
    rewrite eq'. cbn. rewrite bind_ret_l. cbn.
    unfold bang at 1. pcofix CIH. pstep.
  Admitted.

  Fixpoint denote_ccs (prog : ccs) : ctree :=
    match prog with
    | Zero => Ret tt
    | Or (vp, p) (vq, q) =>
      let dp := denote_ccs p in
      let dq := denote_ccs q in
      x <- trigger (OrE 2);;
        if beq_nat x 0 then
          trigger (ActE vp) ;; dp
        else trigger (ActE vq) ;; dp
    | Act l p =>
      let dp := denote_ccs p in
      match l with
      | Visible x =>
        trigger (ActE x) ;; dp
      | Silent =>
        Tau (dp)
      end
    | Par p q =>
      let dp := denote_ccs p in
      let dq := denote_ccs q in
      par dp dq
    | New l p =>
      let dp := denote_ccs p in
      translate (@hide l eff) dp
    | Bang p =>
      let dp := denote_ccs p in
      bang dp
    end
  .

  (** *Interpretation of CCS model *)

  Inductive CCS_handler : eff ~> PropT eff :=
    | CCSAct: forall l, CCS_handler (ActE l) (trigger (ActE l))
    | CCSOr: forall (n x: nat), x <= n -> CCS_handler (OrE n) (Ret x)
  .

  Definition interp_CCS : itree eff ~> PropT eff :=
    interp_prop (CCS_handler).

  Definition model_CCS (c : ccs) : PropT eff unit :=
    interp_CCS (denote_ccs c).

  Definition model := PropT eff unit.

  Definition model_eq (ml mr : model): Prop :=
    forall t, (ml t -> mr t) /\ (mr t -> ml t).

  Infix "⩭" := (model_eq) (at level 30).

  Ltac model_crush :=
    cbn; unfold model_CCS; cbn;
      unfold interp_CCS; unfold interp_prop;
        unfold model_eq; intros; intuition.

  (** *Algebraic Properties of Denotation *)
  (* Equational properties that should hold over our denotation.
     (Good sanity check *and* evidence that our model is nice.) *)
  Lemma par_unit:
    forall (p : ccs), model_CCS p ⩭ model_CCS (Par p Zero).
  Proof.
    intro; destruct p; model_crush.
    - admit.
  Admitted.

  Lemma par_reflexive:
    forall (p : ccs), model_CCS p ⩭ model_CCS (Par p p).
  Proof.
    intro; destruct p; model_crush.
  Qed.

  Lemma par_comm:
    forall (p q : ccs), model_CCS (Par p q) ⩭ model_CCS (Par q p).
  Proof.
    intro; destruct p; destruct q; model_crush.
  Qed.

  Lemma par_assoc:
    forall (p q r : ccs), model_CCS (Par p (Par q r)) ⩭ model_CCS (Par (Par p q) r).
  Proof.
    intro; destruct p; destruct q; destruct r; model_crush.
  Qed.

  Lemma or_comm:
    forall (op oq : visible * ccs), model_CCS (Or op oq) ⩭ model_CCS (Or oq op).
  Proof.
    intro; destruct op; destruct oq; model_crush.
  Qed.

  (* To check that our denotation is a sensible model, we prove that the equational
     properties from our operational semantics is preserved. *)
  Theorem congruence_preservation:
    forall (p q : ccs), structural_congruence p q ->
                   model_CCS p ⩭ model_CCS q.
  Proof.
    intro; destruct p; destruct q; model_crush.
  Qed.

  Theorem weak_bisimulation_preservation:
    forall (p q : ccs), weak_bisimulation p q ->
                   model_CCS p ⩭ model_CCS q.
  Proof.
    intro; destruct p; destruct q. model_crush.
  Qed.

  (** *Full Abstraction Theorem
     The notion of weak bisimulation in operational semantics coincides with
     model equivalence. *)
  Theorem full_abstraction:
    forall (p q : ccs),
      (weak_bisimulation p q -> model_CCS p ⩭ model_CCS q) /\
      (model_CCS p ⩭ model_CCS q -> weak_bisimulation p q).
  Proof.
    intros; destruct p; destruct q; model_crush. 

    model_crush.
  Qed.
