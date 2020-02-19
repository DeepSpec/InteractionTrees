From ITree Require Import
     ITree
     ITreeFacts
     ITreeDefinition
     Eq
     Divergence
.

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

(** *Strongly Guarded CCS*
   - Strongly Guarded: for any summation, the top level process is a visible
                       action.

   Idea(?) : Instead of interpreting non-determination as an uninterpreted event,
   let's model them using K-Trees.

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

  (** Strong Guardedness Condition:
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

  (* TODO:
     Show process congruence is an equivalence relation. *)

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
      strong_bisimulation p q.

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


(** *Denotational Semantics

    Denotation of operational CCS in ITrees.
 *)

(*
Section DenoteCCS.

  Infix "≡?" := (eq_idx) (at level 70).

  (* IY: We leave the parallel composition operator as an uninterpreted event
         for now. *)
  Variant eff : Type -> Type :=
  | ActE (x : label) : eff unit
  | OrE : eff bool
  | ParE : eff bool
  .

  Fixpoint denote_seq_ccs (sp : seq_ccs) : itree eff unit :=
    match sp with
    | Zero => ret tt
    | Or a b =>
      let p1 := denote_seq_ccs a in
      let p2 := denote_seq_ccs b in
      Vis OrE (fun (b : bool) => if b then p1 else p2)
    | Act x k =>
      let p := denote_seq_ccs k in
      Vis (ActE x) (fun _ => p)
    end.

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

  (* Hiding function for denoting the `New` operator. *)
  Definition hide (x : idx) {E : Type -> Type} : eff ~> eff :=
    fun _ e =>
      match e with
      | ActE a =>
        ActE (match_action x a)
      | x => x
      end.

  (* The generating operator, bang.
     IY: Can we write this using the `iter` combinator? *)
  CoFixpoint bang (body : itree eff unit -> (itree eff ((itree eff unit) + unit))):
    (itree eff unit) -> itree eff unit :=
    fun (a : itree eff unit) => ab <- body a;;
             match ab with
             | inl a => Vis ParE (fun (b : bool) => if b then Tau (a) else bang body a)
             | inr b => Ret b (* never going to be reached *)
             end
  .

  Fixpoint denote_ccs (p : ccs) : itree eff unit :=
    match p with
    | Proc x => denote_seq_ccs x
    | New x a => let k := denote_ccs a in
                translate (@hide x eff) k
    | Par a b => let k1 := denote_ccs a in
                let k2 := denote_ccs b in
                Vis ParE (fun (b : bool) => if b then k1 else k2)
    | Bang x => bang (fun a => ret (inl a)) (denote_ccs x)
    end.

  Compute (burn 100 (denote_ccs (Bang (Proc (Or Zero Zero))))).

  (* "CTree" : Concurrent trees, as itree denotations of CCS... *)
  Definition ctree := itree eff unit.

  Inductive ctree_cong : ctree -> ctree -> Prop :=
  (* II. Ambiguity *)
  | CEQ_OrAssoc (t u v : ctree):
      ctree_cong (Vis OrE (fun (b1 : bool) => if b1 then t else (Vis OrE (fun (b2 : bool) => if b2 then u else v))))
               (Vis OrE (fun (b1 : bool) => if b1 then (Vis OrE (fun (b2 : bool) => if b2 then t else u)) else v))
  | CEQ_OrComm (t u : ctree):
      ctree_cong (Vis OrE (fun (b : bool) => if b then t else u))
               (Vis OrE (fun (b : bool) => if b then u else t))
  | CEQ_OrUnit (u : ctree):
      ctree_cong (Vis OrE (fun (b : bool) => if b then ret tt else u))
               u
  | CEQ_OrRefl (u : ctree):
      ctree_cong (Vis OrE (fun (b : bool) => if b then u else u))
                 u
  (* VIII. Commitment *)
  | CEQ_TauJoin (u : ctree):
      ctree_cong (Vis (ActE Silent) (fun _ => Vis (ActE Silent) (fun _ => u)))
                 (Vis (ActE Silent) (fun _ => u))
  | CEQ_TauOr (u : ctree):
      ctree_cong (Vis OrE (fun (b : bool) => if b then u else (Vis (ActE Silent) (fun _ => u))))
                 u
  | CEQ_TauDiv (t u : ctree):
      divergence t ->
      ctree_cong (Vis (ActE Silent) (fun _ => Vis OrE (fun (b : bool) => if b then u else t)))
                 (Vis OrE (fun (b : bool) => if b then u else t))
  .

  Inductive partial_order : ctree -> ctree -> Prop :=
  | PO_Refl (t : ctree):
      partial_order t t
  | PO_Trans (t u v : ctree):
      partial_order t u -> partial_order u v ->
      partial_order t v
  | PO_Div (t u : ctree): (* A diverging tree is bottom. *)
      divergence t ->
      partial_order t u
  | PO_TauOr x (t u t' u': ctree):
      partial_order (Vis OrE (fun (b : bool) => if b then Vis (ActE Silent) (fun _ => t) else Vis (ActE Silent) (fun _ => u)))
                 (Vis OrE (fun (b : bool) => if b then Vis (ActE Silent) (fun _ => t') else Vis (ActE Silent) (fun _ => u'))) ->
      partial_order (Vis OrE (fun (b : bool) => if b then Vis (ActE (Visible x)) (fun _ => t) else Vis (ActE (Visible x)) (fun _ => u)))
                 (Vis OrE (fun (b : bool) => if b then Vis (ActE (Visible x)) (fun _ => t') else Vis (ActE (Visible x)) (fun _ => u')))
  .

  (* TODO: Use Proper Instance and congruence for this definition? *)
  Definition ctree_equiv (t u : ctree) :=
    partial_order t u /\ partial_order u t /\ u ≈ t.

End DenoteCCS.

Theorem denotational_model :
  forall p q, weak_bisimulation p q -> ctree_equiv (denote_ccs p) (denote_ccs q).
Proof.
  intros. destruct p, q.
  - cbn. destruct p, p0.
    + cbn. constructor. constructor. constructor. constructor.
      reflexivity.
    + cbn. constructor. Admitted. (* IY: Something's not quite right here. *)

Theorem full_abstraction :
  forall p q, ctree_equiv (denote_ccs p) (denote_ccs q) -> weak_bisimulation p q.
Proof. Admitted.

(* TODO: Write handler for denotation. (Prop or State monad?) *)
*)
