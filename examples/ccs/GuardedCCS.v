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

(* *Finitary, Guarded CCS*
   - Finitary: for any p, Const(p) is finite.
   - Guarded: for any summation, the top level process is an action or
              synchronous step.

   Idea(?) : Instead of interpreting non-determination as an uninterpreted event,
   let's model them using K-Trees.

   We also attempted to impose an extra guardedness condition on the
   non-deterministic continuations: namely, that the immediate continuations
   must be an action event and cannot be a silent step. This did not work, as
   explained below.
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

  (* CCS labels have polarity. *)
  Variant visible : Type :=
  | In (i : idx)
  | Out (i : idx)
  .

  Variant label : Type :=
  | Visible (vx : visible)
  | Silent
  .

  (** Guarded CCS Syntax, following:
     [R.Gorrieri, C.Versari, _Introduction to Concurrency Theory_].
     Any sequence of labels under nondeterministic choice must be guarded,
     i.e. the starting label must be an action. *)

  (*
     We attempted, at first, to define a "Strongly Guarded" CCS.
     Guarded CCS is defined as having action labels immediately under
     nondeterministic choice. _Strongly Guarded_ CCS, on the other hand,
     forces a *visible* action under nondeterministic choice, i.elim .

        Inductive action : Type := Action (x : label) (a : action).
        Inductive seq_ccs : Type :=
                  ...
        | GAct (vx : visible) (a : action).

     However, this notion of "Strongly Guarded" doesn't work for two
     reasons:

     1. You cannot model any _internal step_ that a system may wish
        to take.
        For instance, in vanilla CCS, one can write down the following
        expression:
              τ.N + α -τ-> N
        We cannot write an equivalent expression in Strongly Guarded CCS.

     2. Guardedness condition breaks (is fragile) whenever we try to
        define an _action_ step.
        How do we define a correct action step?

        Let's look at this expression:
              α.τ.N + β.τ.N
        No matter what the system chooses to do, the guardedness condition
        immediately breaks. Since we want to compare the operational weak
        bisimulation to our denotational equivalence of ITree weak bisimulation,
        (for proving full abstraction) we still want to be able to define
        a small step semantics. This syntactic definition will be fragile.
  *)

  (* Sequential Processes. *)
  Inductive seq_ccs : Type :=
  | Zero
  | Or (a b : seq_ccs)
  | Act (l : label) (a : seq_ccs)
  .

  (* CCS Processes. *)
  Inductive ccs : Type :=
  | Proc (p : seq_ccs)
  | Par (a b : ccs)
  | New (i : idx) (a : ccs)
  | Bang (p : ccs)
  .

  Infix "≡?" := (eq_idx) (at level 70).

  (** *Structural Congruence *)
  Inductive scong : seq_ccs -> seq_ccs -> Prop :=
  | SC_Sum (a b : seq_ccs):
      scong (Or a b) (Or b a)
  | SC_CongOr (a a' b b' : seq_ccs):
      scong a a' -> scong b b' ->
      scong (Or a b) (Or a' b')
  | SC_CongAct (l : label) (a a' : seq_ccs):
      scong a a' ->
      scong (Act l a) (Act l a')
  .

  Inductive s_bound : idx -> seq_ccs -> Prop :=
  | SB_ActIn (i : idx) (a : seq_ccs):
      s_bound i (Act (Visible (In i)) a)
  | SB_ActOut (i : idx) (a : seq_ccs):
      s_bound i (Act (Visible (Out i)) a)
  | SB_Act (i : idx) (x : label) (a : seq_ccs):
      s_bound i a ->
      s_bound i (Act x a)
  | SB_Or (i : idx) (a b : seq_ccs):
      s_bound i a \/ s_bound i b ->
      s_bound i (Or a b)
  .

  Inductive bound : idx -> ccs -> Prop :=
  | B_Proc (i : idx) (a : seq_ccs):
      s_bound i a ->
      bound i (Proc a)
  | B_Par (i : idx) (a b : ccs):
      bound i a \/ bound i b ->
      bound i (Par a b)
  | B_New (i j : idx) (a : ccs):
      bound i a -> not (i ≡? j) ->
      bound i (New j a)
  | B_Bang (i : idx) (a : ccs):
      bound i a ->
      bound i (Bang a)
  .

  Definition free (i : idx) (c : ccs) : Prop := not (bound i c).

  Inductive cong : ccs -> ccs -> Prop :=
  | C_Proc (a b : seq_ccs) :
      scong a b ->
      cong (Proc a) (Proc b)
  | C_ParZero (a : ccs):
      cong (Par (Proc Zero) a) (Par a (Proc Zero))
  | C_ParComm (a b : ccs):
      cong (Par a b) (Par b a)
  | C_ParAssoc (a b c : ccs):
      cong (Par (Par a b) c) (Par a (Par b c))
  | C_NewDist (i : idx) (a b : ccs):
      free i a ->
      cong (New i (Par a b)) (Par a (New i b))
  | C_NewZero (i : idx) :
      cong (New i (Proc Zero)) (Proc Zero)
  | C_Bang (a : ccs) :
      cong (Bang a) (Par a (Bang a))
  | C_CongPar (a a' b b': ccs):
      cong a a' -> cong b b' ->
      cong (Par a b) (Par a' b')
  | C_CongNew (i : idx) (a a' : ccs):
      cong a a' ->
      cong (New i a) (New i a')
  | C_CongBang (a a' : ccs):
      cong a a' ->
      cong (Bang a) (Bang a')
  .

  (** *Structural Operational Semantics *)

  Inductive seval : option label -> seq_ccs -> seq_ccs -> Prop :=
  | SE_Pref (x : label) (a : seq_ccs):
      seval (Some x) (Act x a) a
  | SE_SumL (x : label) (a a' b : seq_ccs):
      seval (Some x) a a' ->
      seval (Some x) (Or a b) a'
  | SE_SumR (x : label) (a b b' : seq_ccs):
      seval (Some x) b b' ->
      seval (Some x) (Or a b) b'
  .

  (* 'None' option is used for structural congruence. *)
  Inductive eval : option label -> ccs -> ccs -> Prop :=
  | E_Proc (x : option label) (a a': seq_ccs):
      seval x a a' ->
      eval x (Proc a) (Proc a')
  | E_ParL (x : option label) (a a' b : ccs):
      eval x a a' ->
      eval x (Par a b) (Par a' b)
  | E_ParR (x : option label) (a b b' : ccs):
      eval x b b' ->
      eval x (Par a b) (Par a b')
  | E_ParC (i : idx) (a a' b b' : ccs):
      eval (Some (Visible (In i))) a a' ->
      eval (Some (Visible (Out i))) b b' ->
      eval (Some Silent) a' b'
  | E_ResIn (i j : idx) (a a' : ccs):
      not (i ≡? j) ->
      eval (Some (Visible (In i))) a a' ->
      eval (Some (Visible (In i))) (New j a) (New j a')
  | E_ResOut (i j : idx) (a a' : ccs):
      not (i ≡? j) ->
      eval (Some (Visible (Out i))) a a' ->
      eval (Some (Visible (Out i))) (New j a) (New j a')
  | E_ResSilent (j : idx) (a a': ccs):
      eval (Some Silent) a a' ->
      eval (Some Silent) (New j a) (New j a')
  | E_Struct (x : option label) (a a' b b': ccs):
      cong a b \/ a = b -> cong a' b' \/ a' = b' ->
      eval x a a' -> eval x b b'
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
      eval (Some Silent) p q ->
      weak_silent_closure p r
  .

  Inductive weak_visible_closure : ccs -> ccs -> Prop :=
  | WeakVisRefl x (p q r: ccs):
      weak_silent_closure q r ->
      eval (Some (Visible x)) p q ->
      weak_visible_closure p r
  | WeakVisTrans x (p q r: ccs):
      weak_visible_closure q r ->
      eval (Some (Visible x)) p q ->
      weak_visible_closure p r
  .

  Inductive weak_simulation : ccs -> ccs -> Prop :=
  | WeakSim (p q : ccs) :
      (forall p', eval (Some Silent) p p' ->
             exists q', weak_silent_closure q q' /\ weak_simulation p' q') ->
      (forall x p', eval (Some (Visible x)) p p' ->
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

  (* TODO: Use Proper Instance and congruence for this definition. *)
  Definition ctree_equiv (t u : ctree) :=
    partial_order t u /\ partial_order u t /\ u ≈ t.

End DenoteCCS.

Theorem denotational_model :
  forall p q, weak_bisimulation p q -> ctree_equiv (denote_ccs p) (denote_ccs q).
Proof. Admitted.

Theorem full_abstraction :
  forall p q, ctree_equiv (denote_ccs p) (denote_ccs q) -> weak_bisimulation p q.
Proof. Admitted.

(* TODO: Write handler for denotation. (Prop or State monad?) *)
