From ITree Require Import
     ITree
     ITreeDefinition
     Interp.Traces
     Eq
.

From ExtLib Require Import
     Structures.Functor
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

From Paco Require Import paco.

Require Import ITree.Eq.EqAxiom.
Require Import Fin.

(** * Modeling Concurrency with ITrees (CCS)

    We want to reason about concurrency with ITrees.

    For modeling concurrency, we use Milner's calculus of communicating systems(#)
    (CCS), a predecessor to π-calculus. In CCS, participating processes of a
    concurrent system have indivisible communications that can be composed in
    parallel.

    The primitive in the calculus is a _process_ that can have input and output
    _actions_ in which processes can communicate. Each action has a corresponding
    label, and can act as either an input or output (but not both).
    Processes can only communicate through complementary actions with the same
    label (i.e. same labels with actions of opposing polarity, such that process
    with input action `a` can communicate with a process with output action `a`).


    (#) Milner, R., Communication and Concurrency, 1989.
*)

Import ListNotations.
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

  (** CCS Operators:

      P := ∅          Empty Process
         | a.P1       Action
         | P1 + P2    Choice (Sum type)
         | P1 ∥ P2    Parallel Composition
         | P1 ∖ a     Restriction

      * Empty Process
      * Action: Process P1 performs an action a. This could be a send or
                receive, depending on the polarity of the action a.
      * Choice : either P1 or P2 will be processed.
      * Parallel Composition: Processes P1 and P2 exist simultaneously
      * Restriction: Hides port a in process P1.
  *)


(** *Denotation of CCS with ITrees *)
Section ccs.

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

  (* Labels for defining parity of actions. *)
  Variant Label : Type :=
  | In (l : idx) : Label
  | Out (l : idx): Label
  .

  (* We need a decidable equality on labels for the Restriction and Parallel
  Composition operator. *)
  Theorem label_dec_eq :
    forall (x y : Label), {x = y} + {x <> y}.
  Proof.
    intros. repeat decide equality.
  Qed.

  (* Denotation of CCS Operators as ITree events. *)
  Variant ccsE : Type -> Type :=
  | Or (n : nat) : ccsE nat
     (* Note: choices are zero-indexed. *)
  | Act : Label -> ccsE unit
  | Sync : idx -> ccsE unit
  | Fail : ccsE void
  .

Definition ccs := itree ccsE unit.

End ccs.

(* begin hide *)
Bind Scope ccs_scope with ccs.
Delimit Scope ccs_scope with ccs.
Local Open Scope ccs_scope.

Arguments In {_}.
Arguments Out {_}.
(* end hide *)

Notation ccs' := (itree' ccsE unit).

Infix "≡?" := (eq_idx) (at level 70) : ccs_scope.

Section ccs_combinators.

  (** *Denotation of CCS Combinators *)

  (* The empty process. *)
  Definition zero : ccs := Vis (Or 0) (fun _ => Ret tt).

  Definition fail : ccs := Vis Fail (fun x : void => match x with end).

  (* Action operators, where l denotes the label. *)
  Definition send (l : idx) (k : ccs) : ccs := Vis (Act (@In l)) (fun _ => k).

  Definition recv (l : idx) (k : ccs) : ccs := Vis (Act (@Out l)) (fun _ => k).

  (* Hide operator. *)
  Definition hide' (l : idx) {E : Type -> Type}: ccsE ~> ccsE :=
    fun _ e =>
      match e with
      | Act (@In n) => if n ≡? l then
                        Act (@In (I_nat 0))
                      else
                        match n with
                        | I_string _ => Act (@In n)
                        | I_nat i => Act (@In (I_nat (i + 1)))
                        end
      | Act (@Out n) => if n ≡? l then
                         Act (@In (I_nat 0))
                       else
                         match n with
                         | I_string _ => Act (@Out n)
                         | I_nat i => Act (@Out (I_nat (i + 1)))
                         end
      | x => x
      end
  .

  Definition hide (l : idx) (t : ccs) : ccs :=
    translate (@hide' l ccsE) t.

  (* Choose operator, where n is the number of choices. *)
  Definition choose (n : nat) (k : nat -> ccs) : ccs := Vis (Or n) k.

  (* Parallel composition operator (#).

    (#) Follows denotation of CCS parallel composition operator from
        Section 5 Rule IV. (p. 269) of:
        M. Henessy & G. Plotkin, A Term Model for CCS, 1980. *)
  CoFixpoint par (p1 p2 : ccs) : ccs :=
    let par_left (p1 p2 : ccs) : ccs :=
      match p1, p2 with
      | (Vis (Act x) k), _ => Vis (Act x) (fun _ => par (k tt) p2)
      | Vis (Sync a) t1, _ => Vis (Sync a) (fun _ => par (t1 tt) p2)
      | Ret _, _ => Tau p2
      | _, _ => fail
      end
    in let par_right (p1 p2 : ccs) : ccs :=
      match p1, p2 with
      | _, (Vis (Act x) k) => Vis (Act x) (fun _ => par p1 (k tt))
      | _, Vis (Sync a) t1 => Vis (Sync a) (fun _ => par p1 (t1 tt))
      | _, Ret _ => Tau p1
      | _, _ => fail
      end
    in let par_comm (p1 p2 : ccs) : ccs :=
      match p1, p2 with
      | (Vis (Act (@In l1)) k1), (Vis (Act (@Out l2)) k2) =>
        if l1 ≡? l2
        then Vis (Sync l1) (fun _ => par (k1 tt) (k2 tt))
        else fail
      | (Vis (Act (@Out l1)) k1), (Vis (Act (@In l2)) k2) =>
        if l1 ≡? l2
        then Vis (Sync l1) (fun _ => par (k1 tt) (k2 tt))
        else fail
      | _, _ => fail
      end
    in
    match (observe p1), (observe p2) with
    | (VisF (Or n1) k1), (VisF (Or n2) k2) =>
      Vis (Or (n1 + n2 + (n1 * n2))) (fun n0 : nat =>
        if beq_nat n0 n1
        then par_left (k1 n0) p2
        else if beq_nat n0 (n2 + n2)
          then par_right p1 (k2 (n0 - n1))
          else par_comm (k1 ((n0 - n1 - n2) mod n2)) (k2 ((n0 - n1 - n2) / n1)))
    | _, _ => fail
    end
  .

  (** *Shape Invariant

    The tree should alternate in depth starting with a (Vis (Or _) _)
    node, then a non-(Vis (Or _) _) node, and keep alternating until
    it finds a leaf.

    The equational properties of CCS structural congruences state that
    any level of the tree can be defined as a sum. This shape invariant
    is necessary for our parallel composition operator, and we define this
    shape as the canonical shape for our denotation of CCS with ITrees.
  *)

  (* Functorial definition of shape invariant.
    The definition takes two parameters :
    - [b] is a boolean flag indicating whether or not it is currently
      at an [Or] event level of the tree.
    - [inv] is the currently built coinductive relation.
  *)
  Inductive shape_invF (inv : bool -> ccs -> Prop) : bool -> ccs' -> Prop :=
  | ShapeRet :
      shape_invF inv false (RetF tt)
  | ShapeOr k
            (n1 n2 : nat)
            (REL : forall n1, inv false (k n1)):
      shape_invF inv true (VisF (Or n2) k)
  | ShapeActIn a k
              (REL : inv true (k tt)):
      shape_invF inv false (VisF (Act (@In a)) k)
  | ShapeActOut a k
                (REL : inv true (k tt)):
      shape_invF inv false (VisF (Act (@Out a)) k)
  | ShapeSync a k
              (REL : inv true (k tt)):
      shape_invF inv false (VisF (Sync a) k)
  | ShapeFail k:
      shape_invF inv false (VisF Fail k)
  | ShapeTau p
            (REL : inv true p):
      shape_invF inv false (TauF p)
  .

  Hint Constructors shape_invF.

  Definition shape_inv_ inv : bool -> ccs -> Prop :=
    fun b p => shape_invF inv b (observe p).

  (* Proving monotonicity properties for [paco]. *)

  Lemma shape_invF_mono inv inv' b p1
        (IN: shape_invF inv b p1)
        (LE: inv <2= inv'):
    shape_invF inv' b p1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma shape_inv__mono : monotone2 (shape_inv_).
  Proof. do 2 red. intros. eapply shape_invF_mono; eauto. Qed.

  Hint Resolve shape_inv__mono : paco.

  Definition shape_inv (p : ccs) : Prop := paco2 shape_inv_ bot2 true p.

  Instance proper_par_eqit :
    Proper (eq_itree eq ==> eq_itree eq ==> eq_itree eq) par.
  Proof.
    repeat intro.
    apply bisimulation_is_eq in H.
    apply bisimulation_is_eq in H0.
    rewrite H, H0. reflexivity.
  Qed.

  Instance shape_inv_par_eqit : Proper (eq_itree eq ==> iff) shape_inv.
  Proof.
    repeat intro.
    apply bisimulation_is_eq in H.
    rewrite H. reflexivity.
  Qed.

  Ltac bubble_types :=
    repeat (match goal with
            | h: ?T |- _ =>
              lazymatch type of h with
              | nat => fail
              | _ => revert h
              end
            end).
  Ltac bubble_types2 :=
    repeat (match goal with
            | h: ?T |- _ =>
              lazymatch type of h with
              | nat -> itree ccsE unit => fail
              | _ => revert h
              end
            end).

  Theorem par_preserves_shape :
    forall (p1 p2 : ccs),
      shape_inv p1 -> shape_inv p2 -> shape_inv (par p1 p2).
  Proof.
    intros p1 p2.
    setoid_rewrite (itree_eta p1).
    setoid_rewrite (itree_eta p2).
    generalize dependent p1. generalize dependent p2.
    pcofix CIH. unfold shape_inv in CIH.
    pstep.
    unfold shape_inv_ in *. intros p2 p1.
    destruct (observe p1) eqn: Heqp1; intros H H0;
      punfold H; punfold H0.
    - (* Ret *)
      destruct (observe p2); inversion H; subst.
    - (* Tau *)
      destruct (observe p2); inversion H; subst.
    - (* Vis *)
      destruct (observe p2) eqn: Heqp2; inversion H;
        inversion H0.
      (* par (Vis e k, Vis e0 k0) *)
      dependent destruction H2.
      dependent destruction H6.
      dependent destruction H7.
      bubble_types; intros. bubble_types2; intros.
      cbn; econstructor; eauto; left; pstep.
      simpl.
      destruct (n4 =? n2).
      + (* Left reduce par *)
        match goal with
          |- shape_invF _ _ (?cont) => remember cont as k2
        end.
        destruct k2 eqn: Hk2.
        * (* RetF *)
          destruct r0; constructor.
        * (* TauF *)
          destruct (_observe (k n4)) eqn:?;
            setoid_rewrite Heqi in Heqk2; try inversion Heqk2.
          -- constructor. left. eapply paco2_mon. pclearbot.
            pstep. unfold shape_inv_ in H0. apply H0.
            intros. inversion PR.
          -- destruct e; inversion Heqk2.
        * (* VisF *)
          destruct (_observe (k n4)) eqn:Heqi;
          setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
          rewrite Heqk2.
          -- constructor.
          -- destruct e0 eqn: He0; try constructor.
             ++ destruct l; econstructor; subst;
                  try (right; setoid_rewrite (itree_eta_ (k3 tt));
                       setoid_rewrite (itree_eta_ (Vis (Or n3) k0)); apply CIH).
                ** pstep. destruct (REL n4).
                   --- punfold H1. unfold shape_inv_ in H1.
                       unfold observe in H1. rewrite Heqi in H1.
                       inversion H1.
                       dependent destruction H5.
                       setoid_rewrite <- (itree_eta_ (k3 tt)).
                       destruct REL1.
                       +++ punfold H3.
                       +++ inversion H3.
                   --- inversion H1.
                ** pstep. destruct (REL n4).
                   --- punfold H1.
                   --- inversion H1.
                ** pstep. destruct (REL n4).
                   --- punfold H1. unfold shape_inv_ in H1.
                       unfold observe in H1. rewrite Heqi in H1.
                       inversion H1.
                       dependent destruction H5.
                       setoid_rewrite <- (itree_eta_ (k3 tt)).
                       destruct REL1.
                       +++ punfold H3.
                       +++ inversion H3.
                   --- inversion H1.
                ** pstep. destruct (REL n4).
                   --- punfold H1.
                   --- inversion H1.
             ++ destruct i.
                ** right.
                   setoid_rewrite (itree_eta_ (k3 tt));
                     setoid_rewrite (itree_eta_ (Vis (Or n3) k0));
                     apply CIH.
                   --- pstep. destruct (REL n4).
                       +++ punfold H1. unfold shape_inv_ in H1.
                           unfold observe in H1. rewrite Heqi in H1.
                           inversion H1.
                           dependent destruction H5.
                           setoid_rewrite <- (itree_eta_ (k3 tt)).
                           destruct REL1.
                           *** punfold H3.
                           *** inversion H3.
                       +++ inversion H1.
                   --- pstep. destruct (REL n4).
                       +++ punfold H1.
                       +++ inversion H1.
                ** right.
                   setoid_rewrite (itree_eta_ (k3 tt));
                     setoid_rewrite (itree_eta_ (Vis (Or n3) k0));
                     apply CIH.
                   --- pstep. destruct (REL n4).
                       +++ punfold H1. unfold shape_inv_ in H1.
                           unfold observe in H1. rewrite Heqi in H1.
                           inversion H1.
                           dependent destruction H5.
                           setoid_rewrite <- (itree_eta_ (k3 tt)).
                           destruct REL1.
                           *** punfold H3.
                           *** inversion H3.
                       +++ inversion H1.
                   --- pstep. destruct (REL n4).
                       +++ punfold H1.
                       +++ inversion H1.
      + (* Right & Comm *)
        destruct (n4 =? n3 + n3).
        * (* Right. This proof is symmetric with Left. *)
          match goal with
            |- shape_invF _ _ (?cont) => remember cont as k2
          end.
          destruct k2 eqn: Hk2.
          -- (* RetF *)
            destruct r0; constructor.
          -- (* TauF *)
            destruct (_observe (k0 (n4 - n2))) eqn:?;
                    setoid_rewrite Heqi in Heqk2; try inversion Heqk2.
            ++ constructor. left. eapply paco2_mon. pstep.
              unfold shape_inv_ in H. apply H. intros.
              inversion PR.
            ++ destruct e; inversion Heqk2.
          -- (* VisF *)
            destruct (_observe (k0 (n4 - n2))) eqn: Heqi;
              setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
                rewrite Heqk2.
            ++ constructor.
            ++ destruct e0 eqn: He0; try constructor;
                 try destruct l.
               ** econstructor; subst;
                  try (right; setoid_rewrite (itree_eta_ (k3 tt));
                       setoid_rewrite (itree_eta_ (Vis (Or n2) k)); apply CIH);
                  try (pstep; apply H); destruct (REL0 (n4 - n2)).
                  --- punfold H1. unfold shape_inv_ in H1.
                      unfold observe in H1.
                      rewrite Heqi in H1. inversion H1.
                      dependent destruction H5.
                      setoid_rewrite <- (itree_eta_ (k3 tt)).
                      destruct REL1. apply H3.
                      inversion H3.
                  --- inversion H1.
               ** econstructor; subst.
                  right; setoid_rewrite (itree_eta_ (k3 tt)).
                  setoid_rewrite (itree_eta_ (Vis (Or n2) k)); apply CIH.
                  --- pstep. apply H.
                  --- destruct (REL0 (n4 - n2)).
                      +++ punfold H1. unfold shape_inv_ in H1.
                          unfold observe in H1.
                          rewrite Heqi in H1. inversion H1.
                          dependent destruction H5.
                          setoid_rewrite <- (itree_eta_ (k3 tt)).
                          destruct REL1. apply H3.
                          inversion H3.
                      +++ inversion H1.
               ** destruct i.
                  --- right. setoid_rewrite (itree_eta_ (k3 tt)).
                      setoid_rewrite (itree_eta_ (Vis (Or n2) k)).
                      apply CIH.
                      +++ pstep. apply H.
                      +++ destruct (REL0 (n4 - n2)).
                          *** punfold H1. unfold shape_inv_ in H1.
                              unfold observe in H1.
                              rewrite Heqi in H1. inversion H1.
                              dependent destruction H5.
                              setoid_rewrite <- (itree_eta_ (k3 tt)).
                              destruct REL1. apply H3.
                              inversion H3.
                          *** inversion H1.
                  --- right. setoid_rewrite (itree_eta_ (k3 tt)).
                      setoid_rewrite (itree_eta_ (Vis (Or n2) k)).
                      apply CIH.
                      +++ pstep. apply H.
                      +++ destruct (REL0 (n4 - n2)).
                          *** punfold H1. unfold shape_inv_ in H1.
                              unfold observe in H1.
                              rewrite Heqi in H1. inversion H1.
                              dependent destruction H5.
                              setoid_rewrite <- (itree_eta_ (k3 tt)).
                              destruct REL1. apply H3.
                              inversion H3.
                          *** inversion H1.
        * (* Comm *)
          match goal with
            |- shape_invF _ _ (?cont) => remember cont as k2
          end.
          destruct k2 eqn: Hk2.
          -- destruct r0; constructor.
          -- destruct (_observe (k ((n4 - n2 - n3) mod n3))) eqn:?;
              setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
              rewrite Heqk2;
             destruct e; try inversion H2; clear H2; clear H3;
             destruct l;
               destruct (_observe (k0 ((n4 - n2 - n3) / n2))) eqn:?;
                        setoid_rewrite Heqi0 in Heqk2; try inversion Heqk2;
                 rewrite Heqk2;
                 destruct e; try inversion H2; clear H2;
                   destruct l0; try inversion Heqk2;
                     destruct (l ≡? l0); inversion Heqk2.
          -- destruct (_observe (k ((n4 - n2 - n3) mod n3))) eqn:?;
              setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
              rewrite Heqk2.
            ++ destruct r0; constructor.
            ++ constructor.
            ++ clear H2. destruct e0.
                ** constructor.
                ** destruct l;destruct (_observe (k0 ((n4 - n2 - n3) / n2))) eqn:?;
                         setoid_rewrite Heqi0 in Heqk2; setoid_rewrite Heqi0;
                           try (inversion Heqk2; dependent destruction H3;
                                dependent destruction H4; constructor);
                           try constructor; destruct e0; try constructor;
                             destruct l0; try constructor;
                               destruct (l ≡? l0).
                   +++ inversion Heqk2.
                      dependent destruction H3.
                      dependent destruction H4.
                      constructor.
                      setoid_rewrite (itree_eta_ (k3 tt)).
                      setoid_rewrite (itree_eta_ (k4 tt)). right.
                      apply CIH.
                      *** destruct (REL ((n4 - n2 - n3) mod n3)).
                          ---- punfold H1. unfold shape_inv_ in H1.
                              unfold observe in H1.
                              rewrite Heqi in H1. inversion H1.
                              dependent destruction H4.
                              setoid_rewrite <- (itree_eta_ (k3 tt)).
                              destruct REL1. apply H2. inversion H2.
                         ---- inversion H1.
                      *** destruct (REL0 ((n4 - n2 - n3) / n2)).
                         ---- punfold H1. unfold shape_inv_ in H1.
                              unfold observe in H1.
                              rewrite Heqi0 in H1. inversion H1.
                              dependent destruction H4.
                              setoid_rewrite <- (itree_eta_ (k4 tt)).
                              destruct REL1. apply H2. inversion H2.
                         ---- inversion H1.
                   +++ constructor.
                   +++ constructor. right.
                       setoid_rewrite (itree_eta_ (k3 tt)).
                       setoid_rewrite (itree_eta_ (k4 tt)).
                       apply CIH.
                       *** destruct (REL ((n4 - n2 - n3) mod n3)).
                           ---- punfold H1. unfold shape_inv_ in H1.
                                unfold observe in H1.
                                rewrite Heqi in H1. inversion H1.
                                dependent destruction H4.
                                setoid_rewrite <- (itree_eta_ (k3 tt)).
                                destruct REL1.
                                ++++ apply H2.
                                ++++ inversion H2.
                           ---- inversion H1.
                       *** destruct (REL0 ((n4 - n2 - n3) / n2)).
                           ---- punfold H1. unfold shape_inv_ in H1.
                               unfold observe in H1.
                               rewrite Heqi0 in H1. inversion H1.
                               dependent destruction H4.
                               setoid_rewrite <- (itree_eta_ (k4 tt)).
                               destruct REL1.
                               ++++ apply H2.
                               ++++ inversion H2.
                           ---- inversion H1.
                   +++ constructor.
                ** constructor.
                ** constructor.
  Qed.

  Eval cbv in fun (a : idx) => ret_traces
    (par (Vis (Or 2) (fun n => if beq_nat n 1 then zero else send a zero))
    (Vis (Or 2) (fun n => if beq_nat n 1 then zero else recv a zero))).

  (* Bang operator. *)
  Inductive bangF bang : ccs -> ccs -> Prop :=
  | _bangF : forall c1 c2 (R : bang c1 c2 : Prop),
      bangF bang c1 (par c1 c2)
  .

  Hint Constructors bangF.

  Definition bang_ bang : ccs -> ccs -> Prop :=
    fun c1 c2 => bangF bang c1 c2.

  Definition bang' (p1 p2 : ccs) := paco2 bang_ bot2 p1 p2.

  Definition bang (p1 p2 : ccs) (R : bang' p1 p2) := par p1 p2.

End ccs_combinators.


(* To show correctness of our denotation of CCS, we compare
   the trace semantics between this denotation and the
   operational semantics for CCS. *)

Section lts.

  (** *Operational Semantics for CCS, the Labeled Transition System (lts) *)
  Inductive lts : Type :=
  | Done : lts
  | Action : Label -> lts -> lts
  | Choice : lts -> lts -> lts
  | Par : lts -> lts -> lts
  | Hide : Label -> lts -> lts
  | Bang : lts -> lts
  .

  (** *Synchronous Model of Operational CCS

    In order to get a trace semantics, we need to limit our operational
    semantics to a _synchronous_ model. A synchronous model is where
    the observable events are only on the synchronous actions of the
    transition system. This is desirable because we need a set of
    sequentially observable events which agree to our denotation
    of the CCS. Note that our `par` definition follows a synchronous
    version of the CCS. (i.e. a.b.0 <> b.a.0. In asynchronous CCS,
    a.b.0 = b.a.0, since it needs to consider all the possible interleavings
    of actions.) This motivates our want for a synchronous CCS, where
    traces of operations only contain synchronous events. This is nice also
    because it provides a more stable basis for our future direction of
    extend our denotation to message passing models of concurrency
    (e.g. π-calculus).
  *)

  (* Operational semantics for Labeled Transition System.

    Transition Rules found in p.39 of
    R. Milner, Communicating and Mobile Systems: The π-calculus.  *)
  Inductive aux_step : option Label -> lts -> lts -> Prop :=
  | aux_step_Send l t :
      aux_step (Some (@In l)) (Action (@In l) t) t
  | aux_step_Recv l t :
      aux_step (Some (@Out l)) (Action (@Out l) t) t
  .

  Inductive sync_step : option Label -> lts -> lts -> Prop :=
  | sync_step_Choice_L a u v u':
      aux_step (Some a) u u' ->
      sync_step (Some a) (Choice u v) u'
  | sync_step_Choice_R a u v v' :
      aux_step (Some a) v v' ->
      sync_step (Some a) (Choice u v) v'
  | sync_step_Par_L u v u' (A' : option Label) :
      sync_step A' u u' -> sync_step A' (Par u v) (Par u' v)
  | sync_step_Par_R u v v' (A' : option Label) :
      sync_step A' v v' -> sync_step A' (Par u v) (Par u v')
  | sync_step_Par_Comm1 l u v u' v' :
      aux_step (Some (@In l)) u u' ->
      aux_step (Some (@Out l)) v v' ->
      sync_step None (Par u v) (Par u' v')
  | sync_step_Par_Comm2 l u v u' v' :
      aux_step (Some (@Out l)) u u' ->
      aux_step (Some (@In l)) v v' ->
      sync_step None (Par u v) (Par u' v')
  | sync_step_Hide_In l u u' :
      sync_step (Some (@In l)) u u' ->
      sync_step (Some (@In l)) (Hide (@In l) u) (Hide (@In l) u')
  | sync_step_Hide_Out l u u' :
      sync_step (Some (@Out l)) u u' ->
      sync_step (Some (@Out l)) (Hide (@Out l) u) (Hide (@Out l) u')
  | sync_step_Bang u u' (A' : option Label) :
      sync_step A' (Par u (Bang u)) u' -> sync_step A' (Bang u) u'
  .

End ccs_op.

(** *Trace Semantics
  The trace semantics for a small-step semantics is the reflexive transitive
  closure of the step relation. *)

Inductive lts_trace : lts -> list (option Label) -> lts -> Prop :=
| lts_trace_refl : forall (p : lts), lts_trace p [] p
| lts_trace_step : forall (p1 p2 p3 : lts) l a,
    lts_trace p2 l p3 ->
    sync_step a p1 p2 ->
    lts_trace p1 (a :: l) p3
.

Lemma lts_trace_app :
  forall (p1 p2 p3 : ccs_) l1 l2,
    lts_trace p1 l1 p2 -> lts_trace p2 l2 p3 ->
    lts_trace p1 (l1 ++ l2) p3.
Proof.
  intros. induction H.
  - cbn; eauto.
  - apply IHis_trace_ in H0.
    eapply is_trace_step. apply H0. apply H1.
Qed.

Lemma lts_trace_inversion (a : option Label) :
  forall (p1 p2 : ccs_) l,
    lts_trace p1 l p2 ->
    (l = [] /\ p1 = p2) \/ (l = [a] /\ sync_step a p1 p2) \/
    (exists l1 l2 p', l = l1 ++ l2 /\ lts_trace p1 l1 p' /\ lts_trace p' l2 p2).
Proof.
  induction p1; intros; inversion H; subst;
    try (left; split; reflexivity);
    try (right; right; exists [a0]).
  - exists l0. exists p0. split. reflexivity.
    split. repeat (econstructor; eauto). auto.
  - exists l1. exists p3. split. reflexivity.
    split. econstructor. econstructor.
    apply H1. apply H0.
  - exists l0. exists p0. split. reflexivity.
    split. econstructor. econstructor.
    apply H1. apply H0.
  - exists l0. exists p0. split. reflexivity.
    split. econstructor. econstructor.
    apply H1. apply H0.
  - exists l1. exists p3. split. reflexivity.
    split. econstructor. econstructor.
    apply H1. apply H0.
  - exists l0. exists p3. split. reflexivity.
    split. econstructor. econstructor.
    apply H1. apply H0.
Qed.

Lemma lts_trace_par (a : option Label) :
  forall (p1 p2 p1' p2' : lts) a1 a2,
    lts_trace p1 [a1] p1' -> lts_trace p2 [a2] p2' ->
    lts_trace (Par p1 p2) [a2; a1] (Par p1' p2').
Proof.
  intros. econstructor.
  econstructor. econstructor. econstructor.
  inversion H; subst. inversion H4; subst.
  apply H6. econstructor. inversion H0; subst.
  inversion H4; subst. apply H6.
Qed.

Lemma lts_trace_par_left :
  forall p1 p1' l1 p2,
    lts_trace p1 l1 p1' ->
    lts_trace (Par p1 p2) l1 (Par p1' p2).
Proof.
  intros. induction H; subst.
  - constructor.
  - econstructor. apply IHis_trace_.
    constructor. apply H0.
Qed.

Lemma lts_trace_par_acc_nonsync :
  forall (p1 p2 p1' p2' : ccs_) l1 l2,
    lts_trace p1 l1 p1' -> lts_trace p2 l2 p2' ->
    lts_trace_ (Par p1 p2) (l2 ++ l1) (Par p1' p2').
Proof.
  intros. induction H0.
  - simpl. inversion H; subst.
    + constructor.
    + econstructor. apply lts_trace_par_left. eauto.
      constructor. apply H1.
  - simpl. econstructor. apply IHis_trace_.
    constructor. apply H1.
Qed.

Lemma lts_trace_par_sync :
  forall (p1 p2 p1' p2' p1'' p2'': lts) a l1 l2,
    lts_trace p1' l1 p1'' -> lts_trace p2' l2 p2'' ->
    aux_step (Some (@In a)) p1 p1' -> aux_step (Some (@Out a)) p2 p2' ->
    lts_trace (Par p1 p2) (None::(l2 ++ l1)) (Par p1'' p2'').
Proof.
  intros.
  assert (is_trace_ (Par p1 p2) [None] (Par p1' p2')).
  { econstructor. econstructor. econstructor; eauto. }
  pose proof lts_trace_step.
  apply lts_trace_step with (p2 := (Par p1' p2')).
  apply lts_trace_par_acc_nonsync; eauto.
  econstructor; eauto.
Qed.

(** *Equivalence on Traces

    We defined the trace semantics for our operational semantics above, and
    there is a trace semantics defined for ITrees (in theories.Interp.Traces).

    To show equivalence between these traces, we need to first show
    an equivalence relation between our varying notion of traces.
*)

Arguments trace _ _.

Inductive equiv_traces : @trace ccsE unit -> list (option Label) -> Prop :=
| TEqNil : equiv_traces TEnd []
| TEqRet x : equiv_traces (TRet x) []
| TEqEvEndAct a :
    equiv_traces (TEventEnd (Act a)) [Some a]
| TEqEvEndSync x :
    equiv_traces (TEventEnd (Sync x)) [None]
| TEqEvEndFail :
    equiv_traces (TEventEnd (Fail)) []
| TEqEvEndOr n : (* Waiting for non-deterministic Choice *)
    equiv_traces (TEventEnd (Or n)) []
| TEqEvRespAct (a : Label) t l :
    equiv_traces t l ->
    equiv_traces (TEventResponse (Act a) tt t) ((Some a)::l)
| TEqEvRespSync x t l :
    equiv_traces t l ->
    equiv_traces (TEventResponse (Sync x) tt t) ((None)::l)
| TEqEvRespFail t {x : void} :
    equiv_traces (@TEventResponse ccsE unit void (Fail) x t) []
| TEqEvRespOr n1 n2 t l a u u' v :
    equiv_traces t l ->
    is_trace_ (Choice u v) (a::l) u' ->
    equiv_traces (@TEventResponse ccsE unit nat (Or n1) n2 t) (a::l)
.

Ltac exists_trace_done := exists []; exists Done; exists Done; split; constructor.

Ltac repeat_constructors :=
  split; repeat econstructor; repeat econstructor; constructor.

(* Now we can prove trace equivalence between the semantic models. *)
Theorem trace_eq_ob_den (a : idx) (l : list idx):
  (forall c1 tr, is_trace c1 tr ->
             exists tr' c1' c2',
               lts_trace c1' tr' c2' /\
               equiv_traces tr tr')
  /\ (forall c1' c2' tr', lts_trace c1' tr' c2' ->
                    exists tr c1,
                      is_trace c1 tr /\
                      equiv_traces tr tr').
Proof.
  split.
  - (* Denotational trace => Operational trace *)
    intros. induction H.
    + (* TraceEmpty *)
      exists_trace_done.
    + (* TraceRet *)
      exists_trace_done.
    + (* TraceTau *)
      destruct (observe t); assumption.
    + (* TraceVisEnd *)
      destruct e.
      * (* Or n0 *)
        exists []; exists (Choice Done Done); exists (Choice Done Done);
          repeat_constructors.
      * (* Act l0 *)
        exists [Some l0]; exists (Choice (Action l0 Done) Done); exists Done.
        destruct l0; repeat_constructors.
      * (* Sync a0 *)
        exists [None];
          exists (Par (Action (@In (hd a l)) Done) (Action (@Out (hd a l)) Done));
          exists (Par Done Done); repeat_constructors.
      * (* Fail *)
        exists_trace_done.
    + (* TraceVisContinue *)
      destruct e.
      * (* Or n0 *)
        destruct IHis_traceF.
        destruct H0 as [? [?]]. destruct H0.
        exists ((Some (@In (hd a l)))::x0);
          exists (Choice (Action (@In (hd a l)) x1) x1); exists x2.
        split. econstructor. apply H0. constructor. econstructor.
        econstructor. apply H1. econstructor. apply H0. constructor.
        constructor.
      * (* Act l0 *)
        destruct IHis_traceF.
        destruct H0 as [? [?]]. destruct H0.
        exists (Some l0::x0); exists (Choice (Action l0 x1) x1); exists x2.
        destruct l0.
        -- split.
           ++ econstructor. apply H0. repeat constructor.
           ++ destruct x. econstructor. apply H1.
        -- split.
           ++ econstructor. apply H0. repeat constructor.
           ++ destruct x. econstructor. apply H1.
      * (* Sync a0 *)
        destruct IHis_traceF.
        destruct H0 as [? [?]]. destruct H0.
        exists (None::(x0)).
        exists (Par (Action (@In (hd a l)) x1) (Action (@Out (hd a l)) x2)).
        exists (Par x2 x2). split.
        -- assert (None :: x0 = [None] ++ x0).
           { reflexivity. }
           rewrite H2.
           eapply is_trace_par_sync. eauto.
           constructor. constructor. econstructor.
        -- destruct x. econstructor. eauto. Unshelve. eauto.
      * (* Fail *)
        destruct IHis_traceF.
        destruct H0 as [? [?]]. destruct H0.
        exists_trace_done.
  - (* Operational trace => Denotational trace *)
    intros. induction H.
    + exists TEnd. exists zero. split; constructor.
    + destruct a0.
      destruct IHis_trace_ as [? [?]].
      destruct H1; unfold is_trace in H1.
      * exists (@TEventResponse ccsE unit unit (Act l1) tt x).
        exists (Vis (Act l1) (fun _ => x0)).
        split; constructor; assumption.
      * destruct IHis_trace_ as [? [?]]. destruct H1.
        exists (@TEventResponse ccsE unit unit (Sync a) tt x).
        exists (Vis (Sync a) (fun _ => x0)).
        split; constructor; assumption.
Qed.
