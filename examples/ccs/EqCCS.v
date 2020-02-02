From ITree Require Import
     ITree
     ITreeDefinition
     Interp.Traces
     Eq
.

Require Import PeanoNat.

Require Import DenoteCCS.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(** *Equational Laws of CCS

    Based on the following text:
    [1] R. Milner., Communicating and Mobile Systems: the π-Calculus. *)

(* begin hide *)
Bind Scope ccs_scope with ccs.
Delimit Scope ccs_scope with ccs.
Local Open Scope ccs_scope.

(* end hide *)

(** *Strong Bisimulation *)

(** *Weak Bisimulation Equational Properties
   Some equational properties of weak bisimulation in CCS.
   From Chapter 6, [1]. *)
Inductive ccs_weak_eqR : ccs -> ccs -> Prop :=
| EqSync l1 p1 p2:
    ccs_weak_eqR (Vis (Sync l1) (fun _ => p1)) p2
| EqChoiceSync n1 n2 l1 (k1 k2: nat -> ccs):
    ccs_weak_eqR (Vis (Or 3)
                     (fun n => if n =? 0 then (Vis (Or n1) k1)
                            else if n =? 1 then (Vis (Or n2) k2)
                                 else (Vis (Sync l1) (fun _ => Vis (Or n2) k2))))
                (Vis (Or 2)
                     (fun n => if n =? 0 then (Vis (Or n1) k1)
                            else (Vis (Sync l1) (fun _ => Vis (Or n2) k2))))
| EqChoiceAct n1 n2 i1 l1 k1 k2 k3:
    ccs_weak_eqR (Vis (Or 3)
                     (fun n => if n =? 0 then (Vis (Or n1) k1)
                            else if n =? 1 then (Vis (Act i1) k2)
                                 else (Vis (Act i1)
                                           (fun _ => Vis (Or 2)
                                                      (fun n => if n =? 0 then
                                                               (Vis (Sync l1) k2)
                                                             else
                                                               (Vis (Or n2) k3))))))
                (Vis (Or 3)
                     (fun n => if n =? 0 then (Vis (Or n1) k1)
                            else (Vis (Act i1)
                                           (fun _ => Vis (Or 2)
                                                      (fun n => if n =? 0 then
                                                               (Vis (Sync l1) k2)
                                                             else
                                                               (Vis (Or n2) k3))))))
.

(** *Weak Bisimulation of CCS

    An attempt to define weak bisimulation of CCS by combining equational laws
    of weak bisimulation and the `eutt` relation intrinsic to ITrees.

    Note that neither heterogeneous bisimulation or weak bisimulation can properly
    capture the weak bisimulation in CCS.

    The weak bisimulation in ITrees capture the coinductive reasoning structure,
    but is unable to handle the bisimulation encoded in the denotational calculi
    that may be modeled by ITrees.
    This is especially tricky because a bisimulation relation is typically
    defined under an operational semantics, where the observed action of a system
    simulates another operationally.

    TODO: 
    One possible direction in extending this is simulation relation is by thinking
    about guarded recursive types.
    See: R.E. Mogelberg, N. Veltri.
         Bisimulation as Path Type for Guarded Recursive Types. [POPL 2018].
 *)
Definition ccs_weak_bisim : ccs -> ccs -> Prop :=
  fun p1 p2 => eutt (fun _ _ => true) p1 p2 /\ ccs_weak_eqR p1 p2.

(** *Process Congruence
   Definition 4.5 Process Congruence. [1] Basically contextual equivalence. *)
Inductive ccs_proc_cong : ccs -> ccs -> Prop :=
| ActCong p1 p2 n1 k1:
    ccs_proc_cong p1 p2 ->
    ccs_proc_cong (Vis (Or n1) (fun n => if n =? 0 then p1 else (k1 n)))
              (Vis (Or n1) (fun n => if n =? 0 then p2 else (k1 n)))
| HideCong p1 p2 i1:
    ccs_proc_cong p1 p2 ->
    ccs_proc_cong (hide i1 p1) (hide i1 p2)
| ParLCong p1 p2 p3 :
    ccs_proc_cong p1 p2 ->
    ccs_proc_cong (par p1 p3) (par p2 p3)
| ParRCong p1 p2 p3 :
    ccs_proc_cong p1 p2 ->
    ccs_proc_cong (par p3 p1) (par p3 p1)
.

(* Weak equivalence is a process congruence. *)
Theorem ccs_weak_proc_cong :
  forall p1 p2, ccs_weak_bisim p1 p2 -> ccs_proc_cong p1 p2.
Proof.
  intros. induction H.
  induction H0.
Admitted.


(* Sanity check equivalences and inequivalences. (p.56 [1]) *)
Theorem ccs_weak_equiv1 :
  forall p1 l1 n1 n2 k1 k2 i1,
    ccs_weak_bisim
      (Vis (Or 3) (fun m => if m =? 0 then (Vis (Or n1) k1)
                         else if m =? 1 then (Vis (Act i1) (fun _ => p1))
                              else
                                (Vis (Sync l1)
                                     (fun _ => (Vis (Or n2) (fun m' => if m' =? 0 then
                                                                   Vis (Act i1) (fun _ => p1) else (k2 m')))))))
      (Vis (Or 2) (fun m => if m =? 0 then (Vis (Or n1) k1)
                         else (Vis (Sync l1) (fun _ => (Vis (Or n2) (fun m' => if m' =? 0 then Vis (Act i1) (fun _ => p1) else (k2 m'))))))).
Proof. Admitted.

Theorem ccs_weak_inequiv1 :
  forall p1 p2 l1,
    not (ccs_weak_bisim
         (Vis (Or 2) (fun n => if n =? 0 then p1 else p2))
         (Vis (Or 2) (fun n => if n =? 0 then p1 else Vis (Sync l1) (fun _ => p2)))).
Proof.
Admitted.

Theorem ccs_weak_inequiv2 :
  forall p1 p2 l1 l2,
    not (ccs_weak_bisim
         (Vis (Or 2) (fun n => if n =? 0 then Vis (Sync l1) (fun _ => p1) else p2))
         (Vis (Or 2)
              (fun n => if n =? 0 then Vis (Sync l1) (fun _ => p1)
                     else Vis (Sync l2) (fun _ => p2)))).
Proof.
Admitted.

(** *Full Abstraction
    A denotational model is *fully abstract* whenever denotational equality
    characterizes contextual equivalence. What does it mean to show full
    abstraction in this CCS model?
 *)
