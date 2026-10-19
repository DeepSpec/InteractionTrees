From Coinduction Require Import all. (* import for CompleteLattice instances; Preorder's leq is re-imported below via Labels and wins as the unqualified name *)
From Stdlib Require Import Morphisms PeanoNat. 


From ITree Require Import
     Basics.Utils
     Axioms
     ITree
     ITreeFacts
.

From ITree.Extra Require Export Secure.Labels.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(* will need more propositional constraints on Preorders *)

Section SecureUntimed.
  Context {E : Type -> Type} {R1 R2 : Type}.
  Context (Label : Preorder).
  Context (priv : forall A, E A -> L).
  Context (RR : R1 -> R2 -> Prop).

  Coercion is_true : bool >-> Sortclass.
  Inductive secure_eqitF (b1 b2 : bool) (l : L) (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=

    (* eqitF constructors *)
    | secEqRet r1 r2 : RR r1 r2 -> secure_eqitF b1 b2 l sim (RetF r1) (RetF r2)
    | secEqTau t1 t2 : sim t1 t2 -> secure_eqitF b1 b2 l sim (TauF t1) (TauF t2)
    | secEqTauL t1 ot2 (CHECK : b1) : secure_eqitF b1 b2 l sim (observe t1) ot2 -> secure_eqitF b1 b2 l sim (TauF t1) ot2
    | secEqTauR ot1 t2 (CHECK : b2) : secure_eqitF b1 b2 l sim ot1 (observe t2) -> secure_eqitF b1 b2 l sim ot1 (TauF t2)
    (* info_flow protecting coinductive constructors *)
    | EqVisPriv {A} (e : E A) k1 k2 (SECCHECK : leq (priv A e) l) :
        ((forall a, sim (k1 a) (k2 a) : Prop)) -> secure_eqitF b1 b2 l sim (VisF e k1) (VisF e k2)
    | EqVisUnPrivTauLCo {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, sim (k1 a) t2) -> secure_eqitF b1 b2 l sim (VisF e k1) (TauF t2)
    | EqVisUnPrivTauRCo {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, sim t1 (k2 a)) -> secure_eqitF b1 b2 l sim (TauF t1) (VisF e k2)
    | EqVisUnPrivVisCo {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
        (SIZECHECK1 : nonempty A ) (SIZECHECK2 : nonempty B) :
        (forall a b, sim (k1 a) (k2 b)) -> secure_eqitF b1 b2 l sim (VisF e1 k1) (VisF e2 k2)
    (* info_flow protecting inductive constructors *)
    | EqVisUnPrivLInd {A} (e : E A) k1 t2 (CHECK : b1) (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, secure_eqitF b1 b2 l sim (observe (k1 a)) (observe t2) ) ->
        secure_eqitF b1 b2 l sim (VisF e k1) (observe t2)
    | EqVisUnPrivRInd {A} (e : E A) t1 k2 (CHECK : b2) (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, secure_eqitF b1 b2 l sim (observe t1) (observe (k2 a) )) ->
        secure_eqitF b1 b2 l sim (observe t1) (VisF e k2)
    (* info_flow protecting constructors for halting events, should capture the notion that a secret halt means
       that either it halted or it is performing some secret or silent computation and you can't tell which *)
    | EqVisUnprivHaltLTauR {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l ) (SIZECHECK : empty A) :
        sim (Vis e k1) t2 -> secure_eqitF b1 b2 l sim (VisF e k1) (TauF t2)
    | EqVisUnprivHaltRTauL {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l ) (SIZECHECK : empty A) :
        sim t1 (Vis e k2) -> secure_eqitF b1 b2  l sim (TauF t1) (VisF e k2)
    | EqVisUnprivHaltLVisR {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
            (SIZECHECK : empty A) :
      (forall b, sim (Vis e1 k1) (k2 b) ) -> secure_eqitF b1 b2 l sim (VisF e1 k1) (VisF e2 k2)
    | EqVisUnprivHaltRVisL {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
            (SIZECHECK : empty B) :
        (forall a, sim (k1 a) (Vis e2 k2)) -> secure_eqitF b1 b2 l sim (VisF e1 k1) (VisF e2 k2)
  .

  Hint Constructors secure_eqitF : itree.

  Definition secure_eqit_ (b1 b2 : bool) (l : L) (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => secure_eqitF b1 b2 l sim (observe t1) (observe t2).

  Hint Unfold secure_eqit_ : itree.


Lemma secure_eqitF_mono b1 b2 l :
  Proper (respectful Coinduction.lattice.leq Coinduction.lattice.leq) 
    (secure_eqit_ b1 b2 l).
  Proof.
    intros!. red; red in H0. 
    induction H0; try solve [constructor; intros; eauto with itree; now apply H].
  Qed.

  Definition secure_eqit_mon b1 b2 l := Build_mon (secure_eqitF_mono b1 b2 l).

  Definition eqit_secure b1 b2 l := gfp (secure_eqit_mon b1 b2 l).

  (*
    Note that this is not reflexive (think it is symmetric and transitive)
    Suppose SecureFlip : E bool has privilege 1 and trigger SecureFlip is
    observed at privilege 0. We end to prove eqit_secure false false 0 of it
    requires us to show forall a b, eqit_secure false false 0 (Ret a) (Ret b)
    this is false, suppose a = true and b = false and the relation is equality

   *)


End SecureUntimed.

#[global] Hint Constructors secure_eqitF : itree.

Definition NatPreorder : Preorder :=
  {|
  L := nat;
  leq := fun n m => Nat.le n m
  |}.

Ltac unpriv_co := try apply EqVisUnPrivVisCo;
                  try apply EqVisUnPrivTauLCo;
                  try apply EqVisUnPrivTauRCo;
                  auto with itree; intros.

Ltac unpriv_ind := try apply EqVisUnPrivLInd;
                   try apply EqVisUnPrivRInd;
                   auto with itree; intros.

Ltac unpriv_halt :=
  match goal with
  | [  Hemp : empty ?A |- secure_eqitF _ _ _ _ _ _ _ (@VisF _ _ _ ?A _ _) _ ] =>
    try apply EqVisUnprivHaltLTauR; try apply EqVisUnprivHaltLVisR; auto with itree; intros

  | [  Hemp : empty ?A |- secure_eqitF _ _ _ _ _ _ _ _ (@VisF _ _ _ ?A _ _)  ] =>
    try apply EqVisUnprivHaltRTauL; try apply EqVisUnprivHaltRVisL; auto with itree; intros end.

Section SecureUntimedUnReflexive.

Section eqit_secureC.
  (* might not be the order I eventually want but whatever*)
  Context {E: Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  Context (Label : Preorder) (priv : forall A, E A -> L) (l : L).

(* Lemma eqit_secure_trans b1 b1' b2 b2' r t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit_secure Label priv RR1 b1 b1' l t1 t1')
      (EQVr: eqit_secure Label priv RR2 b2 b2' l t2 t2')
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      eqit_secure Label priv RR b1 b2' l t1 t2.



  Variant eqit_secure_trans_clo (b1 b2 b1' b2' : bool) (r : itree E R1 -> itree E R2 -> Prop) :
    itree E R1 -> itree E R2 -> Prop :=
        eqit_secure_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit_secure Label priv RR1 b1 b1' l t1 t1')
      (EQVr: eqit_secure Label priv RR2 b2 b2' l t2 t2')
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      eqit_secure_trans_clo b1 b2 b1' b2' r t1 t2.

  Hint Constructors eqit_secure_trans_clo : itree.

  Definition eqit_secureC b1 b2 := eqit_secure_trans_clo b1 b2 false false.
  Hint Unfold eqit_secureC : itree.

  Lemma eqit_secureC_mon b1 b2 r1 r2 t1 t2
    (IN : eqit_secureC b1 b2 r1 t1 t2)
    (LE: r1 <2= r2) :
    eqit_secureC b1 b2 r2 t1 t2.
  Proof.
    destruct IN; eauto with itree.
  Qed. *)

End eqit_secureC.


(* TOUR: This proof *)
Lemma eqit_secure_sym : forall b1 b2 E R1 R2 RR Label priv l (t1 : itree E R1) (t2 : itree E R2),
    eqit_secure Label priv RR b1 b2 l t1 t2 -> eqit_secure Label priv (Basics.flip RR) b2 b1 l t2 t1.
Proof.
  intros b1 b2 E R1 R2 RR Label priv l. icoinduction c CIH.
  intros t1 t2 Hsec. step in Hsec.
  hinduction Hsec before c; intros; eauto with itree; 
  try (unpriv_co; apply CIH; apply H);
  try unpriv_halt.
  - constructor; auto with itree. intros. apply CIH; apply H.
  - eapply CIH. apply H. 
  - eapply CIH. apply H. 
Qed. 

Lemma secure_eqit_mono : forall E (b1 b2 b3 b4 : bool) R1 R2 RR1 RR2 Label priv l
      (t1 : itree E R1) (t2 : itree E R2),
    (b1 -> b3) -> (b2 -> b4) -> (RR1 <= RR2) ->
    eqit_secure Label priv RR1 b1 b2 l t1 t2 -> eqit_secure Label priv RR2 b3 b4 l t1 t2.
Proof.
  intros. generalize dependent t2. revert t1. coinduction c CIH.
  intros t1 t2 Ht12. icbn. 
  step in Ht12.
  hinduction Ht12 before l; intros; 
  try (unpriv_co; apply CIH; try red; eauto; fail);
  try (unpriv_halt; try contra_size; apply CIH; try red; eauto; fail); 
  eauto with itree. 
  - constructor; auto. now apply H2. 
  - constructor; intros; eauto. eapply CIH. apply H. 
Qed.

End SecureUntimedUnReflexive.
