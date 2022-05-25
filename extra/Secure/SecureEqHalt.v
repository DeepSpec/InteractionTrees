From ITree Require Import
     Basics.Tacs
     Axioms
     ITree
     ITreeFacts
.

From ITree.Extra Require Export Secure.Labels.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac pmonauto_itree :=
  let IN := fresh "IN" in
  try (repeat intro; destruct IN; eauto with paco itree; fail).

(* will need more propositional constraints on Preorders *)

Section SecureUntimed.
  Context {E : Type -> Type} {R1 R2 : Type}.
  Context (Label : Preorder).
  Context (priv : forall A, E A -> L).
  Context (RR : R1 -> R2 -> Prop).

  Coercion is_true : bool >-> Sortclass.
  Inductive secure_eqitF (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=

    (* eqitF constructors *)
    | secEqRet r1 r2 : RR r1 r2 -> secure_eqitF b1 b2 l vclo sim (RetF r1) (RetF r2)
    | secEqTau t1 t2 : sim t1 t2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) (TauF t2)
    | secEqTauL t1 ot2 (CHECK : b1) : secure_eqitF b1 b2 l vclo sim (observe t1) ot2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) ot2
    | secEqTauR ot1 t2 (CHECK : b2) : secure_eqitF b1 b2 l vclo sim ot1 (observe t2) -> secure_eqitF b1 b2 l vclo sim ot1 (TauF t2)
    (* info_flow protecting coinductive constructors *)
    | EqVisPriv {A} (e : E A) k1 k2 (SECCHECK : leq (priv A e) l) :
        ((forall a, vclo sim (k1 a) (k2 a) : Prop)) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (VisF e k2)
    | EqVisUnPrivTauLCo {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, vclo sim (k1 a) t2) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (TauF t2)
    | EqVisUnPrivTauRCo {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, vclo sim t1 (k2 a)) -> secure_eqitF b1 b2 l vclo sim (TauF t1) (VisF e k2)
    | EqVisUnPrivVisCo {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
        (SIZECHECK1 : nonempty A ) (SIZECHECK2 : nonempty B) :
        (forall a b, vclo sim (k1 a) (k2 b)) -> secure_eqitF b1 b2 l vclo sim (VisF e1 k1) (VisF e2 k2)
    (* info_flow protecting inductive constructors *)
    | EqVisUnPrivLInd {A} (e : E A) k1 t2 (CHECK : b1) (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe (k1 a)) (observe t2) ) ->
        secure_eqitF b1 b2 l vclo sim (VisF e k1) (observe t2)
    | EqVisUnPrivRInd {A} (e : E A) t1 k2 (CHECK : b2) (SECCHECK : ~ leq (priv A e) l) (SIZECHECK : nonempty A) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe t1) (observe (k2 a) )) ->
        secure_eqitF b1 b2 l vclo sim (observe t1) (VisF e k2)
    (* info_flow protecting constructors for halting events, should capture the notion that a secret halt means
       that either it halted or it is performing some secret or silent computation and you can't tell which *)
    | EqVisUnprivHaltLTauR {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l ) (SIZECHECK : empty A) :
        sim (Vis e k1) t2 -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (TauF t2)
    | EqVisUnprivHaltRTauL {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l ) (SIZECHECK : empty A) :
        sim t1 (Vis e k2) -> secure_eqitF b1 b2  l vclo sim (TauF t1) (VisF e k2)
    | EqVisUnprivHaltLVisR {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
            (SIZECHECK : empty A) :
      (forall b, vclo sim (Vis e1 k1) (k2 b) ) -> secure_eqitF b1 b2 l vclo sim (VisF e1 k1) (VisF e2 k2)
    | EqVisUnprivHaltRVisL {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
            (SIZECHECK : empty B) :
        (forall a, vclo sim (k1 a) (Vis e2 k2)) -> secure_eqitF b1 b2 l vclo sim (VisF e1 k1) (VisF e2 k2)
  .

  Hint Constructors secure_eqitF : itree.

  Definition secure_eqit_ (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => secure_eqitF b1 b2 l vclo sim (observe t1) (observe t2).

  Hint Unfold secure_eqit_ : itree.

  Lemma secure_eqitF_mono b1 b2 l x0 x1 vclo vclo' sim sim'
        (IN: secure_eqitF b1 b2 l vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    secure_eqitF b1 b2 l vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto with itree.
  Qed.

  Lemma secure_eqit_mono b1 b2 l vclo (MON: monotone2 vclo) : monotone2 (secure_eqit_ b1 b2 l vclo).
  Proof.
    do 2 red. intros; eapply secure_eqitF_mono; eauto.
  Qed.

  Hint Resolve secure_eqit_mono : paco.

  Definition eqit_secure b1 b2 l := paco2 (secure_eqit_ b1 b2 l id) bot2.

  (* want and eqitC_secure which could help prove some interesting stuff

   *)


  (*
    Note that this is not reflexive (think it is symmetric and transitive)
    Suppose SecureFlip : E bool has privilege 1 and trigger SecureFlip is
    observed at privilege 0. We end to prove eqit_secure false false 0 of it
    requires us to show forall a b, eqit_secure false false 0 (Ret a) (Ret b)
    this is false, suppose a = true and b = false and the relation is equality

   *)


End SecureUntimed.

#[global] Hint Resolve secure_eqit_mono : paco.

#[global] Hint Constructors secure_eqitF : itree.

Definition NatPreorder : Preorder :=
  {|
  L := nat;
  leq := fun n m => n <= m
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
  | [  Hemp : empty ?A |- secure_eqitF _ _ _ _ _ _ _ _ (@VisF _ _ _ ?A _ _) _ ] =>
    try apply EqVisUnprivHaltLTauR; try apply EqVisUnprivHaltLVisR; auto with itree; intros

  | [  Hemp : empty ?A |- secure_eqitF _ _ _ _ _ _ _ _ _ (@VisF _ _ _ ?A _ _)  ] =>
    try apply EqVisUnprivHaltRTauL; try apply EqVisUnprivHaltRVisL; auto with itree; intros end.

Section SecureUntimedUnReflexive.

Section eqit_secureC.
  (* might not be the order I eventually want but whatever*)
  Context {E: Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  Context (Label : Preorder) (priv : forall A, E A -> L) (l : L).


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
  Qed.

End eqit_secureC.


Ltac gfinal_with H := gfinal; left; apply H.

Lemma eqit_secure_sym : forall b1 b2 E R1 R2 RR Label priv l (t1 : itree E R1) (t2 : itree E R2),
    eqit_secure Label priv RR b1 b2 l t1 t2 -> eqit_secure Label priv (flip RR) b2 b1 l t2 t1.
Proof.
  intros b1 b2 E R1 R2 RR Label priv l. pcofix CIH.
  intros t1 t2 Hsec. pfold. red. punfold Hsec. red in Hsec.
  hinduction Hsec before r; intros; eauto with itree; pclearbot;
  try (unpriv_co; right; apply CIH; apply H);
  try unpriv_halt.
  - constructor; auto with itree. intros. right. apply CIH; apply H.
  - specialize (H a). remember (k2 a) as t. clear Heqt k2.
     left.
     intros. pfold. red. cbn. punfold H. red in H. cbn in H.
     inv H; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto;
     try (unpriv_halt; fail).
     +  unpriv_halt. right. apply CIH. pfold. auto.
     + rewrite H0. rewrite H0 in H2. unpriv_halt.
       right. apply CIH. pfold. apply H2.
     + unpriv_halt. right. apply CIH. apply H1.
     + unpriv_halt. right. apply CIH. apply H1.
  - specialize (H b). remember (k1 b) as t. clear Heqt k1.
     left.
     intros. pfold. red. cbn. punfold H. red in H. cbn in H.
     inv H; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto;
     try (unpriv_halt; fail).
     +  unpriv_halt. right. apply CIH. pfold. auto.
     + rewrite H1. rewrite H1 in H2. unpriv_halt.
       right. apply CIH. pfold. apply H2.
     + unpriv_halt. inv SIZECHECK0. contradiction.
     + unpriv_halt. right. apply CIH. apply H2.
Qed.

Lemma secure_eqit_mon : forall E (b1 b2 b3 b4 : bool) R1 R2 RR1 RR2 Label priv l
      (t1 : itree E R1) (t2 : itree E R2),
    (b1 -> b3) -> (b2 -> b4) -> (RR1 <2= RR2) ->
    eqit_secure Label priv RR1 b1 b2 l t1 t2 -> eqit_secure Label priv RR2 b3 b4 l t1 t2.
Proof.
  intros. generalize dependent t2. revert t1. pcofix CIH.
  intros t1 t2 Ht12. pstep. red.
  punfold Ht12. red in Ht12.
  hinduction Ht12 before r; intros; eauto; pclearbot;
  try (unpriv_co; right; apply CIH; try red; eauto; fail);
  try (unpriv_halt; try contra_size; right; apply CIH; try red; eauto; fail).
  constructor; auto. right.  eauto. apply CIH; apply H2.
Qed.

End SecureUntimedUnReflexive.
