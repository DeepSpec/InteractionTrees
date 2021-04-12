From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.SecurityImp
     Secure.StrongBisimProper
     Secure.SecurityAsm
     Secure.SecurityImpHandler
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.

(* Note that this definition sets considers all registers to be private *)

Definition priv_asm (priv : privacy_map) (A : Type) (e : (Reg +' Memory +' IOE) A ) :=
  match e with
  | inl1 _ => Private
  | inr1 (inl1 (Load x)) => priv x
  | inr1 (inl1 (Store x _ )) => priv x
  | inr1 (inr1 (LabelledPrint s _ ) ) => s
  end.

Definition low_reg_mem_equiv (priv : privacy_map) : (registers * memory) -> (registers * memory) -> Prop := fun '(reg1, mem1) '(reg2, mem2) => forall x, priv x = Public -> mem1 x = mem2 x.

Definition reg_mem : Type := registers * memory.

Definition low_eqit_secure_asmstate (b1 b2 : bool) (priv : var -> sensitivity) {R1 R2 : Type} (RR : R1 -> R2 -> Prop )
           (m1 : stateT reg_mem (itree IOE) R1) (m2 : stateT reg_mem (itree IOE) R2) : Prop :=
  forall s1 s2, low_reg_mem_equiv priv s1 s2 -> eqit_secure sense_preorder priv_io (product_rel (low_reg_mem_equiv priv) RR) b1 b2 Public (m1 s1) (m2 s2).

Lemma low_reg_mem_equiv_update_public:
  forall (priv_map : privacy_map) (x : addr) (v : value),
    priv_map x = Public ->
    forall (reg1 : registers) (mem1 : memory) (reg2 : registers) (mem2 : memory),
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, mem2) ->
      low_reg_mem_equiv priv_map (reg1, update x v mem1) (reg2, update x v mem2).
Proof.
  intros priv_map x v Hx reg1 mem1 reg2 mem2 Hs.
  red. red in Hs. intros. unfold update. rewrite Hs; auto.
Qed.

Lemma low_reg_mem_equiv_update_priv_l:
  forall (priv_map : privacy_map) (x : addr) (v : value),
    priv_map x = Private ->
    forall (reg1 : registers) (mem1 : memory) (reg2 : registers) (mem2 : memory),
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, mem2) ->
      low_reg_mem_equiv priv_map (reg1, update x v mem1) (reg2, mem2).
Proof.
  intros priv_map x v Hx reg1 mem1 reg2 mem2 Hs.
  red. red in Hs. intros. unfold update.
  assert (x <> x0).
  { intro. subst. rewrite Hx in H. discriminate. }
  apply eqb_neq in H0. rewrite H0. auto.
Qed.

Lemma low_reg_mem_equiv_update_priv_r:
  forall (priv_map : privacy_map) (x : addr) (v : value),
    priv_map x = Private ->
    forall (reg1 : registers) (mem1 : memory) (reg2 : registers) (mem2 : memory),
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, mem2) ->
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, update x v mem2).
Proof.
  intros priv_map x v Hx reg1 mem1 reg2 mem2 Hs.
  red. red in Hs. intros. unfold update.
  assert (x <> x0).
  { intro. subst. rewrite Hx in H. discriminate. }
  apply eqb_neq in H0. rewrite H0. auto.
Qed.

Ltac destruct_asm := repeat match goal with
                    | e : (Reg +' Memory +' IOE) ?A |- _ => destruct e
                    | e : (Memory +' IOE) ?A |- _ => destruct e
                    | e : Reg ?A |- _ => destruct e as [ ?r | ?r ?v ]
                    | e : Memory ?A |- _ => destruct e as [?x | ?x ?v]
                    | e : IOE ?A |- _ => destruct e as [?s ?v] end.

Lemma interp_eqit_secure_asm : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (priv_map : privacy_map) 
                                 (t1 : itree (Reg +' Memory +' IOE) R1 ) 
                                 (t2 : itree (Reg +' Memory +' IOE) R2),
    eqit_secure sense_preorder (priv_asm priv_map) RR true true Public t1 t2 ->
    low_eqit_secure_asmstate true true priv_map RR (interp_asm t1 )  (interp_asm t2). 
Proof.
  intros. red. intros [reg1 mem1] [reg2 mem2]. unfold interp_asm.
  generalize dependent t2.
  revert reg1 mem1 reg2 mem2 t1.
  pcofix CIH. intros ? ? ? ? ? ? Ht Hs.
  punfold Ht.
  red in Ht. remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Ht before r; intros; use_simpobs.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_ret.
    pfold; constructor; auto.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_tau.
    pfold; constructor; right. pclearbot. apply CIH; auto.
  - rewrite Heqot1. rewrite interp_state_tau. pfold; constructor; auto.
    pstep_reverse.
  - rewrite Heqot2. rewrite interp_state_tau. pfold; constructor; auto.
    pstep_reverse.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    destruct_asm; cbn; cbv in SECCHECK; try (destruct (priv_map x) eqn : Hx ); try contradiction.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; auto.
      red in Hs. unfold get. rewrite Hs; auto. apply H.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; try apply H.
      apply low_reg_mem_equiv_update_public; auto.
    + repeat rewrite bind_bind. repeat rewrite bind_trigger. repeat setoid_rewrite bind_ret_l. 
      cbn. pfold. constructor; auto. left. pfold. constructor. right. apply CIH; auto.
      apply H.
  - pclearbot. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_vis. rewrite interp_state_tau.
    destruct_asm; cbv in SECCHECK; try (destruct (priv_map x) eqn : Hx ); try contradiction; cbn;
    try rewrite bind_ret_l; try (rewrite bind_bind; rewrite bind_trigger);
    try (pfold; constructor; right; apply CIH; auto; cbn; apply H; fail).
    + pfold. constructor. right. apply CIH; auto. cbn. apply H.
      apply low_reg_mem_equiv_update_priv_l; auto.
    + setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau. cbn. pfold. red. cbn. unpriv_co. right. 
      apply CIH; auto. pfold. constructor; auto. pstep_reverse.
  - pclearbot. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_vis. rewrite interp_state_tau.
    destruct_asm; cbv in SECCHECK; try (destruct (priv_map x) eqn : Hx ); try contradiction; cbn;
    try rewrite bind_ret_l; try (rewrite bind_bind; rewrite bind_trigger);
    try (pfold; constructor; right; apply CIH; auto; cbn; apply H; fail).
    + pfold. constructor. right. apply CIH; auto. cbn. apply H.
      apply low_reg_mem_equiv_update_priv_r; auto.
    + setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau. cbn. pfold. red. cbn. unpriv_co. right. 
      apply CIH; auto. pfold. constructor; auto. pstep_reverse.
  - rewrite Heqot1. rewrite Heqot2. pclearbot.
    repeat rewrite interp_state_vis. 
    destruct_asm; cbv in SECCHECK1; cbv in SECCHECK2; 
    try (destruct (priv_map x) eqn : Hx ); try (destruct (priv_map x0) eqn : Hx0 ); try contradiction; cbn; try (
      repeat rewrite bind_ret_l; cbn; pfold; constructor; right; apply CIH; auto;
      apply H).
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right.
      apply CIH; auto. apply H. apply low_reg_mem_equiv_update_priv_l; auto.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right.
      apply CIH; auto. apply H. eapply low_reg_mem_equiv_update_priv_l; eauto.
    + repeat rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 1. pfold. red. cbn. 
      unpriv_co. right. apply CIH; auto. pfold. constructor; auto. pstep_reverse. 
    + rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 1.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold; constructor; auto; pstep_reverse.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right.
      apply CIH; auto. apply H. apply low_reg_mem_equiv_update_priv_r; auto.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right.
      apply CIH; auto. apply H. apply low_reg_mem_equiv_update_priv_r; auto. 
    + rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 2.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold; constructor; auto; pstep_reverse.
    + rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 2.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold; constructor; auto; pstep_reverse.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right.
      apply CIH; auto. apply H. apply low_reg_mem_equiv_update_priv_l; auto.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right.
      apply CIH; auto. apply H. apply low_reg_mem_equiv_update_priv_r; auto.
    + repeat rewrite bind_ret_l. cbn. pfold. constructor. right.
      apply CIH; auto. apply H. apply low_reg_mem_equiv_update_priv_r; auto.
      apply low_reg_mem_equiv_update_priv_l; auto.
    + rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 1.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold; constructor; auto; pstep_reverse.
    + rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 1.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold; constructor; auto; pstep_reverse.
      apply low_reg_mem_equiv_update_priv_r; auto.
    + rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 2.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold; constructor; auto; pstep_reverse.
    + rewrite bind_ret_l. rewrite bind_bind. rewrite bind_trigger.
      setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau at 2.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold; constructor; auto; pstep_reverse. apply low_reg_mem_equiv_update_priv_l; auto.
    + repeat rewrite bind_bind. repeat setoid_rewrite bind_ret_l.
      repeat setoid_rewrite <- interp_state_tau. repeat rewrite bind_trigger.
      pfold. red. cbn. unpriv_co. right. apply CIH; auto.
      pfold. constructor. left. auto.
  - rewrite Heqot1. rewrite interp_state_vis. 
    destruct_asm; cbv in SECCHECK; try (destruct (priv_map x) eqn : Hx ); try contradiction; cbn.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
      eapply H0; eauto. apply low_reg_mem_equiv_update_priv_l; auto.
    + rewrite bind_bind. rewrite bind_trigger. setoid_rewrite bind_ret_l.
      pfold. red. cbn. unpriv_ind. cbn. constructor; auto. pstep_reverse.
  - rewrite Heqot2. rewrite interp_state_vis. 
    destruct_asm; cbv in SECCHECK; try (destruct (priv_map x) eqn : Hx ); try contradiction; cbn.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold; constructor; auto. pstep_reverse.
      eapply H0; eauto. apply low_reg_mem_equiv_update_priv_r; auto.
    + rewrite bind_bind. rewrite bind_trigger. setoid_rewrite bind_ret_l.
      pfold. red. cbn. unpriv_ind. cbn. constructor; auto. pstep_reverse.
  - destruct_asm; inv SIZECHECK; exfalso; apply H0; try apply tt; apply 0.
  - destruct_asm; inv SIZECHECK; exfalso; apply H0; try apply tt; apply 0.
  - destruct_asm; inv SIZECHECK; exfalso; apply H0; try apply tt; apply 0.
  - destruct_asm; inv SIZECHECK; exfalso; apply H0; try apply tt; apply 0.
Qed.
