From Coq Require Import
     List
     Morphisms.

From ITree Require Import
     ITree
     ITreeFacts
     Secure.SecureEqHalt
.

From SecureExample Require Import
     LabelledImp
     LabelledAsm
     LabelledImpHandler.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

From Paco Require Import paco.

(* Note that this definition sets considers all registers to be private *)

Definition priv_asm (priv : privacy_map sensitivity_lat) (A : Type) (e : (Reg +' Memory +' (IOE sensitivity_lat)) A ) :=
  match e with
  | inl1 _ => Private
  | inr1 (inl1 (Load x)) => priv x
  | inr1 (inl1 (Store x _ )) => priv x
  | inr1 (inr1 (LabelledPrint _ s _ ) ) => s
  end.

Definition low_reg_mem_equiv (priv : privacy_map sensitivity_lat) : (registers * memory) -> (registers * memory) -> Prop := fun '(reg1, mem1) '(reg2, mem2) => forall x, priv x = Public -> mem1 x = mem2 x.

Definition reg_mem : Type := registers * memory.

#[local] Notation lat := sensitivity_lat.

Definition low_eqit_secure_asmstate (b1 b2 : bool) (priv : var -> sensitivity) {R1 R2 : Type} (RR : R1 -> R2 -> Prop )
           (m1 : stateT reg_mem (itree (IOE lat)) R1) (m2 : stateT reg_mem (itree (IOE lat)) R2) : Prop :=
  forall s1 s2, low_reg_mem_equiv priv s1 s2 -> eqit_secure (Lattice.PreOrderOfLattice lat) (priv_io _) (product_rel (low_reg_mem_equiv priv) RR) b1 b2 Public (m1 s1) (m2 s2).

Lemma low_reg_mem_equiv_update_public:
  forall (priv_map : privacy_map lat) (x : addr) (v : value),
    priv_map x = Public ->
    forall (reg1 : registers) (mem1 : memory) (reg2 : registers) (mem2 : memory),
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, mem2) ->
      low_reg_mem_equiv priv_map (reg1, update x v mem1) (reg2, update x v mem2).
Proof.
  intros priv_map x v Hx reg1 mem1 reg2 mem2 Hs.
  red. red in Hs. intros. unfold update. rewrite Hs; auto.
Qed.

Lemma low_reg_mem_equiv_update_priv_l:
  forall (priv_map : privacy_map lat) (x : addr) (v : value),
    priv_map x = Private ->
    forall (reg1 : registers) (mem1 : memory) (reg2 : registers) (mem2 : memory),
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, mem2) ->
      low_reg_mem_equiv priv_map (reg1, update x v mem1) (reg2, mem2).
Proof.
  intros priv_map x v Hx reg1 mem1 reg2 mem2 Hs.
  red. red in Hs. intros. unfold update.
  assert (x <> x0).
  { intro. subst. rewrite Hx in H. discriminate. }
  apply String.eqb_neq in H0. rewrite H0. auto.
Qed.

Lemma low_reg_mem_equiv_update_priv_r:
  forall (priv_map : privacy_map lat) (x : addr) (v : value),
    priv_map x = Private ->
    forall (reg1 : registers) (mem1 : memory) (reg2 : registers) (mem2 : memory),
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, mem2) ->
      low_reg_mem_equiv priv_map (reg1, mem1) (reg2, update x v mem2).
Proof.
  intros priv_map x v Hx reg1 mem1 reg2 mem2 Hs.
  red. red in Hs. intros. unfold update.
  assert (x <> x0).
  { intro. subst. rewrite Hx in H. discriminate. }
  apply String.eqb_neq in H0. rewrite H0. auto.
Qed.
