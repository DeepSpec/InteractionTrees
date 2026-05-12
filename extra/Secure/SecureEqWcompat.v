(* Chain-based congruence for [eqit_secure].

   This file replaces the paco-style [wcompatible2] proofs of "up-to" closures
   over [secure_eqit_]. In Pous' coinduction library we don't need a separate
   [wcompatible2] development: we prove the congruence directly as a fact
   about any chain element [elem c] and recover the gfp-level statement by
   instantiating [c := chain_gfp _]. See [theories/Eq/Eqit.v] —
   [euttge_proper_euttC] / [euttge_proper_eutt] and [eqit_bind_chain] are the
   templates.

   What this file currently exports:

   - The Ltac utilities used by downstream files
     ([inv_vis_secure], [clear_trivial], [find_size], [produce_elem], [spew]).
   - The small helper [eqit_secure_shalt_refl].
   - A chain-level [Proper] instance [eqit_secure_proper_chain] for rewriting
     under [eqit_secure ... eq] on either side of [elem c]. The proof body is
     currently [Admitted]; see the TODO note inside it. The instance is
     declared so downstream chain-style proofs can [rewrite] under it once the
     proof is filled in.

   At the gfp level, [SecureEqEuttHalt.v] already provides:
   - [proper_eqit_secure_eqit] — rewrite under [eqit b b eq] (eq_itree / eutt).
   - [proper_eqit_secure_eqit_secure] — rewrite under [eqit_secure ... eq]. *)

From Stdlib Require Import Morphisms Program.Basics.
From Coinduction Require Import all.
From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* ===== Small helper lemma (paco-free, kept verbatim from prior file) ===== *)

Lemma eqit_secure_shalt_refl : forall E R1 R2 b1 b2 (RR : R1 -> R2 -> Prop) Label priv l A (e : E A) k1 k2,
    (~ leq (priv _ e) l) -> empty A ->
    eqit_secure Label priv RR b1 b2 l (Vis e k1) (Vis e k2).
Proof.
  intros. step. cbn. unpriv_halt. contra_size.
Qed.

(* ===== Utility Ltacs (paco-free) ===== *)

Ltac inv_vis_secure := ddestruction; subst;
   try contradiction; try contra_size.

Ltac clear_trivial :=
  repeat match goal with
  | H : empty ?A, H' : forall a : ?A, ?P |- _ => clear H' end.

Ltac find_size A :=
  match goal with
  | H : nonempty A |- _ => idtac
  | H : empty A |- _ => idtac
  | |- _ => destruct (classic_empty A); try contra_size end.

Ltac produce_elem H A := inv H; assert (nonempty A); try (constructor; auto with itree; fail).

(* Specialize some hypothesis with the assumption x *)
Ltac spew x :=
  let T := type of x in
  repeat lazymatch goal with
  | [ H0 : forall (_ : T), _ |- _ ] => specialize (H0 x)
  end.

(* ===== Chain-level [Proper] for [elem c] under [eqit_secure ... eq] =====

   The proof follows the template of [euttge_proper_euttC] in
   [theories/Eq/Eqit.v]: [tower induction] on the chain, then case-split on
   the chain-element hypothesis at body level, with nested case analysis on
   the [eqit_secure] premises. The body should mirror the original paco proof
   of [eqit_secureC_wcompat_id'] (~ 170 lines, 14 case bullets) with the paco
   verbs replaced by chain primitives. *)
#[global] Instance eqit_secure_proper_chain
  {E R1 R2} (RR : R1 -> R2 -> Prop) Label priv l (b1 b2 : bool)
  (c : Chain (secure_eqit_mon (E := E) Label priv RR b1 b2 l)) :
  Proper (eqit_secure Label priv eq false false l ==>
          eqit_secure Label priv eq false false l ==>
          flip impl) (elem c).
Proof.
  unfold Proper, respectful, flip, impl.
  tower induction. clear c. 
  intros c CIH t1 t2 Ht1t2 t3 t4 Ht3t4 Hbt2t4.
  icbn; icbn in Hbt2t4.
  step in Ht1t2; step in Ht3t4.  
  revert t1 t3 Ht1t2 Ht3t4. induction Hbt2t4; intros.   
  (* Ret-Ret *)
  - inv Ht1t2; inv Ht3t4. now constructor. 
  - 
  (* TODO(paco→coinduction migration): port the 14-case body of the original
     paco proof [eqit_secureC_wcompat_id'] to a [tower induction] over the
     chain [c], replacing the paco verbs:
       [gclo ... gfinal ; left ; apply H] → [apply IH; eauto]
       [pclearbot]                         → (delete: no bot disjunction)
       [pstep_reverse]                     → [now unstep] / [now step]
       [eauto with paco]                   → [eauto with itree]
     The proof shape mirrors [euttge_proper_euttC] in [theories/Eq/Eqit.v].
     Sketch — for each [secure_eqitF] constructor on the [REL] hypothesis,
     case-split on [EQVl] and [EQVr] and reconstruct the resulting chain
     element using [IH] from the [tower induction]. *)
Admitted.
