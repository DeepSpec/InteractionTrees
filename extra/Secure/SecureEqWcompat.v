(* Chain-based congruence for [eqit_secure].

   This currently exports:

   - The Ltac utilities used by downstream files
     ([inv_vis_secure], [clear_trivial], [find_size], [produce_elem], [spew]).
   - The small helper [eqit_secure_shalt_refl].
   - A chain-level [Proper] instance [eqit_secure_proper_chain] for rewriting
     under [eqit_secure ... eq] on either side of [elem c]. 

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

(* ===== Generic Ltac utilities (also used by downstream files) ===== *)

Ltac inv_vis_secure := ddestruction;
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

(* Specialize every [forall _ : (type of x), _] hypothesis with [x]. *)
Ltac spew x :=
  let T := type of x in
  repeat lazymatch goal with
  | [ H0 : forall (_ : T), _ |- _ ] => specialize (H0 x)
  end.

Ltac contra_leq :=
  match goal with
  | [ Hleq : leq ?a ?b, Hnleq : ~ leq ?a ?b |- _ ] => contradiction
  end.

(* Decide the size of every event index appearing in the goal classically
   (paco's [find_size] preprocessing) so the shape-directed
   [smart_constructor] always has the [empty]/[nonempty] facts it needs. *)
Ltac resolve_sizes :=
  repeat match goal with
  | |- context [ @VisF _ _ _ ?A _ _ ] =>
      lazymatch goal with
      | _ : empty A |- _ => fail
      | _ : nonempty A |- _ => fail
      | _ => destruct (classic_empty A)
      end
  end;
  try contra_size.

Ltac apply_foralls :=
  repeat match goal with
  | w : ?A, H : forall _ : ?A, _ |- _ => apply (H w)
  end.

(* Close a halting [Vis]/[Vis] obligation, at either the [gfp]
   ([eqit_secure]) or chain ([elem c]) level: step into the halting
   constructor, then finish by the empty-index contradiction or the body
   hypothesis.  More general than [eqit_secure_shalt_refl] (the two events
   need not coincide). *)
Ltac secure_halt_refl :=
  solve [ step; cbn; unpriv_halt; intros;
          repeat match goal with He : nonempty ?A |- _ =>
                   let w := fresh "wit" in destruct He as [w] end;
          first [ contra_size
                | solve [ apply_foralls; eauto with itree ]
                | solve [ eauto with itree ] ] ].

Ltac sec_hyp :=
  first [ eassumption
        | solve [ apply_foralls; first [ eassumption | eauto with itree ] ]
        | solve [ eauto with itree ] ].

Ltac sec_fin := solve [ sec_hyp | secure_halt_refl ].

(* Deep halt/halt subcases: no hypothesis pins the [CIH] intermediate, but it
   can be taken to be the concrete halting [Vis] already on the other side —
   a reflexive halt bridge.  Mirrors paco's explicit
   [econstructor 1 with (t1' := Vis e k)]. *)
Ltac sec_reflexive :=
  match goal with
  | |- eqit_secure _ _ _ _ _ _ ?X ?Y =>
      first [ is_evar Y; unify Y X | is_evar X; unify X Y ]
  end;
  secure_halt_refl.

(* [eapply CIH] leaves [eqit_secure x ?y], [eqit_secure x0 ?y0],
   [elem c ?y ?y0].  Pin the shared evars from a concrete hypothesis before
   any [secure_halt_refl] (running it on an evar goal would invent and shelve
   a spurious event).  The body hypothesis (premise 3) or the [eqit_secure]
   hypotheses (premises 1/2) provide the pinning; try both orders. *)
Ltac by_coinduction CIH :=
  first
  [ (eapply CIH;
     [ first [ sec_hyp | sec_reflexive ]
     | first [ sec_hyp | sec_reflexive ]
     | sec_fin ])
  | (eapply CIH;
     only 3: (solve [ eassumption | apply_foralls; eassumption ]);
     sec_fin) ].

(* ===== Smart constructor for [secure_eqitF] =====

   [smart_constructor conclude] inspects the goal shape (Ret/Tau/Vis on each
   side) and the context (for [leq]/[~ leq]/[nonempty]/[empty] facts), then
   tries the [secure_eqitF] constructors that are compatible with that shape,
   in a sensible order.  For each candidate it [eapply]s the constructor,
   discharges the side-conditions ([SECCHECK]/[SIZECHECK]/[CHECK]) from the
   context, and runs [conclude] on the remaining relational premise(s).  If
   that whole sequence does not close the goal it backtracks and tries the
   next constructor; if none work it leaves the goal untouched (never fails). *)

(* Discharge one subgoal produced by a [secure_eqitF] constructor: trivial
   side-conditions by [assumption]/[reflexivity]/[contra_size]/[auto]; the
   relational premise(s) by [conclude] (after [intros]). *)
Tactic Notation "sec_side" tactic3(conclude) :=
  first [ assumption
        | reflexivity
        | contra_size
        | solve [ econstructor; eassumption ]   (* [nonempty A] from a witness *)
        | solve [ auto ]
        | solve [ intros;
                  repeat match goal with He : nonempty ?A |- _ =>
                           let w := fresh "wit" in destruct He as [w] end;
                  first [ contra_size | conclude ] ] ].

Tactic Notation "smart_constructor" tactic3(conclude) :=
  lazymatch goal with
  | |- @secure_eqitF _ _ _ _ _ _ _ _ _ _ (RetF _) (RetF _) =>
      first [ solve [ eapply secEqRet;             sec_side conclude ]
            | fail 1 "smart_constructor: Ret/Ret unsolved" ]
  | |- @secure_eqitF _ _ _ _ _ _ _ _ _ _ (TauF _) (TauF _) =>
      first [ solve [ eapply secEqTau;             sec_side conclude ]
            | solve [ eapply secEqTauL;            sec_side conclude ]
            | solve [ eapply secEqTauR;            sec_side conclude ]
            | fail 1 "smart_constructor: Tau/Tau unsolved" ]
  | |- @secure_eqitF _ _ _ _ _ _ _ _ _ _ (VisF _ _) (VisF _ _) =>
      first [ solve [ eapply EqVisPriv;            sec_side conclude ]
            | solve [ eapply EqVisUnPrivVisCo;     sec_side conclude ]
            | solve [ eapply EqVisUnprivHaltLVisR; sec_side conclude ]
            | solve [ eapply EqVisUnprivHaltRVisL; sec_side conclude ]
            | solve [ eapply EqVisUnPrivLInd;      sec_side conclude ]
            | solve [ eapply EqVisUnPrivRInd;      sec_side conclude ]
            | fail 1 "smart_constructor: Vis/Vis unsolved" ]
  | |- @secure_eqitF _ _ _ _ _ _ _ _ _ _ (VisF _ _) (TauF _) =>
      first [ solve [ eapply EqVisUnPrivTauLCo;    sec_side conclude ]
            | solve [ eapply EqVisUnprivHaltLTauR; sec_side conclude ]
            | solve [ eapply secEqTauR;            sec_side conclude ]
            | solve [ eapply secEqTauL;            sec_side conclude ]
            | solve [ eapply EqVisUnPrivLInd;      sec_side conclude ]
            | fail 1 "smart_constructor: Vis/Tau unsolved" ]
  | |- @secure_eqitF _ _ _ _ _ _ _ _ _ _ (TauF _) (VisF _ _) =>
      first [ solve [ eapply EqVisUnPrivTauRCo;    sec_side conclude ]
            | solve [ eapply EqVisUnprivHaltRTauL; sec_side conclude ]
            | solve [ eapply secEqTauL;            sec_side conclude ]
            | solve [ eapply secEqTauR;            sec_side conclude ]
            | solve [ eapply EqVisUnPrivRInd;      sec_side conclude ]
            | fail 1 "smart_constructor: Tau/Vis unsolved" ]
  | |- @secure_eqitF _ _ _ _ _ _ _ _ _ _ (VisF _ _) _ =>
      first [ solve [ eapply EqVisUnPrivLInd;      sec_side conclude ]
            | solve [ eapply secEqTauR;            sec_side conclude ]
            | fail 1 "smart_constructor: Vis/? unsolved" ]
  | |- @secure_eqitF _ _ _ _ _ _ _ _ _ _ _ (VisF _ _) =>
      first [ solve [ eapply EqVisUnPrivRInd;      sec_side conclude ]
            | solve [ eapply secEqTauL;            sec_side conclude ]
            | fail 1 "smart_constructor: ?/Vis unsolved" ]
  | |- _ => idtac
  end.

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
  - (* secEqRet *)
    inv Ht1t2; inv Ht3t4; now constructor.
  - (* secEqTau *)
    inv Ht1t2; inv Ht3t4; ddestruction;  
      try contra_size; try contra_leq.
    all: smart_constructor (by_coinduction CIH).
  - (* secEqTauL (CHECK : b1) *)
    inv Ht1t2; ddestruction; try contra_size; try contra_leq.
    + apply secEqTauL; auto. eapply IHHbt2t4; eauto. now unstep.
    + apply EqVisUnPrivLInd; auto. intros. eapply IHHbt2t4; eauto. now unstep.
    + eapply (IHHbt2t4 (Vis _ _)); eauto. now unstep.
  - (* secEqTauR (CHECK : b2) *)
    inv Ht3t4; ddestruction;  try contra_size; try contra_leq.
    + apply secEqTauR; auto. eapply IHHbt2t4; eauto. now unstep.
    + apply EqVisUnPrivRInd; auto. intros. eapply IHHbt2t4; eauto. now unstep.
    + eapply (IHHbt2t4 _ (Vis _ _)); eauto. now unstep.
  - (* EqVisPriv (priv leq) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; try contra_leq.
    all: smart_constructor (by_coinduction CIH).
  - (* EqVisUnPrivTauLCo (left vis nonempty, right tau) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; try contra_leq.
    all: smart_constructor (by_coinduction CIH).
  - (* EqVisUnPrivTauRCo (left tau, right vis nonempty) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; try contra_leq.
    all: smart_constructor (by_coinduction CIH).
  - (* EqVisUnPrivVisCo (left vis nonempty, right vis nonempty) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; try contra_leq.
    all: smart_constructor (by_coinduction CIH).
  - (* EqVisUnPrivLInd (CHECK : b1, left vis nonempty inductive) *)
    inv Ht1t2; ddestruction;  try contra_size; try contra_leq.
    + (* Ht1t2 = EqVisUnPrivTauRCo : observe t1 = TauF t5 *)
      apply secEqTauL; auto.
      match goal with He : nonempty ?A |- _ => destruct He as [aE] end.
      eapply (H0 aE); eauto. unstep. eauto.
    + (* Ht1t2 = EqVisUnPrivVisCo : observe t1 = VisF, nonempty *)
      apply EqVisUnPrivLInd; auto. intros.
      match goal with He : nonempty ?A |- _ => destruct He as [aE] end.
      eapply (H0 aE); eauto. unstep. eauto.
    + (* Ht1t2 = EqVisUnprivHaltLVisR : observe t1 = VisF, A empty *)
      match goal with He : nonempty ?A |- _ => destruct He as [aE] end.
      eapply (H0 aE (Vis _ _)); eauto. unstep. eauto.
  - (* EqVisUnPrivRInd (CHECK : b2, right vis nonempty inductive) *)
    inv Ht3t4; ddestruction;  try contra_size; try contra_leq.
    + (* Ht3t4 = EqVisUnPrivTauLCo : observe t3 = TauF *)
      apply secEqTauR; auto.
      match goal with He : nonempty ?A |- _ => destruct He as [aE] end.
      eapply (H0 aE); eauto. unstep. eauto.
    + (* Ht3t4 = EqVisUnPrivVisCo : observe t3 = VisF, nonempty *)
      apply EqVisUnPrivRInd; auto. intros.
      match goal with He : nonempty ?A |- _ => destruct He as [aE] end.
      eapply (H0 aE); eauto. unstep. eauto.
    + (* Ht3t4 = EqVisUnprivHaltRVisL : observe t3 = VisF, B empty *)
      match goal with He : nonempty ?A |- _ => destruct He as [aE] end.
      eapply (H0 aE _ (Vis _ _)); eauto. unstep. eauto.
  - (* EqVisUnprivHaltLTauR (left vis empty, right tau) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; try contra_leq.
    all: resolve_sizes.
    all: smart_constructor (by_coinduction CIH).
  - (* EqVisUnprivHaltRTauL (left tau, right vis empty) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; try contra_leq.
    all: resolve_sizes.
    all: smart_constructor (by_coinduction CIH).
  - (* EqVisUnprivHaltLVisR (left vis empty, right vis ~leq) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; 
      try contra_leq.
    all: resolve_sizes.
    all: smart_constructor (by_coinduction CIH).
  - (* EqVisUnprivHaltRVisL (left vis ~leq, right vis empty) *)
    inv Ht1t2; inv Ht3t4; ddestruction; 
      try contra_size; try contra_leq.
    all: resolve_sizes.
    all: smart_constructor (by_coinduction CIH).
  Unshelve.
  all: assumption. 
Qed.
