(** * Equivalence up to taus *)

(** Abbreviated as [eutt]. *)

(** We consider [Tau] as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many [Tau]s between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. This ensures that equivalence
   up to taus is transitive (and in fact an equivalence relation).
 *)

(** A rewrite hint database named [itree] is available via the tactic
    [autorewrite with itree] as a custom simplifier of expressions using
    mainly [Ret], [Tau], [Vis], [ITree.bind] and [ITree.Interp.Interp.interp].
 *)

(** This file contains only the definition of the [eutt] relation.
    Theorems about [eutt] are split in two more modules:

    - [ITree.Eq.UpToTausCore] proves that [eutt] is reflexive, symmetric,
      and that [ITree.Eq.Eq.eq_itree] is a subrelation of [eutt].
      Equations for [ITree.Core.ITreeDefinition] combinators which only rely on
      those properties can also be found here.

    - [ITree.Eq.UpToTausEquivalence] proves that [eutt] is transitive,
      and, more generally, contains theorems for up-to reasoning in
      coinductive proofs.
 *)

(** Splitting things this way makes the library easier to build in parallel.
 *)

(* begin hide *)
Require Import Paco.paco.

From ITree Require Import
     Core.ITreeDefinition
     Eq.Eq.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Definition euttG_ rh := @eqit_ E R1 R2 RR true true (eqit_trans_clo true true true true rh).

Definition euttG r rl rh t1 t2 := gcpn2 (euttG_ rh) r rl t1 t2.

Lemma test (bl br: bool) rh rh' r
   (LE: rh <2= rh'):
  cpn2 (eqit_ RR bl br rh) r <2= cpn2 (@eqit_ E _ _ RR bl br rh') r.
Proof.
  intros. exists (cpn2 (eqit_ RR bl br rh)).
  - econstructor; cycle 1.
    { intros.

      
    
Qed.

Section EUTT_REL.

Context (T1 T2 : Type).

Definition eutt_rel := (T1 * T2) + (T1 * T2) -> Prop.

Definition rpair (r1 r2: T1 -> T2 -> Prop) : eutt_rel := fun x =>
  match x with
  | inl (t1,t2) => r1 t1 t2
  | inr (t1,t2) => r2 t1 t2
  end.

Definition rfst (r: eutt_rel) t1 t2 := r (inl (t1,t2)).

Definition rsnd (r: eutt_rel) t1 t2 := r (inr (t1,t2)).

Lemma rpair_mon r s r' s' p
      (IN: rpair r s p)
      (LEr: r <2= r')
      (LEs: s <2= s'):
  rpair r' s' p.
Proof.
  destruct p, p; simpl in *; eauto.
Qed.

Lemma rfst_mon r r' t1 t2
      (IN: rfst r t1 t2)
      (LE: r <1= r'):
  rfst r' t1 t2.
Proof. apply LE, IN. Qed.

Lemma rsnd_mon r r' t1 t2
      (IN: rsnd r t1 t2)
      (LE: r <1= r'):
  rsnd r' t1 t2.
Proof. apply LE, IN. Qed.

Lemma rpair_bot: rpair bot2 bot2 <1= bot1.
Proof.
  intros. destruct x0, p; contradiction.
Qed.

(* Definition rdup (r: itree' E R1 -> itree' E R2 -> Prop) : eutt_rel := *)
(*   rpair (fun x y => r (observe x) (observe y)) (fun x y => r (observe x) (observe y)). *)

(* Lemma rdup_mon r r' p *)
(*       (IN: rdup r p) *)
(*       (LEr: r <2= r'): *)
(*   rdup r' p. *)
(* Proof. *)
(*   destruct p, p; simpl in *; eauto. *)
(* Qed. *)

(* Lemma rdup_bot: rdup bot2 <1= bot1. *)
(* Proof. *)
(*   intros. destruct x0, p; contradiction. *)
(* Qed. *)

End EUTT_REL.

Hint Unfold rpair rfst rsnd.
Hint Resolve rpair_mon : paco.
(* Hint Unfold rdup. *)
     
Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive euttGF (euttG: eutt_rel (itree E R1) (itree E R2))
  : eutt_rel (itree' E R1) (itree' E R2) :=
| euttGF_ret r1 r2
      (RBASE: RR r1 r2):
    euttGF euttG (inl (RetF r1, RetF r2))
| euttGF_tau t1 t2
      (EQTAUS: euttG (inl (t1, t2))):
    euttGF euttG (inl (TauF t1, TauF t2))


           
| euttGF_tauL t1 ot2
      (EQTAUS: euttGF euttG (inl (observe t1, ot2))):
    euttGF euttG (inl (TauF t1, ot2))
| euttGF_tauR ot1 t2
      (EQTAUS: euttGF euttG (inl (ot1, observe t2))):
    euttGF euttG (inl (ot1, TauF t2))
.

| euttGF_vis u (e : E u) k1 k2
      (EUTTK: forall x, euttG (inl (k1 x, k2 x)) \/ euttG (inr (k1 x, k2 x))):
    euttGF euttG (inj (VisF e k1, VisF e k2))
           
.
Hint Constructors euttGF.







Inductive euttGF (euttG: eutt_rel) : itree' E R1 -> itree' E R2 -> Prop :=
| euttGF_ret r1 r2
      (RBASE: RR r1 r2):
    euttGF euttG (RetF r1) (RetF r2)
| euttGF_vis u (e : E u) k1 k2
      (EUTTK: forall x, euttG (inl (k1 x, k2 x)) \/ euttG (inr (k1 x, k2 x))):
    euttGF euttG (VisF e k1) (VisF e k2)
| euttGF_tau t1 t2
      (EQTAUS: euttG (inl(t1, t2))):
    euttGF euttG (TauF t1) (TauF t2)
| euttGF_tauL t1 ot2
      (EQTAUS: euttGF euttG (observe t1) ot2):
    euttGF euttG (TauF t1) ot2
| euttGF_tauR ot1 t2
      (EQTAUS: euttGF euttG ot1 (observe t2)):
    euttGF euttG ot1 (TauF t2)
.
Hint Constructors euttGF.

Definition euttG' r rw rs := gcpn1 (compose rdup euttGF) (rpair r r) (rpair rw rs).
Hint Unfold euttG'.

Variant euttG r rw rs t1 t2 :=
| _euttG (IN: forall p, p = inl(t1,t2) \/ p = inr(t1,t2) -> euttG' r rw rs p)
.
Hint Constructors euttG.

Lemma euttGF_mon r r' x y
    (EUTT: euttGF r x y)
    (LEr: r <1= r'):
  euttGF r' x y.
Proof.
  induction EUTT; eauto.
  econstructor; intros. edestruct EUTTK; eauto.
Qed.

Lemma monotone_euttG_ : monotone1 (compose rdup euttGF).
Proof. repeat intro. destruct x0, p; eauto using euttGF_mon. Qed.
Hint Resolve monotone_euttG_ : paco.

End EUTTG.

Hint Constructors euttGF.
Hint Unfold euttG'.
Hint Constructors euttG.
Hint Resolve monotone_euttG_ : paco.



Section EUTTG_Properties.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).
(**
   Correctness
 **)

Lemma eutt_le_euttG:
  eutt RR <2= euttG bot2 bot2 bot2.
Proof.
Admitted.

Lemma euttG_le_eutt:
  euttG bot2 bot2 bot2 <2= eutt RR.
Proof.
Admitted.

(**
   Reasoning Principles
 **)

(* Make new hypotheses *)

Lemma euttG_coind r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) x
      (OBG: forall rw' rs'
               (OLDW: rw <2= rw') (NEWW: x <2= rw')
               (OLDS: rs <2= rs') (NEWS: x <2= rs'),
          x <2= euttG r rw' rs'):
    x <2= euttG r rw rs.
Proof.
  econstructor. revert x0 x1 PR.
  gcofix CIH with rr; intros.
  hexploit (OBG (rfst rr) (rsnd rr)); eauto.
  intros. destruct H. repeat red in IN.
  eapply gcpn1_mon; eauto with paco.
  intros. destruct x0, p0; eauto.
Qed.

(* Process itrees *)

Lemma euttG_ret: forall r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) v1 v2,
  RR v1 v2 -> euttG r rw rs (Ret v1) (Ret v2).
Proof.
  intros. econstructor. intros. gstep.
  inv H0; econstructor; eauto.
Qed.

Lemma euttG_bind: forall r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) t1 t2,
  eqit_bind_clo true true (euttG r rw rs) t1 t2 -> euttG r rw rs t1 t2.
Proof.
Admitted.

Lemma euttG_trans_eq: forall r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) t1 t2,
  eqit_trans_clo false true false true (euttG r rw rs) t1 t2 -> euttG r rw rs t1 t2.
Proof.
Admitted.

(* Lose weak hypotheses after general rewriting *)

Lemma euttG_trans_eutt: forall r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) t1 t2,
  eqit_trans_clo true true true true (euttG r r rs) t1 t2 -> euttG r rw rs t1 t2.
Proof.
Admitted.

(* Make available weak hypotheses *)

Lemma euttG_tau: forall r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) t1 t2,
  euttG rw rw rs t1 t2 -> euttG r rw rs (Tau t1) (Tau t2).
Proof.
  (* econstructor. intros. gstep. destruct H. *)
  (* destruct H0; subst; econstructor. *)
  (* - repeat red in IN. *)
Admitted.

(* Make available strong hypotheses *)

Lemma euttG_vis: forall r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) u (e: E u) k1 k2,
  (forall v, euttG rs rs rs (k1 v) (k2 v)) -> euttG r rw rs (Vis e k1) (Vis e k2).
Proof.
  econstructor. intros. gstep. destruct H0; subst.
  - econstructor. intros. right.
    destruct (H x). hexploit IN; [right; eauto|]. intros IN'.
    repeat red in IN'. gbase. simpl.
    
    

Qed.

(* Use available hypotheses *)

Lemma euttG_base: forall r rw rs (INVW: r <2= rw) (INVS: rw <2= rs) t1 t2,
  r t1 t2 -> euttG r rw rs t1 t2.
Proof.
Admitted.

End EUTTG_Properties.



