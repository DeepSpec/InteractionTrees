Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Core.

From ITree Require Export
     Eq.Eq.

Local Open Scope itree.

(* Taken from paco-v2.0.3: BEGIN *)

Lemma paco2_mon_bot {T0 T1} (gf gf': rel2 T0 T1 -> rel2 T0 T1) r' x0 x1
    (REL: paco2 gf bot2 x0 x1)
    (LEgf: gf <3= gf'):
  paco2 gf' r' x0 x1.
Proof.
  eapply paco2_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco2_mon_bot {T0 T1} (gf gf': rel2 T0 T1 -> rel2 T0 T1) r' x0 x1
    (REL: upaco2 gf bot2 x0 x1)
    (LEgf: gf <3= gf'):
  upaco2 gf' r' x0 x1.
Proof.
  eapply upaco2_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma rclo2_mon_gen {T0 T1} gf gf' (clo clo': rel2 T0 T1 -> rel2 T0 T1) r r' e0 e1
      (REL: rclo2 gf clo r e0 e1)
      (LEgf: gf <3= gf')
      (LEclo: clo <3= clo')
      (LEr: r <2= r') :
  rclo2 gf' clo' r' e0 e1.
Proof.
  induction REL.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR| apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply LEgf, CLOR'].
Qed.

(* Taken from paco-v2.0.3: END*)



Section FiniteTaus.

Context {E : Type -> Type} {R : Type}.

(* [notau t] holds when [t] does not start with a [Tau]. *)
Definition notauF {I} (t : itreeF E R I) : Prop :=
  match t with
  | TauF _ => False
  | _ => True
  end.

Notation notau t := (notauF (observe t)).

(* [untaus t t'] holds when [t = Tau (... Tau t' ...)]:
   [t] steps to [t'] by "peeling off" a finite number of [Tau].
   "Peel off" means to remove only taus at the root of the tree,
   not any behind a [Vis] step). *)
Inductive untausF :
  itreeF E R (itree E R) -> itreeF E R (itree E R) -> Prop :=
| NoTau ot0 : untausF ot0 ot0
| OneTau ot t' ot0 (OBS: TauF t' = ot) (TAUS: untausF (observe t') ot0): untausF ot ot0
.
Hint Constructors untausF.

Definition unalltausF ot ot0 := untausF ot ot0 /\ notauF ot0.
Hint Unfold unalltausF.

Lemma unalltausF_untausF ot ot0 : unalltausF ot ot0 -> untausF ot ot0.
Proof. intros []; auto. Qed.
Hint Resolve unalltausF_untausF.

Lemma unalltausF_notauF ot ot0 : unalltausF ot ot0 -> notauF ot0.
Proof. intros []; auto. Qed.
Hint Resolve unalltausF_notauF.

(* [finite_taus t] holds when [t] has a finite number of taus
   to peel. *)
Definition finite_tausF ot : Prop := exists ot', unalltausF ot ot'.
Hint Unfold finite_tausF.

(** ** Lemmas *)

Lemma untaus_all ot ot' :
  untausF ot ot' -> notauF ot' -> unalltausF ot ot'.
Proof. induction 1; eauto. Qed.

Lemma unalltaus_notau ot ot' : unalltausF ot ot' -> notauF ot'.
Proof. intros. induction H; eauto. Qed.

Lemma notau_tau I (ot : itreeF E R I) (t0 : I)
  (NOTAU : notauF ot)
  (OBS: TauF t0 = ot): False.
Proof. subst. auto. Qed.
Hint Resolve notau_tau.

Lemma notau_ret I (ot: itreeF E R I) r (OBS: RetF r = ot) : notauF ot.
Proof. subst. red. eauto. Qed.
Hint Resolve notau_ret.

Lemma notau_vis I (ot : itreeF E R I) u (e: E u) k (OBS: VisF e k = ot) : notauF ot.
Proof. intros. subst. red. eauto. Qed.
Hint Resolve notau_vis.

(* If [t] does not start with [Tau], removing all [Tau] does
   nothing. Can be thought of as [notau_unalltaus] composed with
   [unalltaus_injective] (below). *)
Lemma unalltaus_notau_id ot ot' :
  unalltausF ot ot' -> notauF ot -> ot = ot'.
Proof.
  intros [[ | ]] ?; eauto. exfalso; eauto.
Qed.

(* There is only one way to peel off all taus. *)
Lemma unalltaus_injective ot ot1 ot2 :
    unalltausF ot ot1 -> unalltausF ot ot2 -> ot1 = ot2.
Proof.
  intros [Huntaus Hnotau]. revert ot2 Hnotau.
  induction Huntaus; intros; eauto using unalltaus_notau_id.
  eapply IHHuntaus; eauto.
  destruct H as [Huntaus' Hnotau'].
  destruct Huntaus'.
  + exfalso; eauto.
  + subst. inversion OBS0; subst; eauto.
Qed.

(* Adding a [Tau] to [t1] then peeling them all off produces
   the same result as peeling them all off from [t1]. *)
Lemma unalltaus_tau t ot1 ot2
    (OBS: TauF t = ot1)
    (TAUS: unalltausF ot1 ot2):
  unalltausF (observe t) ot2.
Proof.
  destruct TAUS as [Huntaus Hnotau].
  destruct Huntaus.
  - exfalso; eauto.
  - subst; inversion OBS0; subst; eauto.
Qed.

Lemma unalltaus_tau' t ot1 ot2
    (OBS: TauF t = ot1)
    (TAUS: unalltausF (observe t) ot2):
  unalltausF ot1 ot2.
Proof.
  destruct TAUS as [Huntaus Hnotau].
  subst. eauto.
Qed.

Lemma notauF_untausF ot1 ot2
      (NOTAU : notauF ot1)
      (UNTAUS : untausF ot1 ot2) : ot1 = ot2.
Proof.
  destruct UNTAUS; eauto.
  exfalso; eauto.
Qed.

Definition untausF_shift (t1 t2 : itree E R) :
  untausF (TauF t1) (TauF t2) -> untausF (observe t1) (observe t2).
Proof.
  intros H.
  inversion H; subst.
  { constructor. }
  clear H.
  inversion OBS; subst; clear OBS.
  remember (observe t1) as ot1.
  remember (TauF t2) as tt2.
  generalize dependent t1.
  generalize dependent t2.
  induction TAUS; intros; subst; econstructor; eauto.
Qed.

Definition untausF_trans (t1 t2 t3 : itreeF E R _) :
  untausF t1 t2 -> untausF t2 t3 -> untausF t1 t3.
Proof.
  induction 1; auto.
  subst; econstructor; auto.
Qed.

Definition untausF_strong_ind
           (P : itreeF E R _ -> Prop)
           (ot1 ot2 : itreeF E R _)
           (Huntaus : untausF ot1 ot2)
           (Hnotau : notauF ot2)
           (STEP : forall ot1
               (Huntaus : untausF ot1 ot2)
               (IH: forall t1' oti
                     (NEXT: ot1 = TauF t1')
                     (UNTAUS: untausF (observe t1') oti),
                   P oti),
               P ot1)
  : P ot1.
Proof.
  enough (H : forall oti,
             untausF ot1 oti ->
             untausF oti ot2 ->
             P oti
         ).
  { apply H; eauto. }
  revert STEP.
  induction Huntaus; intros; subst.
  - eapply STEP; eauto.
    intros; subst. dependent destruction H; inv Hnotau.
  - destruct H0; auto.
    subst. apply STEP; eauto.
    intros. inv NEXT.
    apply IHHuntaus; eauto.
    + clear -H UNTAUS.
      remember (TauF t') as ott'. remember (TauF t1') as ott1'.
      move H at top. revert_until H. induction H; intros; subst.
      * inv Heqott1'. eauto.
      * inv Heqott'. dependent destruction H; eauto.
    + genobs t1' ot1'. revert UNTAUS. clear -Hnotau H0. induction H0; intros.
      * dependent destruction UNTAUS; eauto.
        subst. simpobs. inv Hnotau.
      * subst. dependent destruction UNTAUS; eauto.
Qed.

(* If [t] does not start with [Tau], then it starts with finitely
   many [Tau]. *)
Lemma notau_finite_taus ot : notauF ot -> finite_tausF ot.
Proof. eauto. Qed.

(* [Vis] and [Ret] start with no taus, of course. *)
Lemma finite_taus_ret ot (r : R) (OBS: RetF r = ot) : finite_tausF ot.
Proof. eauto 10. Qed.

Lemma finite_taus_vis {u} ot (e : E u) (k : u -> itree E R) (OBS: VisF e k = ot):
  finite_tausF ot.
Proof. eauto 10. Qed.

(* [finite_taus] is preserved by removing or adding one [Tau]. *)
Lemma finite_taus_tau t':
  finite_tausF (TauF t') <-> finite_tausF (observe t').
Proof.
  split; intros [? [Huntaus Hnotau]]; eauto 10.
  inv Huntaus.
  - contradiction.
  - inv OBS; eauto.
Qed.

(* (* [finite_taus] is preserved by removing or adding any finite *)
(*    number of [Tau]. *) *)
Lemma untaus_finite_taus ot ot':
    untausF ot ot' -> (finite_tausF ot <-> finite_tausF ot').
Proof.
  induction 1; intros; subst.
  - reflexivity.
  - erewrite finite_taus_tau; eauto.
Qed.

Lemma untaus_untaus : forall (ot1 ot2 ot3: itreeF E R _),
    untausF ot1 ot2 -> untausF ot2 ot3 -> untausF ot1 ot3.
Proof.
  intros t1 t2 t3. induction 1; simpl; eauto.
Qed.

Lemma untaus_unalltaus_rev (ot1 ot2 ot3: itreeF E R _) :
    untausF ot1 ot2 -> unalltausF ot1 ot3 -> unalltausF ot2 ot3.
Proof.
  intros H. revert ot3.
  induction H; intros.
  - eauto with arith.
  - destruct H0 as [Huntaus Hnotau].
    destruct Huntaus.
    + exfalso; eauto.
    + inv OBS0. inversion H0; subst; eauto.
Qed.

Lemma unalltausF_ret : forall x (t: itree' E R),
    unalltausF (RetF x) t -> t = RetF x.
Proof.
  intros x t [UNT NOT]; inversion UNT; subst; clear UNT; [reflexivity | easy].
Qed.

Lemma unalltausF_vis {S}: forall e (k: S -> itree E R) (t: itree' E R),
    unalltausF (VisF e k) t -> t = VisF e k.
Proof.
  intros e k t [UNT NOT]; inversion UNT; subst; clear UNT; [reflexivity | easy].
Qed.

End FiniteTaus.

Arguments untaus_unalltaus_rev : clear implicits.

Hint Resolve unalltausF_notauF.
Hint Resolve unalltausF_untausF.

Hint Constructors untausF.
Hint Unfold unalltausF.
Hint Unfold finite_tausF.
Hint Resolve notau_ret.
Hint Resolve notau_vis.
Hint Resolve notau_tau.

Notation finite_taus t := (finite_tausF (observe t)).
Notation untaus t t' := (untausF (observe t) (observe t')).
Notation unalltaus t t' := (unalltausF (observe t) (observe t')).

Ltac auto_untaus :=
  repeat match goal with
  | [ H1 : notauF ?X, H2 : unalltausF ?X ?Y |- _ ] =>
    assert_fails (unify X Y);
    replace Y with X in * by apply (unalltaus_notau_id _ _ H2 H1)
  | [ H1 : unalltausF ?X ?Y, H2 : unalltausF ?X ?Z |- _ ] =>
    assert_fails (unify Y Z);
    replace Z with Y in * by apply (unalltaus_injective _ _ _ H1 H2)
  end; auto.
