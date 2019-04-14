(** * Strong bisimulation *)

(** Because [itree] is a coinductive type, the naive [eq] relation
    is too strong: most pairs of "morally equivalent" programs
    cannot be proved equal in the [eq] sense.
[[
    (* Not provable *)
    Goal (cofix spin := Tau spin) = Tau (cofix spin := Tau spin).
    Goal (cofix spin := Tau spin) = (cofix spin2 := Tau (Tau spin2)).
]]
    As an alternative, we define a weaker, coinductive notion of equivalence,
    [eqit], which can be intuitively thought of as a form of extensional
    equality. We shall rely extensively on setoid rewriting.
 *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Shallow.

Import ITreeNotations.

(* TODO: Send to paco *)
Global Instance Symmetric_bot2 (A : Type) : @Symmetric A bot2.
Proof. auto. Qed.

Global Instance Transitive_bot2 (A : Type) : @Transitive A bot2.
Proof. auto. Qed.
(* end hide *)

(** ** Coinductive reasoning with Paco *)

(** Similarly to the way we deal with cofixpoints explained in
    [Core.ITreeDefinition], coinductive properties are defined in two steps,
    as greatest fixed points of monotone relation transformers.

    - a _relation transformer_, a.k.a. _generating function_,
      is a function mapping relations to relations
      [gf : (i -> i -> Prop) -> (i -> i -> Prop)];
    - _monotonicity_ is with respect to relations ordered by set inclusion
      (a.k.a. implication, when viewed as predicates)
      [(r1 <2= r2) -> (gf r1 <2= gf r2)];
    - the Paco library provides a combinator [paco2] defining the greatest
      fixed point [paco2 gf] when [gf] is indeed monotone.

    By thus avoiding [CoInductive] to define coinductive properties,
    Paco spares us from thinking about guardedness of proof terms,
    instead encoding a form of productivity visibly in types.
 *)

Coercion is_true : bool >-> Sortclass.

Section eqit.

  (** Although the original motivation is to define an equivalence
      relation on [itree E R], we will generalize it into a
      heterogeneous relation [eqit_] between [itree E R1] and
      [itree E R2], parameterized by a relation [RR] between [R1]
      and [R2].

      Then the desired equivalence relation is obtained by setting
      [RR := eq] (with [R1 = R2]).
   *)
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  (** We also need to do some gymnastics to work around the
      two-layered definition of [itree]. We first define a
      relation transformer [eqitF] as an indexed inductive type
      on [itreeF], which is then composed with [observe] to obtain
      a relation transformer on [itree] ([eqit_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [itree].
   *)

  Inductive eqitF (bl br: bool) (hsim sim : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqitF bl br hsim sim (RetF r1) (RetF r2)
  | EqTau m1 m2
        (REL: sim m1 m2):
      eqitF bl br hsim sim (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2
        (REL: forall v, sim (k1 v) (k2 v) \/ hsim (k1 v) (k2 v)):
      eqitF bl br hsim sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2
        (CHECK: bl)
        (REL: eqitF bl br hsim sim (observe t1) ot2):
      eqitF bl br hsim sim (TauF t1) ot2
  | EqTauR ot1 t2
        (CHECK: br)
        (REL: eqitF bl br hsim sim ot1 (observe t2)):
      eqitF bl br hsim sim ot1 (TauF t2)
  .
  Hint Constructors eqitF.

  Definition eqit_ bl br (hsim sim: itree E R1 -> itree E R2 -> Prop) :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eqitF bl br hsim sim (observe t1) (observe t2).
  Hint Unfold eqit_.

  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono bl br x0 x1 (hsim hsim' sim sim' : itree E R1 -> itree E R2 -> Prop)
        (IN: eqitF bl br hsim sim x0 x1)
        (LEh: forall x2 x3, hsim x2 x3 -> hsim' x2 x3 : Prop)
        (LE: forall x2 x3, sim x2 x3 -> sim' x2 x3 : Prop):
    eqitF bl br hsim' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
    econstructor. intros. edestruct REL; eauto.
  Qed.

  Lemma eqit__mono bl br hsim : monotone2 (eqit_ bl br hsim).
  Proof. do 2 red. intros. eapply eqitF_mono; eauto. Qed.

  Hint Resolve eqit__mono : paco.
  
  Definition eqit bl br hsim : itree E R1 -> itree E R2 -> Prop :=
    paco2 (eqit_ bl br hsim) bot2.

  (** Strong bisimulation on itrees. If [eqit RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)
  
  Definition eq_itree := eqit false false bot2.

  Definition eutt := eqit true true bot2.

  Definition euttle := eqit false true bot2.

  Lemma eqit_cpn_compat bl br:
    compatible2 (eqit_ bl br bot2) (cpn2 (eqit_ bl br bot2)).
  Proof.
    eapply cpn2_compat; eauto with paco. 
  Qed.

End eqit.

(* begin hide *)
Hint Constructors eqitF.
Hint Unfold eqit_.
Hint Resolve eqit__mono : paco.
Hint Unfold eqit.
Hint Unfold eq_itree.
Hint Unfold eutt.
Hint Unfold euttle.
Hint Resolve eqit_cpn_compat : paco.

Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ _ |- _ ] => red in H end).

Lemma flip_eqit {E R1 R2} (RR : R1 -> R2 -> Prop) bl br hsim:
  forall (u : itree E R1) (v : itree E R2),
    eqit RR bl br hsim u v -> eqit (flip RR) br bl (flip hsim) v u.
Proof.
  pcofix self; pstep.
  intros u v euv. punfold euv.
  red in euv |- *. induction euv; pclearbot; eauto with paco.
  econstructor. intros. edestruct REL; pclearbot; eauto with paco.
Qed.
(* end hide *)

Delimit Scope eq_itree_scope with eq_itree.

(** A notation of [eq_itree eq]. You can write [≅] using [[\cong]] in
    tex-mode *)

Open Scope itree.

Infix "≅" := (eq_itree eq) (at level 70) : itree_scope.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

Infix "≲" := (euttle eq) (at level 70) : itree_scope.

Section eqit_h.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(** [eqit] is a congruence for [itree] constructors. *)

Lemma eqit_Tau bl br hsim (t1 : itree E R1) (t2 : itree E R2) :
  eqit RR bl br hsim (Tau t1) (Tau t2) <-> eqit RR bl br hsim t1 t2.
Proof.
  split; intros H.
  - punfold H. red in H. simpl in *. pstep. red.
    remember (TauF t1) as ot1. remember (TauF t2) as ot2.
    hinduction H before RR; intros; subst; try inv Heqot1; try inv Heqot2; eauto.
    + pclearbot. punfold REL.
    + inv H; eauto.
    + inv H; eauto.
  - pstep. constructor; auto.
Qed.

Lemma eqit_Vis bl br {U} (e : E U)
      (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
      (forall u, eqit RR bl br bot2 (k1 u) (k2 u))
  <-> eqit RR bl br bot2 (Vis e k1) (Vis e k2).
Proof.
  split; intros H.
  - pstep. econstructor. left. left. eapply H.
  - punfold H. inv H; auto_inj_pair2; subst; auto.
    intros. pclearbot. eauto.
Qed.

Lemma eqit_Ret bl br hsim (r1 : R1) (r2 : R2) :
  RR r1 r2 <-> @eqit E _ _ RR bl br hsim (Ret r1) (Ret r2).
Proof.
  split; intros H.
  - pstep. constructor; auto.
  - punfold H. inversion H; auto_inj_pair2; subst; auto.
Qed.

(** *** "Up-to" principles for coinduction. *)

Inductive eqit_trans_clo bl1 br1 bl2 br2 (r : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| eqit_trans_clo_intro t1 t2 t1' t2'
      (EQVl: eqit eq bl1 br1 bot2 t1' t1)
      (EQVr: eqit eq bl2 br2 bot2 t2' t2)
      (RELATED: r t1' t2')
  : eqit_trans_clo bl1 br1 bl2 br2 r t1 t2
.
Hint Constructors eqit_trans_clo.

Lemma eqit_clo_trans (bl br br1 br2: bool)
    (COND1: br1 -> bl) (COND2: br2 -> br):
  eqit_trans_clo false br1 false br2 <3= cupaco2 (eqit_ RR bl br bot2) (cpn2 (eqit_ RR bl br bot2)).
Proof.
  (* TODO: use a tactic. *)
  econstructor. apply rclo2_clo.
  eapply cpn2_mon; [|intros; eapply rclo2_base; right; apply PR0].
  revert_until COND2. ucompat. econstructor; [pmonauto|].
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction RELATED before r; intros; clear t1' t2'.
  - remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
  - remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. econstructor. apply rclo2_clo. left. econstructor; cycle -1; eauto with paco.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; subst; try dependent destruction Heqx; try inv CHECK; eauto.
    remember (VisF e0 k3) as y.
    hinduction EQVr before r; intros; subst; try dependent destruction Heqy; try inv CHECK; eauto.
    econstructor. intros.
    left. apply rclo2_clo. left. pclearbot. econstructor; eauto with paco.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    pclearbot. punfold REL.
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. punfold REL.
Qed.

Inductive eqit_bind_clo bl br (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: eqit RU bl br bot2 t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : eqit_bind_clo bl br r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eqit_bind_clo.

Lemma eqit_clo_bind bl br: eqit_bind_clo bl br <3= cupaco2 (eqit_ RR bl br bot2) (cpn2 (eqit_ RR bl br bot2)).
Proof.
  (* TODO: use a tactic. *)
  econstructor. apply rclo2_clo.
  eapply cpn2_mon; [|intros; eapply rclo2_base; right; apply PR0].
  revert_until br. ucompat. econstructor; [pmonauto|].
  intros. dependent destruction PR.
  punfold EQV. unfold_eqit. rewrite !unfold_bind. 
  hinduction EQV before r; intros.
  - eapply eqitF_mono; [eapply REL0 |..]; eauto with paco.
  - simpl. pclearbot. econstructor. apply rclo2_clo. left.
    econstructor; eauto.
    intros. apply rclo2_clo. right. ustep.
    eapply eqit__mono; eauto with paco.
  - econstructor.
    intros x. pclearbot. left.
    apply rclo2_clo. left. econstructor; eauto.
    intros. apply rclo2_clo. right. ustep.
    eapply eqit__mono; eauto with paco.
  - econstructor; eauto. rewrite unfold_bind; eauto.
  - econstructor; eauto. rewrite unfold_bind; eauto.
Qed.

End eqit_h.

Hint Resolve eqit_cpn_compat : paco.

Arguments eqit_clo_trans : clear implicits.
Arguments eqit_clo_bind : clear implicits.

Hint Constructors eqit_trans_clo.
Hint Constructors eqit_bind_clo.

(** *** One-sided inversion *)

Lemma eqit_ret_inv1 {E R} (t : itree E R) r :
  t ≅ (Ret r) -> observe t = RetF r.
Proof.
  intros; punfold H; inv H; try inv CHECK; eauto.
Qed.

Lemma eqit_vis_inv1 {E R U} (t : itree E R) (e : E U) (k : U -> _) :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ forall u, k' u ≅ k u.
Proof.
  intros; punfold H; inv H; auto_inj_pair2; subst; try inv CHECK.
  eexists; split; eauto.
  intros. destruct (REL u); try contradiction; pclearbot; eauto.
Qed.

Lemma eqit_tau_inv1 {E R} (t t' : itree E R) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; punfold H; inv H; try inv CHECK; pclearbot; eauto.
Qed.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eqit_eq.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R : Type}.

Local Notation eqit := (@eqit E R R eq).

Global Instance Reflexive_eqitF bl br (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqitF eq bl br bot2 sim).
Proof.
  red. destruct x; constructor; eauto.
Qed.

Global Instance Symmetric_eqitF b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqitF eq b b bot2 sim).
Proof.
  red. induction 2; constructor; subst; eauto.
  intros. destruct (REL v); try contradiction; eauto.
Qed.

Global Instance Reflexive_eqit_ bl br (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqit_ eq bl br bot2 sim).
Proof. repeat red. reflexivity. Qed.

Global Instance Symmetric_eqit_ b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqit_ eq b b bot2 sim).
Proof. repeat red; symmetry; auto. Qed.

(** *** [eqit] is an equivalence relation *)

Global Instance Reflexive_eqit_gen bl br (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (cpaco2 (eqit_ eq bl br bot2) (cpn2 (eqit_ eq bl br bot2)) r rg).
Proof.
  repeat intro. eapply cpaco2_mon_bot; eauto with paco.
  revert x. ccofix CIH. cstep; intros.
  repeat red. destruct (observe x); eauto with paco.
Qed.

Global Instance Reflexive_eqit bl br : Reflexive (eqit bl br bot2).
Proof.
  red; intros. cinit. apply Reflexive_eqit_gen.
Qed.

Global Instance Symmetric_eqit b : Symmetric (eqit b b bot2).
Proof.
  cinit. ccofix CIH; cstep; intros.
  red. punfold H0. red in H0.
  induction H0; pclearbot; eauto 7 with paco.
Qed.

Global Instance Transitive_eqit (br: bool) : Transitive (eqit false br bot2).
Proof.
  under_forall cinit. intros.
  cclo eqit_clo_trans; eauto.
  econstructor; eauto with paco. reflexivity.
Qed.

Global Instance Equivalence_eqit : Equivalence (eqit false false bot2).
Proof.
  constructor; try typeclasses eauto.
Qed.

(** *** Congruence properties *)

Global Instance eqit_observe bl br:
  Proper (eqit bl br bot2 ==> going (eqit bl br bot2)) (@observe E R).
Proof.
  constructor; punfold H.
Qed.

Global Instance eqit_tauF bl br:
  Proper (eqit bl br bot2 ==> going (eqit bl br bot2)) (@TauF E R _).
Proof.
  constructor; pstep. econstructor. eauto.
Qed.

Global Instance eqit_VisF bl br {u} (e: E u) :
  Proper (pointwise_relation _ (eqit bl br bot2) ==> going (eqit bl br bot2)) (VisF e).
Proof.
  constructor; red in H. unfold eqit in *. pstep; econstructor; eauto.
Qed.

Global Instance observing_sub_eqit l r :
  subrelation (observing eq) (eqit l r bot2).
Proof.
  repeat red; intros. destruct H.
  pstep. red. rewrite H. apply Reflexive_eqitF. left. apply reflexivity.
Qed.

Global Instance eq_sub_eqit l r:
  subrelation (eqit false false bot2) (eqit l r bot2).
Proof.
  cinit. ccofix CIH. intros.
  punfold H0. cstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; try inv CHECK; pclearbot; eauto 7 with paco.
Qed.  

Global Instance eqit_sub_eutt l r:
  subrelation (eqit l r bot2) (eqit true true bot2).
Proof.
  cinit. ccofix CIH. intros.
  punfold H0. cstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; pclearbot; eauto 7 with paco.
Qed.  

(** ** Eta-expansion *)

Lemma itree_eta (t : itree E R) : t ≅ go (observe t).
Proof. apply observing_sub_eqit. econstructor. reflexivity. Qed.

Lemma itree_eta' (ot : itree' E R) : ot = observe (go ot).
Proof. reflexivity. Qed.

End eqit_eq.

Hint Resolve Reflexive_eqit Reflexive_eqit_gen : reflexivity.

(** ** Equations for core combinators *)

(* TODO (LATER): I keep these [...bind_] lemmas around temporarily
   in case I run some issues with slow typeclass resolution. *)

Lemma unfold_bind_ {E R S}
           (t : itree E R) (k : R -> itree E S) :
  ITree.bind t k ≅ ITree._bind k (fun t => ITree.bind t k) (observe t).
Proof. rewrite unfold_bind. reflexivity. Qed.

Lemma bind_ret_ {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k ≅ (k r).
Proof. rewrite bind_ret. reflexivity. Qed.

Lemma bind_tau_ {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof. rewrite bind_tau. reflexivity. Qed.

Lemma bind_vis_ {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof. rewrite bind_vis. reflexivity. Qed.

Lemma unfold_forever_ {E R S} (t : itree E R)
  : @ITree.forever E R S t ≅ (t >>= fun _ => Tau (ITree.forever t)).
Proof.
  rewrite itree_eta, (itree_eta (_ >>= _)).
  reflexivity.
Qed.

Instance eqit_cpaco {E R1 R2 RS} bl br r rg:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (cpaco2 (@eqit_ E R1 R2 RS bl br bot2) (cpn2 (eqit_ RS bl br bot2)) r rg).
Proof.
  repeat intro. cclo eqit_clo_trans; cycle -1.
  - econstructor; [symmetry|symmetry|]; eauto.
  - discriminate.
  - discriminate.
Qed.

Lemma eqit_bind' {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) bl br
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eqit RR bl br bot2 t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eqit RS bl br bot2 (k1 r1) (k2 r2)) ->
  @eqit E _ _ RS bl br bot2 (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. cinit. cclo eqit_clo_bind. unfold eqit in *.
  econstructor; eauto with paco.
Qed.

Instance eqit_bind {E R S} bl br :
  Proper (pointwise_relation _ (eqit eq bl br bot2) ==>
          eqit eq bl br bot2 ==>
          eqit eq bl br bot2) (@ITree.bind' E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

Instance eqit_bind_ {E R S} bl br k :
  Proper (going (eqit eq bl br bot2) ==>
          eqit eq bl br bot2) (@ITree._bind E R S k (@ITree.bind' E R S k)).
Proof.
  cinit. intros. destruct H0.
  rewrite (itree_eta' x), (itree_eta' y), <- !unfold_bind_.
  cclo eqit_clo_bind. econstructor; eauto.
  intros. subst. apply reflexivity.
Qed.

Lemma eqit_map {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) bl br
      (RS : S1 -> S2 -> Prop)
      f1 f2 t1 t2 :
  (forall r1 r2, RR r1 r2 -> RS (f1 r1) (f2 r2)) ->
  @eqit E _ _ RR bl br bot2 t1 t2 ->
  eqit RS bl br bot2 (ITree.map f1 t1) (ITree.map f2 t2).
Proof.
  unfold ITree.map; intros.
  eapply eqit_bind'; eauto.
  intros; pstep; constructor; auto.
Qed.

Instance eqit_eq_map {E R S} bl br :
  Proper (pointwise_relation _ eq ==>
          eqit eq bl br bot2 ==>
          eqit eq bl br bot2) (@ITree.map E R S).
Proof.
  repeat intro; eapply eqit_map; eauto.
  intros; subst; auto.
Qed.

Lemma bind_ret2 {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  cinit. ccofix CIH. intros.
  rewrite !unfold_bind_. cstep. repeat red.
  genobs s os. destruct os; simpl; eauto with paco.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  cinit. ccofix CIH. intros. rewrite !unfold_bind_.
  cstep. repeat red. destruct (observe s); simpl; eauto with paco.
  apply reflexivity.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret_. reflexivity.
Qed.

Lemma bind_map {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret_. reflexivity.
Qed.

Lemma map_bind {E X Y Z} (t: itree E X) (k: X -> itree E Y) (f: Y -> Z) :
  (ITree.map f (x <- t;; k x)) ≅ (x <- t;; ITree.map f (k x)).
Proof.
  intros.
  unfold ITree.map.
  rewrite bind_bind.
  reflexivity.
Qed.

Lemma map_ret {E A B} (f : A -> B) (a : A) :
    @ITree.map E _ _ f (Ret a) ≅ Ret (f a).
Proof.
  intros.
  unfold ITree.map.
  rewrite bind_ret; reflexivity.
Qed.

Hint Rewrite @bind_ret_ : itree.
Hint Rewrite @bind_tau_ : itree.
Hint Rewrite @bind_vis_ : itree.
Hint Rewrite @bind_map : itree.
Hint Rewrite @map_ret : itree.
Hint Rewrite @bind_ret2 : itree.
Hint Rewrite @bind_bind : itree.
