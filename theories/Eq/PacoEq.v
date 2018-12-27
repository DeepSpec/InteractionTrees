From Coq Require Import
(*     Program *)
     Relations.Relations.

From Paco Require Import paco2.

From ITree Require Import ITree.

Inductive bisimF' {E R} {it} (bisim: relation it) : relation (itreeF E R it) :=
| Bisim_Ret: forall r, bisimF' bisim (RetF r) (RetF r)
| Bisim_Tau: forall t1 t2
               (REL: bisim t1 t2),
             bisimF' bisim (TauF t1) (TauF t2)
| Bisim_Vis: forall u (e: E u) k1 k2
                (REL: forall v, bisim (k1 v) (k2 v)),
             bisimF' bisim (VisF e k1) (VisF e k2)
.

Inductive Ritree {E R}
  (bisim : relation (itreeF E R (itree E R)))
  (it it' : itree E R) : Prop :=
| Ritree_obs
    (_ : bisim it.(observe) it'.(observe))
  : Ritree bisim it it'
.

Definition bisimF {E R} (bisim: relation (itree E R))
: relation (itree E R) :=
  Ritree (bisimF' bisim).

Lemma bisimF_mono
  : forall E R, monotone2 (@bisimF E R).
Proof.
  unfold bisimF.
  compute. intros.
  constructor.
  inversion IN.
  inversion H; constructor; eauto.
Qed.
Hint Resolve bisimF_mono : paco.

Definition pbisim {E R} r := paco2 (@bisimF E R) r.
(* Hint Unfold pbisim. *)

Definition bisim {E R} := @pbisim E R bot2.
(* Hint Unfold bisim. *)

(*
Axiom bisim_eq: forall E R s t, @bisim E R s t -> s = t.
*)

(* these seem to be useful for proving forcing lemmas *)
Lemma bisim_ext {E T}
: forall r (a b : itree E T),
  bisimF (paco2 bisimF r) a b ->
  paco2 bisimF r a b.
Proof.
  intros.
  pfold.
  eapply bisimF_mono.
  eapply H.
  left. apply PR.
Qed.


Lemma bisim_ext' {E T}
: forall (a b : itree E T),
  bisim a b ->
  bisimF bisim a b.
Proof.
  intros.
  punfold H.
  eapply bisimF_mono. eapply H.
  intros.
  destruct PR. apply H0. destruct H0.
Qed.

Require Import Coq.Classes.RelationClasses.

Global Instance bisim_refl {E R} : Reflexive (@bisim E R).
Proof.
  pcofix CIH; intros.
  pfold. constructor. destruct (observe x); constructor; eauto.
Qed.


Goal forall {E T} (a : itree E T), bisim a a.
Proof.
  intros.
  Fail reflexivity. (* why does this not work? *)
  eapply bisim_refl.
Qed.

Lemma bisim_force_L {E T} r (a b : itree E T)
: paco2 bisimF r {| observe := a.(observe) |} b -> paco2 bisimF r a b.
Proof.
  inversion 1.
  econstructor.
  eapply LE.
  clear - SIM.
  inversion SIM. constructor. apply H.
Qed.


Lemma bisim_force_R {E T} r(a b : itree E T)
: paco2 bisimF r a {| observe := b.(observe) |} ->
  paco2 bisimF r a b.
Proof.
  inversion 1.
  econstructor.
  eapply LE.
  clear - SIM.
  inversion SIM. constructor. apply H.
Qed.

Lemma bisim_force_both {E T} r (a b : itree E T)
: paco2 bisimF r {| observe := a.(observe) |} {| observe := b.(observe) |} ->
  paco2 bisimF r a b.
Proof.
  intros.
  eapply bisim_force_L.
  eapply bisim_force_R.
  assumption.
Qed.

Ltac by_forcing :=
  eapply bisim_force_both; eapply bisim_refl.


Lemma interp_unfold {E F R} {f : eff_hom E F} (t : itree E R) :
  bisim (interp f t) (interp_match f (fun t' => interp f t') t).
Proof. by_forcing. Qed.



Lemma interp_ret {E F R} {f : eff_hom E F} (x: R):
  bisim (interp f (Ret x)) (Ret x).
Proof. by_forcing. Qed.

Lemma interp_tau {E F R} {f : eff_hom E F} (t: itree E R):
  bisim (interp f (Tau t)) (Tau (interp f t)).
Proof. by_forcing. Qed.

Lemma interp_vis {E F R} {f : eff_hom E F} U (e: E U) (k: U -> itree E R) :
  bisim (interp f (Vis e k)) (x <- (f _ e);; Tau (interp f (k x))).
Proof. by_forcing. Qed.

Lemma bind_unfold {E R} U t (k: U -> itree E R) :
  bisim (ITree.bind t k) (ITree.bind_match k (ITree.bind' k) t).
Proof. by_forcing. Qed.

Lemma bind_ret {E R} U x (k: U -> itree E R) :
  bisim (Ret x >>= k) (k x).
Proof. by_forcing. Qed.

Lemma bind_tau {E R} U t (k: U -> itree E R) :
  bisim (Tau t >>= k) (Tau (t >>= k)).
Proof. by_forcing. Qed.

Lemma bind_vis {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  bisim (Vis e ek >>= k) (Vis e (fun x => ek x >>= k)).
Proof. by_forcing. Qed.

Lemma bind_assoc E A B C (t: itree E A) (k1: A -> itree E B) (k2: B -> itree E C):
  bisim ((t >>= k1) >>= k2) (t >>= fun r => k1 r >>= k2).
Proof.
  revert A B t k1 k2.
  pcofix CIH. intros.
  eapply bisim_force_both.
  simpl.
  cbv beta iota zeta delta [ ITree.bind ITree.bind' ].
  simpl.
  cbv beta iota zeta.
  destruct (observe t).
  - compute.
    eapply paco2_mon; [eapply bisim_refl|contradiction].
  - simpl.
    pfold.
    constructor. constructor.
    right.
    eapply (CIH _ _ t0 k1 k2).
  - simpl.
    pfold.
    do 2 constructor. intros.
    right.
    eapply (CIH _ _ (k v) k1 k2).
Qed.

Inductive prefix_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| pbc_intro U (t: itree E U) k1 k2
      (REL: forall v, r (k1 v) (k2 v))
  : prefix_clo r (t >>= k1) (t >>= k2)
.
Hint Constructors prefix_clo.

(* missing `weak_respectful2`? *)
Lemma prefix_clo_bisim_respectful E R: weak_respectful2 (@bisimF E R) prefix_clo.
Proof.
  econstructor; try pmonauto.
  intros. dependent destruction PR.
  destruct t, observe.
  - rewrite !bind_ret. eapply bisimF_mono; eauto using rclo2.
  - rewrite !bind_tau. eauto 7 using rclo2.
  - rewrite !bind_vis. eauto 7 using rclo2.
Qed.

Lemma interp_bind {E F R S}
      (f : eff_hom E F) (t : itree E R) (k : R -> itree E S) :
   (interp f (t >>= k)) = (interp f  t >>= fun r => interp f (k r)).
Proof.
  apply bisim_eq.
  pupto2_init.
  revert R t k.
  pcofix CIH. intros.
  destruct t, observe.
  - rewrite interp_ret, !bind_ret. pupto2_final.
    eapply paco2_mon; [eapply bisim_refl|contradiction].
  - rewrite interp_tau, !bind_tau, interp_tau.
    pupto2_final.
  - rewrite interp_vis, !bind_vis, interp_vis, bind_assoc.
    pupto2 (prefix_clo_bisim_respectful F S).
    econstructor. intros.
    rewrite bind_tau.
    pupto2_final.
Qed.