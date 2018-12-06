(* Coinductively defined equality on itrees,
   also called: strong bisimulation, extensional equality.
 *)

(* TODO: paco-fy this *)

From Coq Require Import
     Setoid
     Morphisms
     ProofIrrelevance.

From ITree Require Import
     ITree.

Section eq_itree.
  Context {E : Type -> Type} {R : Type}.

  Inductive eq_itreeF {t} (sim : t -> t -> Prop) : relation (@itreeF E R t) :=
  | EqRet : forall x, eq_itreeF sim (RetF x) (RetF x)
  | EqTau : forall m1 m2,
      sim m1 m2 -> eq_itreeF sim (TauF m1) (TauF m2)
  | EqVis : forall {u} (e : E u) k1 k2,
      (forall y, sim (k1 y) (k2 y)) ->
      eq_itreeF sim (VisF e k1) (VisF e k2)
  .

  Global Instance Reflexive_eq_itreeF {t} {sim : t -> t -> Prop}
  : Reflexive sim -> Reflexive (@eq_itreeF t sim).
  Proof.
    red. destruct x.
    - constructor.
    - constructor. reflexivity.
    - constructor. intro; eapply H.
  Qed.

  Global Instance Symmetric_eq_itreeF {t} {sim : t -> t -> Prop}
  : Symmetric sim -> Symmetric (@eq_itreeF t sim).
  Proof.
    red. inversion 2.
    - constructor.
    - constructor. eauto.
    - constructor. intros; eapply H. eapply H1.
  Qed.

  Global Instance Transitive_eq_itreeF {t} {sim : t -> t -> Prop}
  : Transitive sim -> Transitive (@eq_itreeF t sim).
  Proof.
    red. inversion 2.
    - inversion 1. constructor.
    - inversion 1. constructor. eauto.
    - inversion 1.
      (* todo(gmm): i don't think these are strictly necessary *)
      eapply inj_pair2 in H7.
      eapply inj_pair2 in H8.
      subst. constructor. eauto.
  Qed.

  CoInductive eq_itree (l r : itree E R) : Prop :=
  { observe_eq : eq_itreeF eq_itree l.(observe) r.(observe) }.

End eq_itree.


Delimit Scope eq_itree_scope with eq_itree.
(* note(gmm): overriding `=` seems like a bad idea *)
Notation "t1 ≅ t2" := (eq_itree t1%itree t2%itree) (at level 70).
(* you can write ≅ using \cong in tex-mode *)

Instance Reflexive_eq_itree {E R} : Reflexive (@eq_itree E R).
Proof.
  cofix self.
  intro.
  constructor.
  destruct (observe x).
  - constructor.
  - constructor. eapply self.
  - constructor. intros. eapply self.
Qed.

Instance Symmetric_eq_itree {E R} : Symmetric (@eq_itree E R).
Proof.
  cofix self.
  intros x y H.
  constructor. eapply observe_eq in H.
  destruct H; constructor.
  - apply self. assumption.
  - intros. eapply self. eapply H.
Qed.

Instance Transitive_eq_itree {E R} : Transitive (@eq_itree E R).
Proof.
  cofix self.
  intros x y z; intros.
  eapply observe_eq in H.
  eapply observe_eq in H0.
  constructor.
  generalize dependent (observe x); generalize dependent (observe y);
    generalize dependent (observe z).
  inversion 1; subst.
  - clear. eauto.
  - inversion 1. subst.
    constructor.
    eapply self. eassumption. eassumption.
  - inversion 1.
    subst.
    eapply inj_pair2 in H5. subst.
    eapply inj_pair2 in H6. subst.
    constructor.
    intros.
    eapply self. eapply H4. eapply H.
Qed.

Instance Equivalence_eq_itree {E R} :
  Equivalence (@eq_itree E R).
Proof.
  constructor; typeclasses eauto.
Qed.

Instance Proper_bind {E R S} :
  Proper (eq_itree ==> pointwise_relation _ eq_itree ==> eq_itree)
         (@bind E R S).
Proof.
  intros s1 s2 Hs k1 k2 Hk.
  generalize dependent s2.
  generalize dependent s1.
  cofix core_bind_mor.
  intros.
  constructor. simpl. unfold bind_match.
  inversion Hs.
  do 2 rewrite observe_bind.
  inversion observe_eq0.
  { eapply Hk. }
  { constructor.
    eapply core_bind_mor. eapply H1. }
  { constructor; intros.
    eapply core_bind_mor. eapply H1. }
Defined.

Lemma ret_bind {E R S} (r : R) :
  forall k : R -> itree E S,
    eq_itree (Ret r >>= k) (k r).
Proof.
  constructor; cbn; reflexivity.
Qed.

Lemma bind_ret {E R} :
  forall s : itree E R,
    (s >>= (fun x => Ret x)) ≅ s.
Proof.
  cofix bind_ret.
  intros s; constructor; cbn.
  destruct (observe s); constructor; eauto.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ( (s >>= k) >>= h
      ≅
      s >>= (fun r => k r >>= h)
    ).
Proof.
  cofix bind_bind.
  intros s k h.
  constructor; cbn.
  destruct (observe s).
  - reflexivity.
  - constructor.
    eapply (bind_bind t k h).
  - constructor.
    intros.
    apply (bind_bind (k0 y) k h).
Qed.

Lemma map_map : forall {E R S T} (f : R -> S) (g : S -> T) (t : itree E R),
    map g (map f t) ≅ map (fun x => g ( f x)) t.
Proof.
  intros E R S T f g.
  cofix ch.
  intros t.
  econstructor; cbn.
  destruct (observe t); cbn; econstructor; eauto.
Qed.

(*
Import Hom.

Lemma hom_bind {E1 E2 R S} (f : E1 ~> itree E2)
      (s : itree E1 R) (k : R -> itree E1 S) :
  ((hom f _ (s >>= k))
   =
   (hom f _ s >>= fun x => hom f _ (k x)))%eq_itree.
Proof.
  simpl.
  generalize dependent s.
  cofix hom_bind.
  intros s.
  do 2 rewrite hom_def.
  destruct s.
  - do 2 rewrite bind_def.
    constructor. reflexivity.
  - rewrite bind_def.
    simpl.
    remember (f _ e) as t0 eqn:foo.
    clear foo.
    generalize dependent t0.
    (* nested cofix... *)
    cofix bind_assoc.
    intros t0.
    rewrite (bind_def t0).
    rewrite (bind_def (bind_itree _ _)).
    destruct t0; constructor.
    + apply hom_bind.
    + intros x0.
      apply bind_assoc.
    + apply bind_assoc.
  - do 2 rewrite bind_def.
    constructor.
    apply hom_bind.
Defined.

Lemma hom_ret {E1 E2 R} (f : E1 ~> itree E2) (r : R) :
  hom f _ (Ret r) = Ret r.
Proof.
  rewrite hom_def.
  constructor.
Defined.

Lemma hom_while {E1 E2 S} (phi : E1 ~> itree E2)
      (f : S -> bool) (body : S -> itree E1 S) : forall (s : S),
    (hom phi _ (while f body s)
     =
     while f (fun s' => hom phi _ (body s')) s)%eq_itree.
Proof.
  cofix hom_while.
  intros s.
  do 2 rewrite while_loop_unfold.
  destruct (f s); simpl.
  - remember (body s) as t eqn:Et; clear Et; generalize dependent t.
    cofix bind_hom.
    intros t.
    rewrite hom_def.
    destruct t.
    + rewrite (bind_def (hom _ _ _)).
      constructor.
      apply hom_while.
    + rewrite hom_def.
      rewrite (bind_def (Vis _ _)).
      simpl.
      remember (phi _ _) as u eqn:Eu; clear Eu; generalize dependent u.
      cofix bind_phi.
      intros u.
      do 2 rewrite bind_def.
      destruct u;
        constructor;
        [ auto | | ];
        try intro; apply bind_phi.
    + rewrite (bind_def (hom _ _ _)).
      constructor.
      apply bind_hom.
  - rewrite hom_def; constructor.
Qed.
*)
