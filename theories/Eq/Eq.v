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

CoInductive eq_itree {E : Type -> Type} {R} : relation (itree E R) :=
| EqRet : forall x, eq_itree (Ret x) (Ret x)
| EqTau : forall m1 m2,
    eq_itree m1 m2 -> eq_itree (Tau m1) (Tau m2)
| EqVis : forall {u} (e : E u) k1 k2,
    (forall y, eq_itree (k1 y) (k2 y)) ->
    eq_itree (Vis e k1) (Vis e k2)
.

Delimit Scope eq_itree_scope with eq_itree.
Notation "t1 = t2" := (eq_itree t1%itree t2%itree) : eq_itree_scope.

(* Axiom EqM_eq : forall a b, EqM a b -> a = b. *)

Instance Reflexive_eq_itree {E R} : Reflexive (@eq_itree E R).
Proof.
  cofix self.
  intros []; constructor; auto.
Qed.

Instance Symmetric_eq_itree {E R} : Symmetric (@eq_itree E R).
Proof.
  cofix self.
  intros x y []; constructor; auto.
Qed.

Instance Transitive_eq_itree {E R} : Transitive (@eq_itree E R).
Proof.
  cofix self.
  intros x y z [] Hyz; inversion Hyz.
  - constructor.
  - constructor; eapply self; eauto.
  - apply inj_pair2 in H2.
    subst.
    apply inj_pair2 in H3.
    subst.
    constructor.
    intro y'.
    eapply self; auto.
Qed.

Instance Equivalence_eq_itree {E R} :
  Equivalence (@eq_itree E R).
Proof.
  constructor; typeclasses eauto.
Qed.

Add Parametric Relation {E R} : (itree E R) eq_itree
  reflexivity proved by Reflexive_eq_itree
  symmetry proved by Symmetric_eq_itree
  transitivity proved by Transitive_eq_itree
    as eq_itree_rel.

Add Parametric Morphism {E R S} : (@bind E R S)
    with signature
    (eq_itree ==> pointwise_relation _ eq_itree ==> eq_itree)
      as core_bind_mor.
Proof.
  intros s1 s2 Hs k1 k2 Hk.
  generalize dependent s2.
  generalize dependent s1.
  cofix core_bind_mor.
  intros.
  rewrite (match_itree (s1 >>= _)).
  rewrite (match_itree (s2 >>= _)).
  destruct Hs; simpl.
  - do 2 rewrite <- match_itree; apply (Hk x).
  - constructor; apply core_bind_mor; auto.
  - constructor; intro y; apply core_bind_mor; auto.
Defined.

(* [ret_bind] in basics *)

Lemma bind_ret {E R} :
  forall s : itree E R,
    (s >>= Ret = s)%eq_itree.
Proof.
  cofix bind_ret.
  intros s.
  rewrite (match_itree (s >>= _)).
  destruct s; constructor; auto.
  - apply bind_ret.
  - intro y. apply bind_ret.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ( (s >>= k) >>= h
      =
      s >>= (fun r => k r >>= h)
    )%eq_itree.
Proof.
  cofix bind_bind.
  intros s k h.
  do 2 rewrite (match_bind s).
  destruct s; simpl; auto.
  - reflexivity.
  - rewrite (match_bind (Tau _)).
    constructor. apply bind_bind.
  - rewrite (match_bind (Vis _ _)).
    constructor. intro y. apply bind_bind.
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
