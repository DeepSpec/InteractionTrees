(** Properties of [Fix.mrec] and [Fix.rec]. *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.Basics
     Basics.Functions
     Core.ITree
     Eq.Eq
     Eq.UpToTaus
     Eq.SimUpToTaus
     Indexed.Sum
     Indexed.OpenSum
     Interp.Interp
     Interp.MorphismsFacts.

Import ITreeNotations.

Section Facts.

Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

(** Unfolding of [interp_mrec]. *)

Definition interp_mrecF R (ot : itreeF (D +' E) R _) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec ctx _ t)
  | VisF e k => Tau
    match e with
    | inl1 d => interp_mrec ctx _ (ctx _ d >>= k)
    | inr1 e => Vis e (fun x => interp_mrec ctx _ (k x))
    end
  end.

Lemma unfold_interp_mrec R (t : itree (D +' E) R) :
  interp_mrec ctx _ t ≅ interp_mrecF _ (observe t).
Proof.
  unfold interp_mrec.
  rewrite unfold_aloop'.
  destruct observe; cbn.
  - reflexivity.
  - rewrite ret_bind_; reflexivity. (* TODO: ret_bind, vis_bind are sloooow *)
  - destruct e; cbn.
    + rewrite ret_bind_; reflexivity.
    + rewrite vis_bind_. pfold; constructor. left.
      pfold; constructor.
      left. rewrite ret_bind.
      apply reflexivity.
Qed.

Lemma ret_mrec {T} (x: T) :
  interp_mrec ctx _ (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp_mrec; reflexivity. Qed.

Lemma tau_mrec {T} (t: itree _ T) :
  interp_mrec ctx _ (Tau t) ≅ Tau (interp_mrec ctx _ t).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_right {T U} (e : E U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx _ (Vis (inr1 e) k) ≅
  Tau (Vis e (fun x => interp_mrec ctx _ (k x))).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_left {T U} (d : D U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx _ (Vis (inl1 d) k) ≅
  Tau (interp_mrec ctx _ (ITree.bind (ctx _ d) k)).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Hint Rewrite @ret_mrec : itree.
Hint Rewrite @vis_mrec_left : itree.
Hint Rewrite @vis_mrec_right : itree.
Hint Rewrite @tau_mrec : itree.

Instance eq_itree_mrec {R} :
  Proper (eq_itree eq ==> eq_itree eq) (interp_mrec ctx R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  pupto2_final.
  punfold H0. inv H0; pclearbot; [| |destruct e].
  - apply reflexivity.
  - pfold. econstructor. eauto.
  - pfold. econstructor. apply pointwise_relation_fold in REL.
    right. eapply CIH. rewrite REL. reflexivity.
  - pfold. econstructor. left; pfold; constructor. auto.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx _ (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx _ t) (fun x => interp_mrec ctx _ (k x)).
Proof.
  intros. pupto2_init; revert t k; pcofix CIH; intros.
  rewrite (unfold_interp_mrec _ t), (unfold_bind t).
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree;
    try rewrite <- bind_bind.
  1: { pupto2_final; apply reflexivity. }
  all: try (pfold; econstructor; eauto).
  intros.
  pupto2_final. left; pfold; constructor. auto.
Qed.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx _ c ≈ interp (Sum1.elim (C:=itree E) (mrec ctx) ITree.liftE) _ c.
Proof.
  repeat intro. pupto2_init. revert_until T. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto 8.
  - rewrite interp_mrec_bind.
    pfold; constructor.
    pupto2 eutt_nested_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; eauto.

  - unfold ITree.liftE. rewrite vis_bind_.
    pfold; constructor.
    pupto2_final.
    left; pfold; econstructor.
    left.
    rewrite ret_bind_. auto.
Qed.

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx _ d ≈ interp (Sum1.elim (C:=itree E) (mrec ctx) ITree.liftE) _ (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

End Facts.

Lemma rec_unfold {E A B} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec f x ≈ interp (Sum1.elim (C:=itree E) (calling' (rec f)) ITree.liftE) _ (f x).
Proof.
  unfold rec.
  rewrite mrec_as_interp.
  eapply eutt_interp_gen.
  - do 2 red. intros ? [[] | ]; reflexivity.
  - reflexivity.
Qed.

Notation loop_once_ f loop_ :=
  (loop_once f (fun cb => Tau (loop_ f%function cb))).

Lemma unfold_loop'' {E A B C} (f : C + A -> itree E (C + B)) (x : C + A) :
    observe (loop_ f x)
  = observe (loop_once f (fun cb => Tau (loop_ f cb)) x).
Proof. reflexivity. Qed.

Lemma unfold_loop' {E A B C} (f : C + A -> itree E (C + B)) (x : C + A) :
    loop_ f x
  ≅ loop_once f (fun cb => Tau (loop_ f cb)) x.
Proof.
  rewrite itree_eta, (itree_eta (loop_once _ _ _)).
  reflexivity.
Qed.

Lemma unfold_loop {E A B C} (f : C + A -> itree E (C + B)) (x : C + A) :
    loop_ f x
  ≈ loop_once f (loop_ f) x.
Proof.
  rewrite unfold_loop'.
  apply eutt_bind; try reflexivity.
  intros []; try reflexivity.
  rewrite tau_eutt; reflexivity.
Qed.

(* Equations for a traced monoidal category *)

Lemma loop_natural_l {E A A' B C} (f : A -> itree E A')
      (body : C + A' -> itree E (C + B)) (a : A) :
    ITree.bind (f a) (loop body)
  ≅ loop (fun ca =>
      match ca with
      | inl c => Ret (inl c)
      | inr a => ITree.map inr (f a)
      end >>= body) a.
Proof.
  unfold loop.
  rewrite unfold_loop'; unfold loop_once.
  unfold ITree.map. autorewrite with itree.
  eapply eq_itree_bind; try reflexivity.
  intros a' _ []. autorewrite with itree.
  remember (inr a') as ca eqn:EQ; clear EQ a'.
  pupto2_init. revert ca; clear; pcofix self; intro ca.
  rewrite unfold_loop'; unfold loop_once.
  pupto2 @eq_itree_clo_bind; econstructor; try reflexivity.
  intros [c | b]; intros; subst.
  - match goal with
    | [ |- _ _ (Tau (loop_ ?f _)) ] => rewrite (unfold_loop' f)
    end.
    unfold loop_once_.
    rewrite ret_bind_. (* TODO: [ret_bind] doesn't work. *)
    pfold; constructor; auto.
  - pfold; constructor; auto.
Qed.

Lemma loop_natural_r {E A B B' C} (f : B -> itree E B')
      (body : C + A -> itree E (C + B)) (a : A) :
    loop body a >>= f
  ≅ loop (fun ca => body ca >>= fun cb =>
      match cb with
      | inl c => Ret (inl c)
      | inr b => ITree.map inr (f b)
      end) a.
Proof.
  unfold loop.
  remember (inr a) as ca eqn:EQ; clear EQ a.
  pupto2_init. revert ca; clear; pcofix self; intro ca.
  rewrite !unfold_loop'; unfold loop_once.
  rewrite !bind_bind.
  pupto2 @eq_itree_clo_bind; econstructor; try reflexivity.
  intros [c | b]; intros; subst.
  - rewrite ret_bind_, tau_bind_.
    pfold; constructor; auto.
  - autorewrite with itree.
    pupto2_final; apply reflexivity.
Qed.

Lemma loop_dinatural {E A B C C'} (f : C -> itree E C')
      (body : C' + A -> itree E (C + B)) (a : A) :
    loop (fun c'a => body c'a >>= fun cb =>
      match cb with
      | inl c => Tau (ITree.map inl (f c))
      | inr b => Ret (inr b)
      end) a
  ≅ loop (fun ca =>
      match ca with
      | inl c => f c >>= fun c' => Tau (Ret (inl c'))
      | inr a => Ret (inr a)
      end >>= body) a.
Proof.
  unfold loop.
  do 2 rewrite unfold_loop'; unfold loop_once.
  autorewrite with itree.
  eapply eq_itree_bind; try reflexivity.
  clear a; intros cb _ [].
  pupto2_init. revert cb; pcofix self; intros.
  destruct cb as [c | b].
  - rewrite tau_bind.
    pfold; constructor; pupto2_final; left.
    rewrite map_bind.
    rewrite (unfold_loop' _ (inl c)); unfold loop_once.
    autorewrite with itree.
    pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
    intros c'; intros; subst.
    rewrite tau_bind.
    rewrite ret_bind_.
    rewrite unfold_loop'; unfold loop_once.
    rewrite bind_bind.
    pfold; constructor.
    pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
    intros; subst. eauto.
  - rewrite ret_bind.
    pupto2_final; apply reflexivity.
Qed.

Lemma vanishing1 {E A B} (f : Empty_set + A -> itree E (Empty_set + B))
      (a : A) :
  loop f a ≅ ITree.map sum_empty_l (f (inr a)).
Proof.
  unfold loop.
  rewrite unfold_loop'; unfold loop_once, ITree.map.
  eapply eq_itree_bind; try reflexivity.
  intros [[]| b] _ []; reflexivity.
Qed.

Lemma vanishing2 {E A B C D} (f : D + (C + A) -> itree E (D + (C + B)))
      (a : A) :
    loop (loop f) a
  ≅ loop (fun dca => ITree.map sum_assoc_l (f (sum_assoc_r dca))) a.
Proof.
  unfold loop; rewrite 2 unfold_loop'; unfold loop_once.
  rewrite map_bind.
  rewrite unfold_loop'; unfold loop_once.
  rewrite bind_bind.
  eapply eq_itree_bind; try reflexivity.
  clear a; intros dcb _ [].
  pupto2_init. revert dcb; pcofix self; intros.
  destruct dcb as [d | [c | b]]; simpl.
  - (* d *)
    rewrite tau_bind.
    rewrite 2 unfold_loop'; unfold loop_once.
    autorewrite with itree.
    pfold; constructor.
    pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
    intros; subst. auto.
  - (* c *)
    rewrite ret_bind.
    rewrite 2 unfold_loop'; unfold loop_once.
    rewrite unfold_loop'; unfold loop_once.
    autorewrite with itree.
    pfold; constructor.
    pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
    intros; subst. auto.
  - (* b *)
    rewrite ret_bind.
    pupto2_final; apply reflexivity.
Qed.

Lemma superposing1 {E A B C D D'} (f : C + A -> itree E (C + B))
      (g : D -> itree E D') (a : A) :
    ITree.map inl (loop f a)
  ≅ loop (fun cad =>
      match cad with
      | inl c => ITree.map (sum_bimap id inl) (f (inl c))
      | inr (inl a) => ITree.map (sum_bimap id inl) (f (inr a))
      | inr (inr d) => ITree.map (inr ∘ inr) (g d)
      end) (inl a).
Proof.
  unfold loop.
  remember (inr a) as inra eqn:Hr.
  remember (inr (inl a)) as inla eqn:Hl.
  assert (Hlr : match inra with
                | inl c => inl c
                | inr a => inr (inl a)
                end = inla).
  { subst; auto. }
  clear a Hl Hr.
  unfold ITree.map.
  pupto2_init. revert inla inra Hlr; pcofix self; intros.
  rewrite 2 unfold_loop'; unfold loop_once.
  rewrite bind_bind.
  destruct inra as [c | a]; subst.
  - rewrite bind_bind; setoid_rewrite ret_bind_.
    pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
    intros [c' | b]; simpl; intros; subst.
    + rewrite tau_bind. pfold; constructor.
      pupto2_final. auto.
    + rewrite ret_bind. pupto2_final; apply reflexivity.
  - rewrite bind_bind; setoid_rewrite ret_bind_.
    pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
    intros [c' | b]; simpl; intros; subst.
    + rewrite tau_bind. pfold; constructor.
      pupto2_final. auto.
    + rewrite ret_bind_. pupto2_final; apply reflexivity.
Qed.

Lemma superposing2 {E A B C D D'} (f : C + A -> itree E (C + B))
      (g : D -> itree E D') (d : D) :
    ITree.map inr (g d)
  ≅ loop (fun cad =>
      match cad with
      | inl c => ITree.map (sum_bimap id inl) (f (inl c))
      | inr (inl a) => ITree.map (sum_bimap id inl) (f (inr a))
      | inr (inr d) => ITree.map (inr ∘ inr) (g d)
      end) (inr d).
Proof.
  unfold loop; rewrite unfold_loop'; unfold loop_once.
  rewrite map_bind; unfold ITree.map.
  eapply eq_itree_bind; try reflexivity.
  intros d' _ []. reflexivity.
Qed.

Lemma yanking {E A} (a : A) :
  @loop E _ _ _ (fun aa => Ret (sum_comm aa)) a ≅ Tau (Ret a).
Proof.
  rewrite itree_eta; cbn; apply eq_itree_tau.
  rewrite itree_eta; reflexivity.
Qed.

Definition sum_map1 {A B C} (f : A -> B) (ac : A + C) : B + C :=
  match ac with
  | inl a => inl (f a)
  | inr c => inr c
  end.

Instance eq_itree_loop {E A B C} :
  Proper ((eq ==> eq_itree eq) ==> eq ==> eq_itree eq) (@loop E A B C).
Proof.
  repeat intro; subst.
  unfold loop.
  remember (inr _) as ca eqn:EQ; clear EQ y0.
  pupto2_init. revert ca; pcofix self; intros.
  rewrite 2 unfold_loop'; unfold loop_once.
  pupto2 eq_itree_clo_bind; econstructor; try auto.
  intros [c | b]; intros; subst; pfold; constructor; auto.
Qed.

Section eutt_loop.

Context {E : Type -> Type} {A B C : Type}.
Variables f1 f2 : C + A -> itree E (C + B).
Hypothesis eutt_f : forall ca, sutt eq (f1 ca) (f2 ca).

Inductive loop_preinv (t1 t2 : itree E B) : Prop :=
| loop_inv_main ca :
    t1 ≅ loop_ f1 ca ->
    t2 ≅ loop_ f2 ca ->
    loop_preinv t1 t2
| loop_inv_bind u1 u2 :
    sutt eq u1 u2 ->
    t1 ≅ (cb <- u1;;
       match cb with
       | inl c => Tau (loop_ f1 (inl c))
       | inr b => Ret b
       end) ->
    t2 ≅ (cb <- u2;;
       match cb with
       | inl c => Tau (loop_ f2 (inl c))
       | inr b => Ret b
       end) ->
    loop_preinv t1 t2
.
Hint Constructors loop_preinv.

Lemma eutt_loop_inv_main_step (ca : C + A) t1 t2 :
  t1 ≅ loop_ f1 ca ->
  t2 ≅ loop_ f2 ca ->
  suttF1 eq (going loop_preinv) (observe t1) (observe t2).
Proof.
  intros H1 H2.
  rewrite unfold_loop' in H1.
  rewrite unfold_loop' in H2.
  unfold loop_once.
  specialize (eutt_f ca).
  apply sutt_is_sutt1 in eutt_f.
  punfold eutt_f.
  unfold loop_once in H1.
  unfold loop_once in H2.
  rewrite unfold_bind in H1.
  rewrite unfold_bind in H2.

  revert t1 t2 H1 H2.
  induction eutt_f; intros z1 z2 H1 H2.

  - subst; destruct r2.
    + apply eq_itree_tau_inv1 in H1.
      destruct H1 as [t1' [Ht1 Ht1']].
      apply eq_itree_tau_inv1 in H2.
      destruct H2 as [t2' [Ht2 Ht2']].
      rewrite Ht1, Ht2.
      repeat constructor.
      econstructor; try rewrite <- itree_eta; eassumption.
    + apply eq_itree_ret_inv1 in H1.
      apply eq_itree_ret_inv1 in H2.
      rewrite H1, H2.
      auto.

  - pclearbot. apply eq_itree_vis_inv1 in H1.
    apply eq_itree_vis_inv1 in H2.
    destruct H1 as [k01 [Hk1 Hk1']].
    destruct H2 as [k02 [Hk2 Hk2']].
    rewrite Hk1, Hk2.
    constructor; intros.
    repeat constructor.
    eapply loop_inv_bind.
    + apply sutt_is_sutt1, SUTTK.
    + rewrite <- itree_eta; auto.
    + rewrite <- itree_eta; auto.

  - apply eq_itree_tau_inv1 in H2.
    destruct H2 as [t2' [Ht2 Ht2']].
    rewrite Ht2.
    constructor.
    apply IHs; auto. rewrite <- unfold_bind; auto.

  - pclearbot.
    replace ot2 with (observe (go ot2)) in *.
    rewrite <- unfold_bind in H2.
    apply eq_itree_tau_inv1 in H1.
    destruct H1 as [t1' [Ht1 Ht1']].
    rewrite Ht1.
    repeat constructor.
    eapply loop_inv_bind.
    + apply sutt_is_sutt1. eauto.
    + rewrite <- itree_eta; auto.
    + rewrite <- itree_eta; auto.
    + auto.
Qed.

Lemma eutt_loop_inv ot1 ot2 :
  loop_preinv (go ot1) (go ot2) -> paco2 (suttF1 eq) bot2 ot1 ot2.
Proof.
  intros HH.
  revert ot1 ot2 HH; pcofix self; intros. pfold.
  destruct HH as [ca H1 H2 | u1 u2 Hu H1 H2].
  - eapply monotone_suttF1.
    + eapply (eutt_loop_inv_main_step ca (go ot1) (go ot2)); eauto.
    + intros ? ? []. right. eapply self; eauto.
  - apply sutt_is_sutt1 in Hu.
    punfold Hu.
    rewrite unfold_bind in H1.
    rewrite unfold_bind in H2.
    revert ot1 ot2 H1 H2; induction Hu; intros.

    + subst; destruct r2.
      * apply eq_itree_tau_inv1 in H1.
        apply eq_itree_tau_inv1 in H2.
        simpl in H1, H2.
        destruct H1 as [? []], H2 as [? []].
        subst.
        do 2 constructor. right.
        apply self.
        eapply loop_inv_main; rewrite <- itree_eta; eauto.
      * apply eq_itree_ret_inv1 in H1.
        apply eq_itree_ret_inv1 in H2.
        simpl in H1, H2. subst; auto.

    + pclearbot.
      apply eq_itree_vis_inv1 in H1.
      apply eq_itree_vis_inv1 in H2.
      simpl in H1, H2.
      destruct H1 as [? []], H2 as [? []].
      subst; constructor.
      right. apply self.
      eapply loop_inv_bind.
      * apply sutt_is_sutt1. eapply SUTTK.
      * rewrite <- itree_eta; auto.
      * rewrite <- itree_eta; auto.

    + apply eq_itree_tau_inv1 in H2.
      simpl in H2.
      destruct H2 as [t2' [Ht2 Ht2']].
      rewrite Ht2.
      constructor.
      apply IHHu; auto.
      rewrite <- itree_eta, <- unfold_bind; auto.

    + pclearbot.
      replace ot2 with (observe (go ot2)) in *.
      rewrite <- unfold_bind in H2.
      apply eq_itree_tau_inv1 in H1.
      simpl in H1.
      destruct H1 as [t1' [Ht1 Ht1']].
      rewrite Ht1.
      constructor.
      right; apply self.
      eapply loop_inv_bind.
      * apply sutt_is_sutt1.
        eapply EQTAUS.
      * rewrite <- itree_eta; auto.
      * auto.
      * auto.
Qed.

End eutt_loop.

Instance sutt_loop {E A B C} :
  Proper (pointwise_relation _ (sutt eq) ==> eq ==> sutt eq) (@loop E A B C).
Proof.
  repeat intro; subst. apply sutt_is_sutt1.

  eapply eutt_loop_inv.
  - eauto.
  - unfold loop; econstructor; rewrite <- itree_eta; reflexivity.
Qed.

Instance eutt_loop {E A B C} :
  Proper (pointwise_relation _ (eutt eq) ==> eq ==> eutt eq) (@loop E A B C).
Proof.
  repeat intro; subst.
  repeat red in H.
  eapply sutt_eutt.
  - eapply sutt_loop; auto.
    repeat intro; subst.
    apply eutt_sutt; auto.
  - eapply paco2_mon_gen.
    + eapply sutt_loop; auto.
      repeat intro.
      apply eutt_sutt. apply symmetry; auto.
    + intros. eapply monotone_sutt_RR; try eassumption.
      red; auto.
    + auto.
Qed.

Lemma interp_loop {E F} (f : E ~> itree F) {A B C}
      (t : C + A -> itree E (C + B)) ca :
  interp f _ (loop_ t ca) ≅ loop_ (fun ca => interp f _ (t ca)) ca.
Proof.
  pupto2_init. revert ca. pcofix CIH. intros.
  unfold loop. rewrite !unfold_loop'. unfold loop_once.
  rewrite interp_bind.
  pupto2 eq_itree_clo_bind. econstructor; [reflexivity|].
  intros. subst. rewrite unfold_interp. pupto2_final. pfold. red.
  destruct u2; simpl; eauto.
Qed.
