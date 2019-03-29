(* begin hide *)
From Coq Require Import
     Morphisms.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.Function
     Basics.FunctionFacts
     Core.ITreeDefinition
     Core.KTree
     Eq.UpToTausEquivalence
     Eq.SimUpToTaus.

From ITree Require Export
     Core.KTreeBasicFacts.

Import ITreeNotations.
Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.
Local Opaque paco2.
(* end hide *)

Section UnfoldLemmas.

Local Opaque ITree.bind' eutt eq_itree.

Lemma assoc_l_itree {E A B C} (x : A + (B + C)) :
  assoc_l_ A B C x ≅ @lift_ktree E (A + (B + C)) _ assoc_l x.
Proof.
  cbv; destruct x as [ | [] ]; try rewrite bind_ret; reflexivity.
Qed.

Lemma assoc_r_itree {E A B C} (x : (A + B) + C) :
  assoc_r_ A B C x ≅ @lift_ktree E ((A + B) + C) _ assoc_r x.
Proof.
  cbv; destruct x as [ [] | ]; try rewrite bind_ret; reflexivity.
Qed.

Lemma assoc_l_ktree {E A B C} :
  assoc_l ⩯ @lift_ktree E (A + (B + C)) _ assoc_l.
Proof.
  cbv; intros [ | [] ]; try rewrite bind_ret; reflexivity.
Qed.

Lemma assoc_r_ktree {E A B C} :
  assoc_r ⩯ @lift_ktree E ((A + B) + C) _ assoc_r.
Proof.
  intros ?; rewrite <- assoc_r_itree; reflexivity.
Qed.

End UnfoldLemmas.

(** ** Equations *)

Section CategoryLaws.

Context {E : Type -> Type}.

(** *** [compose_ktree] respect eq_ktree *)
Global Instance eq_ktree_compose {A B C} :
  @Proper (ktree E A B -> ktree E B C -> _) (eq2 ==> eq2 ==> eq2) cat.
Proof.
  intros ab ab' eqAB bc bc' eqBC.
  intro a.
  unfold cat, Cat_ktree, ITree.cat.
  rewrite (eqAB a).
  apply eutt_bind; try reflexivity.
  intro b; rewrite (eqBC b); reflexivity.
Qed.

(** *** [compose_ktree] is associative *)
Global Instance CatAssoc_ktree : CatAssoc (ktree E).
Proof.
  intros A B C D f g h a.
  unfold cat, Cat_ktree, ITree.cat.
  rewrite bind_bind.
  reflexivity.
Qed.

(** *** [id_ktree] respect identity laws *)
Global Instance CatIdL_ktree : CatIdL (ktree E).
Proof.
  intros A B f a; unfold cat, Cat_ktree, ITree.cat, id_, Id_ktree.
  rewrite bind_ret. reflexivity.
Qed.

Global Instance CatIdR_ktree : CatIdR (ktree E).
Proof.
  intros A B f a; unfold cat, Cat_ktree, ITree.cat, id_, Id_ktree.
  rewrite <- (bind_ret2 (f a)) at 2.
  reflexivity.
Qed.

Global Instance Category_ktree : Category (ktree E).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance InitialObject_ktree : InitialObject (ktree E) void.
Proof. intros A f []. Qed.

End CategoryLaws.

(** *** [lift] properties *)

Section LiftLaws.

Context {E : Type -> Type}.

Local Open Scope cat.

(** *** [lift_ktree] is well-behaved *)

Global Instance eq_lift_ktree {A B} :
  Proper (eq2 ==> eq2) (@lift_ktree E A B).
Proof.
  repeat intro.
  unfold lift_ktree.
  erewrite (H a); reflexivity.
Qed.

Lemma lift_ktree_id {A: Type}: (id_ A ⩯ @lift_ktree E A A (id_ A))%cat.
Proof.
  reflexivity.
Qed.

Fact compose_lift_ktree {A B C} (ab : A -> B) (bc : B -> C) :
  (@lift_ktree E _ _ ab >>> lift_ktree bc ⩯ lift_ktree (ab >>> bc))%cat.
Proof.
  intros a.
  unfold lift_ktree, cat, Cat_ktree, ITree.cat.
  rewrite bind_ret_.
  reflexivity.
Qed.

Fact compose_lift_ktree_l {A B C D} (f: A -> B) (g: B -> C) (k: ktree E C D) :
  (lift_ktree f >>> (lift_ktree g >>> k) ⩯ lift_ktree (g ∘ f) >>> k)%cat.
Proof.
  rewrite <- cat_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
  typeclasses eauto.
Qed.

Fact compose_lift_ktree_r {A B C D} (f: B -> C) (g: C -> D) (k: ktree E A B) :
  ((k >>> lift_ktree f) >>> lift_ktree g ⩯ k >>> lift_ktree (g ∘ f))%cat.
Proof.
  rewrite cat_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
  typeclasses eauto.
Qed.

Fact lift_compose_ktree {A B C}: forall (f:A -> B) (bc: ktree E B C),
    lift_ktree f >>> bc ⩯ fun a => bc (f a).
Proof.
  intros; intro a.
  unfold lift_ktree, cat, Cat_ktree, ITree.cat.
  rewrite bind_ret_. reflexivity.
Qed.

Fact compose_ktree_lift {A B C}: forall (ab: ktree E A B) (g:B -> C),
    (ab >>> lift_ktree g)
  ⩯ (fun a => ITree.map g (ab a)).
Proof.
  reflexivity.
Qed.

Lemma sym_ktree_unfold {A B}:
  @lift_ktree E (A + B) (B + A) swap ⩯ swap.
Proof.
  intros []; reflexivity.
Qed.

End LiftLaws.

Section MonoidalCategoryLaws.

Context {E : Type -> Type}.

Local Open Scope cat.

Fact lift_case_sum {A B C} (ac : A -> C) (bc : B -> C) :
    case_ (@lift_ktree E _ _ ac) (lift_ktree bc)
  ⩯ lift_ktree (case_ ac bc).
Proof.
  intros []; reflexivity.
Qed.

(** *** [Unitors] lemmas *)

(* This is probably generalizable into [Basics.Category]. *)

Lemma unit_l_ktree (A : Type) :
  unit_l ⩯ @lift_ktree E _ A unit_l.
Proof.
  intros [[]|]. reflexivity.
Qed.

Lemma unit_l'_ktree (A : Type) :
  unit_l' ⩯ @lift_ktree E A (void + A) unit_l'.
Proof.
  reflexivity.
Qed.

Lemma unit_r_ktree (A : Type) :
  unit_r ⩯ @lift_ktree E _ A unit_r.
Proof.
  intros [|[]]. reflexivity.
Qed.

Lemma unit_r'_ktree (A : Type) :
  unit_r' ⩯ @lift_ktree E A (A + void) unit_r'.
Proof.
  reflexivity.
Qed.

Lemma case_l_ktree {A B: Type} (ab: @ktree E A (void + B)) :
  ab >>> unit_l ⩯ (fun a: A => ITree.map unit_l (ab a)).
Proof.
  rewrite unit_l_ktree.
  reflexivity.
Qed.

Lemma case_l_ktree' {A B: Type} (f: @ktree E (void + A) (void + B)) :
  unit_l' >>> f ⩯ fun a => f (inr a).
Proof.
  rewrite unit_l'_ktree.
  intro. unfold cat, Cat_ktree, ITree.cat, lift_ktree.
  rewrite bind_ret_; reflexivity.
Qed.

Lemma case_r_ktree' {A B: Type} (f: @ktree E (A + void) (B + void)) :
  unit_r' >>> f ⩯ fun a => f (inl a).
Proof.
  rewrite unit_r'_ktree.
  intro. unfold cat, Cat_ktree, ITree.cat, lift_ktree.
  rewrite bind_ret_; reflexivity.
Qed.

Lemma case_r_ktree {A B: Type} (ab: @ktree E A (B + void)) :
  ab >>> unit_r ⩯ (fun a: A => ITree.map unit_r (ab a)).
Proof.
  rewrite unit_r_ktree.
  reflexivity.
Qed.

(** *** [bimap] lemmas *)

Fact bimap_id_lift {A B C} (f : B -> C) :
  bimap (id_ A) (@lift_ktree E _ _ f) ⩯ lift_ktree (bimap (id_ A) f).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l, <- lift_case_sum, <- compose_lift_ktree.
  reflexivity.
  all: typeclasses eauto.
Qed.

Fact bimap_lift_id {A B C} (f : A -> B) :
  bimap (@lift_ktree E _ _ f) (id_ C) ⩯ lift_ktree (bimap f id).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l, <- lift_case_sum, <- compose_lift_ktree.
  reflexivity.
  all: typeclasses eauto.
Qed.

Global Instance Coproduct_ktree : Coproduct (ktree E) sum.
Proof.
  constructor.
  - intros a b c f g.
    unfold inl_, Inl_ktree.
    rewrite lift_compose_ktree.
    reflexivity.
  - intros a b c f g.
    unfold inr_, Inr_ktree.
    rewrite lift_compose_ktree.
    reflexivity.
  - intros a b c f g fg Hf Hg [x | y].
    + unfold inl_, Inl_ktree in Hf.
      rewrite lift_compose_ktree in Hf.
      specialize (Hf x). simpl in Hf. rewrite Hf. reflexivity.
    + unfold inr_, Inr_ktree in Hg.
      rewrite lift_compose_ktree in Hg.
      specialize (Hg y). simpl in Hg. rewrite Hg. reflexivity.
Qed.

End MonoidalCategoryLaws.

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
  revert ca; clear; ucofix self; intro ca.
  rewrite unfold_loop'; unfold loop_once.
  uclo eq_itree_clo_bind; econstructor; try reflexivity.
  intros [c | b]; intros; subst.
  - match goal with
    | [ |- _ _ (Tau (loop_ ?f _)) ] => rewrite (unfold_loop' f)
    end.
    unfold loop_once_.
    rewrite bind_ret_. (* TODO: [bind_ret] doesn't work. *)
    constructor; eauto with paco.
  - constructor; eauto.
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
  revert ca; clear; ucofix self; intro ca.
  rewrite !unfold_loop'; unfold loop_once.
  rewrite !bind_bind.
  uclo eq_itree_clo_bind; econstructor; try reflexivity.
  intros [c | b]; intros; subst.
  - rewrite bind_ret_, bind_tau_.
    constructor; auto with paco.
  - autorewrite with itree.
    apply reflexivity.
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
  revert cb; ucofix self; intros.
  destruct cb as [c | b].
  - rewrite bind_tau.
    constructor. 
    rewrite map_bind.
    rewrite (unfold_loop' _ (inl c)); unfold loop_once.
    autorewrite with itree.
    uclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros c'; intros; subst.
    rewrite bind_tau.
    rewrite bind_ret_.
    rewrite unfold_loop'; unfold loop_once.
    rewrite bind_bind.
    ustep; constructor.
    uclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros; subst. eauto with paco.
  - rewrite bind_ret.
    apply reflexivity.
Qed.

Lemma vanishing1 {E A B} (f : void + A -> itree E (void + B))
      (a : A) :
  loop f a ≅ ITree.map (apply unit_l) (f (inr a)).
Proof.
  unfold loop.
  rewrite unfold_loop'; unfold loop_once, ITree.map.
  eapply eq_itree_bind; try reflexivity.
  intros [[]| b] _ []; reflexivity.
Qed.

Lemma vanishing2 {E A B C D} (f : D + (C + A) -> itree E (D + (C + B)))
      (a : A) :
    loop (loop f) a
  ≅ loop (assoc_r >>> f >>> assoc_l) a.
Proof.
  unfold loop; rewrite 2 unfold_loop'; unfold loop_once.
  unfold ITree.cat.
  cbn. unfold inr_, Inr_ktree.
  unfold cat, Cat_ktree, ITree.cat, lift_ktree.
  rewrite assoc_r_itree; unfold lift_ktree.
  rewrite !bind_ret.
  rewrite unfold_loop'; unfold loop_once.
  rewrite !bind_bind.
  eapply eq_itree_bind; try reflexivity.
  clear a; intros dcb _ [].
  revert dcb; ucofix self; intros.
  destruct dcb as [d | [c | b]]; cbn.
  all: unfold cat, inl_, inr_, Inl_ktree, lift_ktree; cbn.
  all: rewrite !bind_ret_.
  - (* d *)
    rewrite bind_tau.
    rewrite 2 unfold_loop'; unfold loop_once.
    autorewrite with itree.
    cbn; unfold cat, inl_, Inl_ktree, lift_ktree.
    rewrite bind_ret_.
    constructor.
    uclo eq_itree_clo_bind; econstructor. reflexivity.
    intros; subst. auto with paco.
  - (* c *)
    rewrite 2 unfold_loop'; unfold loop_once.
    rewrite unfold_loop'; unfold loop_once.
    autorewrite with itree.
    cbn; unfold cat, inl_, inr_, Inl_ktree, lift_ktree.
    rewrite !bind_ret_.
    constructor.
    uclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros; subst. auto with paco.
  - (* b *)
    apply reflexivity.
Qed.

Lemma superposing1 {E A B C D D'} (f : C + A -> itree E (C + B))
      (g : D -> itree E D') (a : A) :
    ITree.map inl (loop f a)
  ≅ loop (fun cad =>
      match cad with
      | inl c => ITree.map (bimap id inl) (f (inl c))
      | inr (inl a) => ITree.map (bimap id inl) (f (inr a))
      | inr (inr d) => ITree.map (inr >>> inr)%cat (g d)
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
  revert inla inra Hlr; ucofix self; intros.
  rewrite 2 unfold_loop'; unfold loop_once.
  rewrite bind_bind.
  destruct inra as [c | a]; subst.
  - rewrite bind_bind; setoid_rewrite bind_ret_.
    uclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros [c' | b]; simpl; intros; subst.
    + rewrite bind_tau. constructor.
      auto with paco.
    + rewrite bind_ret. apply reflexivity.
  - rewrite bind_bind; setoid_rewrite bind_ret_.
    uclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros [c' | b]; simpl; intros; subst.
    + rewrite bind_tau. constructor.
      auto with paco.
    + rewrite bind_ret_. apply reflexivity.
Qed.

Lemma superposing2 {E A B C D D'} (f : C + A -> itree E (C + B))
      (g : D -> itree E D') (d : D) :
    ITree.map inr (g d)
  ≅ loop (fun cad =>
      match cad with
      | inl c => ITree.map (bimap id inl) (f (inl c))
      | inr (inl a) => ITree.map (bimap id inl) (f (inr a))
      | inr (inr d) => ITree.map (inr >>> inr)%cat (g d)
      end) (inr d).
Proof.
  unfold loop; rewrite unfold_loop'; unfold loop_once.
  rewrite map_bind; unfold ITree.map.
  eapply eq_itree_bind; try reflexivity.
  intros d' _ []. reflexivity.
Qed.

Lemma yanking {E A} (a : A) :
  @loop E _ _ _ swap a ≅ Tau (Ret a).
Proof.
  rewrite itree_eta; cbn; apply eq_itree_Tau.
  rewrite itree_eta; reflexivity.
Qed.

Instance eq_itree_loop {E A B C} :
  Proper ((eq ==> eq_itree eq) ==> eq ==> eq_itree eq) (@loop E A B C).
Proof.
  repeat intro; subst.
  unfold loop.
  remember (inr _) as ca eqn:EQ; clear EQ y0.
  revert ca; ucofix self; intros.
  rewrite 2 unfold_loop'; unfold loop_once.
  uclo eq_itree_clo_bind; econstructor; try auto.
  intros [c | b]; intros; subst; constructor; auto with paco.
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
  uunfold eutt_f.
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

  - apply eq_itree_vis_inv1 in H1.
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
    apply IHg; auto. rewrite <- unfold_bind; auto.

  - replace ot2 with (observe (go ot2)) in *.
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
  loop_preinv (go ot1) (go ot2) -> cpn2 (suttF1 eq) bot2 ot1 ot2.
Proof.
  intros HH.
  revert ot1 ot2 HH; ucofix self; intros.
  destruct HH as [ca H1 H2 | u1 u2 Hu H1 H2].
  - eapply monotone_suttF1.
    + eapply (eutt_loop_inv_main_step ca (go ot1) (go ot2)); eauto.
    + intros ? ? []. ubase. eapply self; eauto.
  - apply sutt_is_sutt1 in Hu.
    uunfold Hu.
    rewrite unfold_bind in H1.
    rewrite unfold_bind in H2.
    revert ot1 ot2 H1 H2; induction Hu; intros.

    + subst; destruct r2.
      * apply eq_itree_tau_inv1 in H1.
        apply eq_itree_tau_inv1 in H2.
        simpl in H1, H2.
        destruct H1 as [? []], H2 as [? []].
        subst.
        do 2 constructor. ubase.
        apply self.
        eapply loop_inv_main; rewrite <- itree_eta; eauto.
      * apply eq_itree_ret_inv1 in H1.
        apply eq_itree_ret_inv1 in H2.
        simpl in H1, H2. subst; auto with paco.

    + apply eq_itree_vis_inv1 in H1.
      apply eq_itree_vis_inv1 in H2.
      simpl in H1, H2.
      destruct H1 as [? []], H2 as [? []].
      subst; constructor.
      ubase. intros. apply self.
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

    + replace ot2 with (observe (go ot2)) in *.
      rewrite <- unfold_bind in H2.
      apply eq_itree_tau_inv1 in H1.
      simpl in H1.
      destruct H1 as [t1' [Ht1 Ht1']].
      rewrite Ht1.
      constructor.
      ubase; apply self.
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
  - eapply cpn2_mon_bot.
    + eapply sutt_loop; auto.
      repeat intro.
      apply eutt_sutt. apply symmetry; auto.
    + eauto with paco.
    + eauto with paco.
    + intros. eapply monotone_sutt_RR; try eassumption.
      red; auto.
Qed.

(** *** Traced monoidal categories *)

Section TraceLaws.

Context {E : Type -> Type}.

Local Open Scope cat.

(** *** [loop] lemmas *)

Global Instance eq_ktree_loop {I A B} :
  Proper (eq2 ==> eq2) (@loop E I A B).
Proof.
  repeat intro; apply eutt_loop; auto.
Qed.

(* Naturality of (loop_ktree I A B) in A *)
(* Or more diagrammatically:
[[
        +-----+
        | ### |
        +-###-+I
A----B----###----C
          ###

is equivalent to:

   +----------+
   |      ### |
   +------###-+I
A----B----###----C
          ###

]]
 *)

Lemma compose_loop {I A B C}
      (bc_: ktree E (I + B) (I + C)) (ab: ktree E A B) :
    loop ((bimap (id_ _) ab) >>> bc_)
  ⩯ ab >>> loop bc_.
Proof.
  intros a.
  rewrite (loop_natural_l ab bc_ a).
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold bimap, Bimap_Coproduct, case_, Case_ktree, cat, Cat_ktree, ITree.cat, id_, Id_ktree; cbn.
  - rewrite bind_bind, bind_ret_; reflexivity.
  - rewrite bind_bind, map_bind.
    setoid_rewrite bind_ret_; reflexivity.
Qed.

(* Naturality of (loop I A B) in B *)
(* Or more diagrammatically:
[[
   +-----+
   | ### |
   +-###-+I
A----###----B----C
     ###

is equivalent to:

   +----------+
   | ###      |
   +-###------+I
A----###----B----C
     ###

]]
 *)

Lemma loop_compose {I A B B'}
      (ab_: ktree E (I + A) (I + B)) (bc: ktree E B B') :
    loop (ab_ >>> bimap (id_ _) bc)
  ⩯ loop ab_ >>> bc.
Proof.
  intros a.
  rewrite (loop_natural_r bc ab_ a).
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold bimap, Bimap_Coproduct, case_, Case_ktree,
       cat, Cat_ktree, ITree.cat, id_, Id_ktree; cbn.
  - apply eutt_bind; [intros []; simpl | reflexivity ].
    rewrite bind_ret_; reflexivity.
    reflexivity.
  - apply eutt_bind; [intros []; simpl | reflexivity].
    rewrite bind_ret_; reflexivity.
    reflexivity.
Qed.

(* Dinaturality of (loop I A B) in I *)

Lemma loop_rename_internal {I J A B}
      (ab_: ktree E (I + A) (J + B)) (ji: ktree E J I) :
    loop (ab_ >>> bimap ji (id_ _))
  ⩯ loop (bimap ji (id_ _) >>> ab_).
Proof.
  assert (EQ:forall (x: J + B),
             match x with
             | inl a => a0 <- ji a;; Ret (inl a0)
             | inr b => a <- Ret b;; Ret (inr a)
             end ≈
                 match x with
                 | inl a => Tau (ITree.map (@inl I B) (ji a))
                 | inr b => Ret (inr b)
                 end).
  {
    intros [].
    symmetry; apply tau_eutt.
    rewrite bind_ret_; reflexivity.
  }

  unfold bimap, Bimap_Coproduct, case_, Case_ktree, case_sum, cat, Cat_ktree,
  ITree.cat, id_, Id_ktree, inr_, Inr_ktree, inl_, Inl_ktree, lift_ktree; cbn.

  intros ?.
  setoid_rewrite EQ.
  rewrite loop_dinatural.
  apply eutt_loop; [intros [] | reflexivity].
  all: repeat rewrite bind_bind.
  2: repeat rewrite bind_ret_; reflexivity.
  apply eutt_bind; [intros ? | reflexivity ].
  apply eutt_bind; [intros ?; reflexivity| ].
  apply tau_eutt.
Qed.

(* Loop over the empty set can be erased *)
Lemma vanishing_ktree {A B: Type} (f: ktree E (void + A) (void + B)) :
  loop f ⩯ unit_l' >>> f >>> unit_l.
Proof.
  intros a.
  rewrite vanishing1.
  unfold unit_l, UnitL_Coproduct, unit_l', UnitL'_Coproduct, case_, Case_ktree, inr_, Inr_ktree.
  unfold cat, Cat_ktree, ITree.cat, ITree.map, lift_ktree.
  rewrite bind_bind.
  rewrite bind_ret_.
  apply eutt_bind.
  - intros [[] | ]. reflexivity.
  - reflexivity.
Qed.

(* [loop_loop]:

These two loops:

[[
    +----------+
    | +-----+  |
    | | ### |  |
    | +-###-+I |
    +---###----+J
  A-----###-------B
        ###
]]

... can be rewired as a single one:


[[
     +-------+
     |  ###  |
     +--###--+(I+J)
     +--###--+
  A-----###-----B
        ###
]]

 *)

Lemma loop_loop {I J A B} (ab__: ktree E (I + (J + A)) (I + (J + B))) :
    loop (loop ab__)
  ⩯ loop (assoc_r >>> ab__ >>> assoc_l).
Proof.
  intros a.
  rewrite vanishing2.
  unfold ITree.map, cat, Cat_ktree, ITree.cat, assoc_r, AssocR_Coproduct, assoc_l, AssocL_Coproduct, inl_, Inl_ktree, inr_, Inr_ktree, case_, Case_ktree, lift_ktree; cbn.
  apply eutt_loop; [intros [[]|] | reflexivity]; cbn.
  all: rewrite !bind_bind.
  all: try rewrite !bind_ret_.
  all: reflexivity.
Qed.

Lemma fold_map {R S}:
  forall (f: R -> S) (t: itree E R),
    (x <- t;; Ret (f x)) ≅ (ITree.map f t).
Proof.
  intros; reflexivity.
Qed.

Lemma bimap_ktree_loop {I A B C D}
      (ab : ktree E (I + A) (I + B)) (cd : ktree E C D) :
    bimap (loop ab) cd
  ⩯ loop (assoc_l >>> bimap ab cd >>> assoc_r).
Proof.
  rewrite assoc_l_ktree, assoc_r_ktree.
  rewrite lift_compose_ktree, compose_ktree_lift.
  unfold bimap, Bimap_Coproduct, cat, Cat_ktree, ITree.cat, case_, Case_ktree, case_sum.
  unfold inl_, Inl_ktree, inr_, Inr_ktree, lift_ktree.
  intros []; simpl.
  - rewrite fold_map.
    rewrite (@superposing1 E A B I C D).
    apply eutt_loop; try reflexivity.
    intros [|[]]; cbn.
    all: symmetry. (* protect the existential. *)
    all: rewrite fold_map.
    all: rewrite map_map.
    all: reflexivity.
  - unfold loop; rewrite unfold_loop.
    unfold loop_once; cbn.
    rewrite map_bind.
    rewrite bind_bind.
    apply eutt_bind; [ | reflexivity ].
    intros d.
    rewrite bind_ret; cbn.
    reflexivity.
Qed.

(** Utility: lemma to ease working forward in an equational proof.
      Make it more convenient to rewrite subterm only on one side of the equation.
 *)
Fact fwd_eqn {a b : Type} (f g : ktree E a b) :
  (forall h, h ⩯ f -> h ⩯ g) -> f ⩯ g.
Proof.
  intro H; apply H; reflexivity.
Qed.

(** Utility: lemmas to ease forward reasoning *)
Fact cat_eq2_l {a b c : Type} (h : ktree E a b) (f g : ktree E b c) :
  f ⩯ g ->
  h >>> f ⩯ h >>> g.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Fact cat_eq2_r {a b c : Type} (h : ktree E b c) (f g : ktree E a b) :
  f ⩯ g ->
  f >>> h ⩯ g >>> h.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Fact local_rewrite1 {a b c : Type}:
  bimap (id_ a) (@swap _ (ktree E) _ _ b c) >>> assoc_l >>> swap
        ⩯ assoc_l >>> bimap swap (id_ c) >>> assoc_r.
Proof.
  symmetry.
  apply fwd_eqn; intros h Eq.
  do 2 apply (cat_eq2_l (bimap (id_ _) swap)) in Eq.
  rewrite <- cat_assoc, bimap_cat, swap_involutive, cat_id_l,
  bimap_id, cat_id_l in Eq.
  rewrite <- (cat_assoc _ _ _ assoc_r), <- (cat_assoc _ _ assoc_l _)
    in Eq.
  rewrite <- swap_assoc_l in Eq.
  rewrite (cat_assoc _ _ _ assoc_r) in Eq.
  rewrite assoc_l_mono in Eq.
  rewrite cat_id_r in Eq.
  rewrite cat_assoc.
  assumption.
  all: typeclasses eauto.
Qed.

Fact local_rewrite2 {a b c : Type}:
  swap >>> assoc_r >>> bimap (id_ _) swap
       ⩯ @assoc_l _ (ktree E) _ _ a b c >>> bimap swap (id_ _) >>> assoc_r.
Proof.
  symmetry.
  apply fwd_eqn; intros h Eq.
  do 2 apply (cat_eq2_r (bimap (id_ _) swap)) in Eq.
  rewrite cat_assoc, bimap_cat, swap_involutive, cat_id_l,
  bimap_id, cat_id_r in Eq.
  rewrite 2 (cat_assoc _ assoc_l) in Eq.
  rewrite <- swap_assoc_r in Eq.
  rewrite <- 2 (cat_assoc _ assoc_l) in Eq.
  rewrite assoc_l_mono, cat_id_l in Eq.
  assumption.
  all: try typeclasses eauto.
Qed.

Lemma loop_bimap_ktree {I A B C D}
      (ab : ktree E A B) (cd : ktree E (I + C) (I + D)) :
  bimap ab (loop cd)
        ⩯ loop (assoc_l >>> bimap swap (id_ _)
                        >>> assoc_r
                        >>> bimap ab cd
                        >>> assoc_l >>> bimap swap (id_ _) >>> assoc_r).
Proof.
  rewrite swap_bimap, bimap_ktree_loop.
  rewrite <- compose_loop, <- loop_compose.
  rewrite (swap_bimap _ _ cd ab).
  rewrite <- !cat_assoc.
  rewrite local_rewrite1.
  rewrite 2 cat_assoc.
  rewrite <- (cat_assoc _ swap assoc_r).
  rewrite local_rewrite2.
  rewrite <- !cat_assoc.
  reflexivity.
  all: typeclasses eauto.
Qed.

Lemma yanking_ktree {A: Type}:
  @loop E _ _ _ swap ⩯ id_ A.
Proof.
  intros ?; rewrite yanking.
  apply tau_eutt.
Qed.

Lemma loop_rename_internal' {I J A B} (ij : ktree E I J) (ji: ktree E J I)
      (ab_: @ktree E (I + A) (I + B)) :
  (ij >>> ji) ⩯ id_ _ ->
    loop (bimap ji (id_ _) >>> ab_ >>> bimap ij (id_ _))
  ⩯ loop ab_.
Proof.
  intros Hij.
  rewrite loop_rename_internal.
  rewrite <- cat_assoc.
  rewrite bimap_cat.
  rewrite Hij.
  rewrite cat_id_l.
  rewrite bimap_id.
  rewrite cat_id_l.
  reflexivity.
  all: try typeclasses eauto.
Qed.

End TraceLaws.

Hint Rewrite @bimap_id_lift : lift_ktree.
Hint Rewrite @bimap_lift_id : lift_ktree.
Hint Rewrite @lift_case_sum : lift_ktree.

(* Here we show that we can implement [ITree.cat] using
   [bimap], [loop], and composition with the monoidal
   natural isomorphisms. *)
Section CatFromLoop.

Variable E : Type -> Type.

Local Open Scope cat.

(* [cat_from_loop]:

      +-------------+
      |             |
      +---\/---ab---+
   -------/\---bc-------

is equivalent to

   ----ab---bc----
 *)
Theorem cat_from_loop {A B C} (ab : ktree E A B) (bc : ktree E B C) :
  loop (swap >>> bimap ab bc) ⩯ ab >>> bc.
Proof with try typeclasses eauto.
(*
      +-------------+
      |             |
      +---\/---ab---+
   -------/\---bc-------
 *)

  rewrite bimap_slide...
  rewrite <- cat_assoc...
(*
      +----------------+
      |                |
      +---\/---ab------+
   -------/\------bc-------
 *)

  rewrite loop_compose...
(*
      +-------------+
      |             |
      +---\/---ab---+
   -------/\------------bc----
 *)

  rewrite swap_bimap...
  rewrite <- !cat_assoc...
(*
      +-------------------+
      |                   |
      +---\/--\/------\/--+
   -------/\--/\--ab--/\----bc----
 *)

  rewrite swap_involutive, cat_id_l...
(*
      +-------------------+
      |                   |
      +---------------\/--+
   ---------------ab--/\----bc----
 *)

  rewrite compose_loop...
(*
           +------+
           |      |
           +--\/--+
   ----ab-----/\-----bc----
 *)

  rewrite yanking_ktree...
  rewrite cat_id_r...
(*
   ----ab---bc----
 *)

  reflexivity.
Qed.

End CatFromLoop.
