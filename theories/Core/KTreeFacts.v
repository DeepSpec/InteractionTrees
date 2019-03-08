(* begin hide *)
From Coq Require Import
     Morphisms.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.Function
     Core.ITree
     Core.KTree
     Eq.UpToTaus
     Eq.SimUpToTaus
     Indexed.OpenSum.

Import CatNotations.
Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

(* Facts about [loop] *)

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
  ≅ loop (fun dca => ITree.map assoc_l (f (assoc_r dca))) a.
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
      | inl c => ITree.map (bimap id inl) (f (inl c))
      | inr (inl a) => ITree.map (bimap id inl) (f (inr a))
      | inr (inr d) => ITree.map (inr >=> inr)%cat (g d)
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
      | inl c => ITree.map (bimap id inl) (f (inl c))
      | inr (inl a) => ITree.map (bimap id inl) (f (inr a))
      | inr (inr d) => ITree.map (inr >=> inr)%cat (g d)
      end) (inr d).
Proof.
  unfold loop; rewrite unfold_loop'; unfold loop_once.
  rewrite map_bind; unfold ITree.map.
  eapply eq_itree_bind; try reflexivity.
  intros d' _ []. reflexivity.
Qed.

Lemma yanking {E A} (a : A) :
  @loop E _ _ _ (fun aa => Ret (swap aa)) a ≅ Tau (Ret a).
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

(** ** Equations *)

Section CategoryLaws.

Context {E : Type -> Type}.

(** *** [compose_ktree] respect eq_ktree *)
Global Instance eq_ktree_compose {A B C} :
  Proper (eq_ktree ==> eq_ktree ==> eq_ktree) (@ITree.cat E A B C).
Proof.
  intros ab ab' eqAB bc bc' eqBC.
  intro a.
  unfold ITree.cat.
  rewrite (eqAB a).
  apply eutt_bind; try reflexivity.
  intro b; rewrite (eqBC b); reflexivity.
Qed.

(** *** [compose_ktree] is associative *)
Lemma compose_ktree_assoc {A B C D}
      (ab : ktree E A B) (bc : ktree E B C) (cd : ktree E C D) :
  ((ab >=> bc) >=> cd) ⩯ (ab >=> (bc >=> cd)).
Proof.
  intros a.
  unfold ITree.cat.
  rewrite bind_bind.
  apply eutt_bind; try reflexivity.
Qed.

(** *** [id_ktree] respect identity laws *)
Lemma id_ktree_left {A B}: forall (f: ktree E A B),
    id_ktree >=> f ⩯ f.
Proof.
  intros f a; unfold ITree.cat, id_ktree.
  rewrite itree_eta; rewrite ret_bind. rewrite <- itree_eta; reflexivity.
Qed.

Lemma id_ktree_right {A B}: forall (f: ktree E A B),
    f >=> id_ktree ⩯ f.
Proof.
  intros f a; unfold ITree.cat, id_ktree.
  rewrite <- (bind_ret (f a)) at 2.
  reflexivity.
Qed.

End CategoryLaws.

(** *** [lift] properties *)

Section LiftLaws.

Context {E : Type -> Type}.

(** *** [lift_ktree] is well-behaved *)

Global Instance eq_lift_ktree {A B} :
  Proper (eq2 ==> eq_ktree) (@lift_ktree E A B).
Proof.
  repeat intro.
  unfold lift_ktree.
  erewrite (H a); reflexivity.
Qed.

Lemma lift_ktree_id {A: Type}: @id_ktree E A ⩯ lift_ktree id.
Proof.
  unfold id_ktree, lift_ktree; reflexivity.
Qed.

Fact compose_lift_ktree {A B C} (ab : A -> B) (bc : B -> C) :
  (@lift_ktree E _ _ ab >=> lift_ktree bc) ⩯ (lift_ktree (bc ∘ ab)).
Proof.
  intros a.
  unfold lift_ktree, ITree.cat.
  rewrite ret_bind_.
  reflexivity.
Qed.

Fact compose_lift_ktree_l {A B C D} (f: A -> B) (g: B -> C) (k: ktree E C D) :
  (lift_ktree f >=> (lift_ktree g >=> k)) ⩯ (lift_ktree (g ∘ f) >=> k).
Proof.
  rewrite <- compose_ktree_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
Qed.

Fact compose_lift_ktree_r {A B C D} (f: B -> C) (g: C -> D) (k: ktree E A B) :
  ((k >=> lift_ktree f) >=> lift_ktree g) ⩯ (k >=> lift_ktree (g ∘ f)).
Proof.
  rewrite compose_ktree_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
Qed.

Fact lift_compose_ktree {A B C}: forall (f:A -> B) (bc: ktree E B C),
    lift_ktree f >=> bc ⩯ fun a => bc (f a).
Proof.
  intros; intro a.
  unfold lift_ktree, ITree.cat.
  rewrite ret_bind_. reflexivity.
Qed.

Fact compose_ktree_lift {A B C}: forall (ab: ktree E A B) (g:B -> C),
    eq_ktree (ab >=> lift_ktree g)
             (fun a => ITree.map g (ab a)).
Proof.
  intros; intro a.
  unfold ITree.map.
  apply eutt_bind.
  reflexivity.
  intro; reflexivity.
Qed.

Lemma sym_ktree_unfold {A B}:
  lift_ktree swap ⩯ @sym_ktree E A B.
Proof.
  reflexivity.
Qed.

End LiftLaws.

Section MonoidalCategoryLaws.

Context {E : Type -> Type}.

(** *** [associators]  *)
Lemma assoc_lr {A B C} :
  @assoc_ktree_l E A B C >=> assoc_ktree_r ⩯ id_ktree.
Proof.
  unfold assoc_ktree_l, assoc_ktree_r.
  rewrite compose_lift_ktree.
  intros [| []]; reflexivity.
Qed.

Lemma assoc_rl {A B C} :
  @assoc_ktree_r E A B C >=> assoc_ktree_l ⩯ id_ktree.
Proof.
  unfold assoc_ktree_l, assoc_ktree_r.
  rewrite compose_lift_ktree.
  intros [[]|]; reflexivity.
Qed.

(** *** [sum_elim] lemmas *)

Fact compose_sum_elim {A B C D} (ac : ktree E A C) (bc : ktree E B C) (cd : ktree E C D) :
  elim_ Fun ac bc >=> cd ⩯ elim_ Fun (ac >=> cd)%itree (bc >=> cd)%itree.
Proof.
  intros; intros [];
    (unfold ITree.map; simpl; apply eutt_bind; reflexivity).
Qed.

Fact lift_sum_elim {A B C} (ac : A -> C) (bc : B -> C) :
    elim_ Fun (@lift_ktree E _ _ ac) (lift_ktree bc)
  ⩯ lift_ktree (elim ac bc).
Proof.
  intros []; reflexivity.
Qed.

(** *** [Unitors] lemmas *)

(* TODO: replacing l by λ breaks PG (retracts like crazy, or if you go too far it can't retract at all from the second lemma) (ρ is fine, interestingly) *)
Lemma elim_l_ktree {A B: Type} (ab: @ktree E A (void + B)) :
  ab >=> λ_ktree ⩯ (fun a: A => ITree.map unit_l (ab a)).
Proof.
  intros; apply compose_ktree_lift.
Qed.

Lemma elim_l_ktree' {A B: Type} (f: @ktree E (void + A) (void + B)) :
  λ_ktree' >=> f ⩯ fun a => f (inr a).
Proof.
  repeat intro.
  unfold λ_ktree', ITree.cat, lift_ktree.
  rewrite ret_bind_; reflexivity.
Qed.

Lemma elim_ρ_ktree' {A B: Type} (f: @ktree E (A + void) (B + void)) :
  ρ_ktree' >=> f ⩯ fun a => f (inl a).
Proof.
  repeat intro.
  unfold ρ_ktree', ITree.cat, lift_ktree.
  rewrite ret_bind_; reflexivity.
Qed.

Lemma elim_ρ_ktree {A B: Type} (ab: @ktree E A (B + void)) :
  ab >=> ρ_ktree ⩯ (fun a: A => ITree.map unit_r (ab a)).
Proof.
  intros; apply compose_ktree_lift.
Qed.

(** *** [tensor] lemmas *)

Global Instance eq_ktree_tensor {A B C D}:
  Proper (eq_ktree ==> eq_ktree ==> eq_ktree) (@tensor_ktree E A B C D).
Proof.
  intros ac ac' eqac bd bd' eqbd.
  unfold tensor_ktree.
  rewrite eqac, eqbd; reflexivity.
Qed.

Fact tensor_id_lift {A B C} (f : B -> C) :
  (@id_ktree E A) ⊗ (lift_ktree f) ⩯ lift_ktree (bimap id f).
Proof.
  unfold tensor_ktree.
  rewrite compose_lift_ktree, id_ktree_left.
  rewrite lift_sum_elim.
  reflexivity.
Qed.

Fact tensor_lift_id {A B C} (f : A -> B) :
  (lift_ktree f) ⊗ (@id_ktree E C) ⩯ lift_ktree (bimap f id).
Proof.
  unfold tensor_ktree.
  rewrite compose_lift_ktree, id_ktree_left.
  rewrite lift_sum_elim.
  reflexivity.
Qed.

Lemma tensor_id {A B} :
  id_ktree ⊗ id_ktree ⩯ @id_ktree E (A + B).
Proof.
  unfold tensor_ktree, ITree.cat, id_ktree.
  intros []; cbn; rewrite ret_bind_; reflexivity.
Qed.

Lemma assoc_I {A B}:
  @assoc_ktree_r E A void B >=> id_ktree ⊗ λ_ktree ⩯ ρ_ktree ⊗ id_ktree.
Proof.
  unfold ρ_ktree,λ_ktree.
  rewrite tensor_lift_id, tensor_id_lift.
  unfold assoc_ktree_r.
  rewrite compose_lift_ktree.
  apply eq_lift_ktree.
  intros [[|]|]; compute; try reflexivity.
  destruct v.
Qed.

Lemma cat_tensor {A1 A2 A3 B1 B2 B3}
      (f1 : ktree E A1 A2) (f2 : ktree E A2 A3)
      (g1 : ktree E B1 B2) (g2 : ktree E B2 B3) :
  (f1 ⊗ g1) >=> (f2 ⊗ g2) ⩯ (f1 >=> f2) ⊗ (g1 >=> g2).
Proof.
  unfold tensor_ktree, ITree.cat, lift_ktree; simpl.
  intros []; unfold elim, sum_elim; simpl;
    rewrite !bind_bind; setoid_rewrite ret_bind_; reflexivity.
Qed.

Lemma sum_elim_compose {A B C D F}
      (ac: ktree E A (C + D)) (bc: ktree E B (C + D))
      (cf: ktree E C F) (df: ktree E D F) :
    elim_ Fun ac bc >=> elim_ Fun cf df
  ⩯ elim_ Fun (ac >=> elim_ Fun cf df) (bc >=> elim_ Fun cf df).
Proof.
  intros.
  unfold ITree.map.
  intros []; reflexivity.
Qed.

Lemma inl_sum_elim {A B C} (ac: ktree E A C) (bc: ktree E B C) :
  lift_ktree inl >=> elim_ Fun ac bc ⩯ ac.
Proof.
  intros.
  unfold ITree.cat, lift_ktree.
  intros ?.
  rewrite ret_bind_.
  reflexivity.
Qed.

Lemma inr_sum_elim {A B C} (ac: ktree E A C) (bc: ktree E B C) :
  lift_ktree inr >=> elim_ Fun ac bc ⩯ bc.
Proof.
  intros.
  unfold ITree.cat, lift_ktree.
  intros ?.
  rewrite ret_bind_.
  reflexivity.
Qed.

Lemma tensor_ktree_slide {A B C D} (ac: ktree E A C) (bd: ktree E B D) :
  ac ⊗ bd ⩯ ac ⊗ id_ktree >=> id_ktree ⊗ bd.
Proof.
  intros.
  unfold tensor_ktree.
  repeat rewrite id_ktree_left.
  rewrite sum_elim_compose.
  rewrite compose_ktree_assoc.
  rewrite inl_sum_elim, inr_sum_elim.
  reflexivity.
Qed.

Lemma assoc_coherent_r {A B C D}:
    @assoc_ktree_r E A B C ⊗ @id_ktree E D
      >=> assoc_ktree_r
      >=> id_ktree ⊗ assoc_ktree_r
  ⩯ assoc_ktree_r >=> assoc_ktree_r.
Proof.
  unfold tensor_ktree, assoc_ktree_r.
  repeat rewrite id_ktree_left.
  repeat rewrite compose_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  apply eq_lift_ktree.
  intros [[[|]|]|]; reflexivity.
Qed.

Lemma assoc_coherent_l {A B C D}:
    @id_ktree E A ⊗ @assoc_ktree_l E B C D
      >=> assoc_ktree_l
      >=> assoc_ktree_l ⊗ id_ktree
  ⩯ assoc_ktree_l >=> assoc_ktree_l.
Proof.
  unfold tensor_ktree, assoc_ktree_l.
  repeat rewrite id_ktree_left.
  repeat rewrite compose_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  apply eq_lift_ktree.
  intros [|[|[|]]]; reflexivity.
Qed.

(** *** [sym] lemmas *)

Lemma sym_unit_ktree {A} :
  sym_ktree >=> λ_ktree ⩯ @ρ_ktree E A.
Proof.
  unfold sym_ktree, ρ_ktree, λ_ktree.
  rewrite lift_compose_ktree.
  intros []; simpl; reflexivity.
Qed.

Lemma sym_assoc_ktree {A B C}:
    @assoc_ktree_r E A B C >=> sym_ktree >=> assoc_ktree_r
  ⩯ (sym_ktree ⊗ id_ktree) >=> assoc_ktree_r >=> (id_ktree ⊗ sym_ktree).
Proof.
  unfold assoc_ktree_r, sym_ktree.
  rewrite tensor_lift_id, tensor_id_lift.
  repeat rewrite compose_lift_ktree.
  apply eq_lift_ktree.
  intros [[|]|]; compute; reflexivity.
Qed.

Lemma sym_nilpotent {A B: Type}:
  sym_ktree >=> sym_ktree ⩯ @id_ktree E (A + B).
Proof.
  unfold sym_ktree, id_ktree.
  rewrite compose_lift_ktree.
  unfold compose.
  unfold lift_ktree; intros a.
  setoid_rewrite iso_ff'; reflexivity.
Qed.

Lemma tensor_swap {A B C D} (ab : ktree E A B) (cd : ktree E C D) :
  ab ⊗ cd ⩯ (sym_ktree >=> cd ⊗ ab >=> sym_ktree).
Proof.
  unfold tensor_ktree.
  unfold sym_ktree.
  rewrite !(compose_ktree_lift cd), !(compose_ktree_lift ab), !lift_compose_ktree, !compose_ktree_lift.
  intros []; cbn; rewrite map_map; cbn;
    apply eutt_map; try intros []; reflexivity.
Qed.

End MonoidalCategoryLaws.

(** *** Traced monoidal categories *)

Section TraceLaws.

Context {E : Type -> Type}.

(** *** [loop] lemmas *)

Global Instance eq_ktree_loop {I A B} :
  Proper (eq_ktree ==> eq_ktree) (@loop E I A B).
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
    loop ((id_ktree ⊗ ab) >=> bc_)
  ⩯ ab >=> loop bc_.
Proof.
  intros a.
  rewrite (loop_natural_l ab bc_ a).
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold tensor_ktree, elim, sym_ktree, ITree.cat, assoc_ktree_l, assoc_ktree_r, id_ktree, lift_ktree; simpl.
  - rewrite bind_bind, ret_bind_; reflexivity.
  - rewrite bind_bind, map_bind.
    setoid_rewrite ret_bind_; reflexivity.
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
    loop (ab_ >=> (id_ktree ⊗ bc))
  ⩯ loop ab_ >=> bc.
Proof.
  intros a.
  rewrite (loop_natural_r bc ab_ a).
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold tensor_ktree, elim, sym_ktree, ITree.cat, assoc_ktree_l, assoc_ktree_r, id_ktree, lift_ktree; simpl.
  - apply eutt_bind; [reflexivity | intros []; simpl].
    rewrite ret_bind_; reflexivity.
    reflexivity.
  - apply eutt_bind; [reflexivity | intros []; simpl].
    rewrite ret_bind_; reflexivity.
    reflexivity.
Qed.

(* Dinaturality of (loop I A B) in I *)

Lemma loop_rename_internal {I J A B}
      (ab_: ktree E (I + A) (J + B)) (ji: ktree E J I) :
    loop (ab_ >=> (ji ⊗ id_ktree))
  ⩯ loop ((ji ⊗ id_ktree) >=> ab_).
Proof.
  unfold tensor_ktree, elim, ITree.cat, lift_ktree, sum_elim.

  assert (EQ:forall (x: J + B),
             match x with
             | inl a => a0 <- ji a;; Ret (inl a0)
             | inr b => a <- id_ktree b;; Ret (inr a)
             end ≈
                 match x with
                 | inl a => Tau (ITree.map (@inl I B) (ji a))
                 | inr b => Ret (inr b)
                 end).
  {
    intros [].
    symmetry; apply tau_eutt.
    unfold id_ktree.
    rewrite ret_bind_; reflexivity.
  }
  intros ?.
  setoid_rewrite EQ.
  rewrite loop_dinatural.
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold id_ktree.
  all: repeat rewrite bind_bind.
  2: repeat rewrite ret_bind_; reflexivity.
  apply eutt_bind; [reflexivity | intros ?].
  apply eutt_bind; [| intros ?; reflexivity].
  apply tau_eutt.
Qed.

(* Loop over the empty set can be erased *)
Lemma vanishing_ktree {A B: Type} (f: ktree E (void + A) (void + B)) :
  loop f ⩯ λ_ktree' >=> f >=> λ_ktree.
Proof.
  intros a.
  rewrite vanishing1.
  unfold λ_ktree,λ_ktree'.
  unfold ITree.cat, ITree.map, lift_ktree.
  rewrite bind_bind.
  rewrite ret_bind_.
  reflexivity.
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
  ⩯ loop (assoc_ktree_r >=> ab__ >=> assoc_ktree_l).
Proof.
  intros a.
  rewrite vanishing2.
  apply eutt_loop; [intros [[]|] | reflexivity].
  all: unfold ITree.map, ITree.cat, assoc_ktree_r, assoc_ktree_l, lift_ktree; cbn.
  all: rewrite bind_bind.
  all: rewrite ret_bind_.
  all: reflexivity.
Qed.

Lemma fold_map {R S}:
  forall (f: R -> S) (t: itree E R),
    (x <- t;; Ret (f x)) ≅ (ITree.map f t).
Proof.
  intros; reflexivity.
Qed.

Lemma tensor_ktree_loop {I A B C D}
      (ab : ktree E (I + A) (I + B)) (cd : ktree E C D) :
    (loop ab) ⊗ cd
  ⩯ loop (assoc_ktree_l >=> (ab ⊗ cd) >=> assoc_ktree_r).
Proof.
  unfold tensor_ktree, elim, ITree.cat, assoc_ktree_l, assoc_ktree_r, lift_ktree, sum_elim.
  intros []; simpl.
  all:setoid_rewrite bind_bind.
  all:setoid_rewrite ret_bind_.
  all:rewrite fold_map.
  1:rewrite (@superposing1 E A B I C D).
  2:rewrite (@superposing2 E A B I C D).
  all:unfold bimap, ITree.map, assoc_r,sum_elim; cbn.
  all:apply eutt_loop; [intros [| []]; cbn | reflexivity].
  all: setoid_rewrite bind_bind.
  all:setoid_rewrite ret_bind_.
  all:reflexivity.
Qed.

Lemma yanking_ktree {A: Type}:
  loop sym_ktree ⩯ @id_ktree E A.
Proof.
  unfold sym_ktree, lift_ktree.
  intros ?; rewrite yanking.
  apply tau_eutt.
Qed.

Lemma loop_rename_internal' {I J A B} (ij : ktree E I J) (ji: ktree E J I)
      (ab_: @ktree E (I + A) (I + B)) :
  (ij >=> ji) ⩯ id_ktree ->
    loop ((ji ⊗ id_ktree) >=> ab_ >=> (ij ⊗ id_ktree))
  ⩯ loop ab_.
Proof.
  intros Hij.
  rewrite loop_rename_internal.
  rewrite <- compose_ktree_assoc.
  rewrite cat_tensor.
  rewrite Hij.
  rewrite id_ktree_left.
  rewrite tensor_id.
  rewrite id_ktree_left.
  reflexivity.
Qed.

End TraceLaws.

Hint Rewrite @compose_ktree_assoc : lift_ktree.
Hint Rewrite @tensor_id_lift : lift_ktree.
Hint Rewrite @tensor_lift_id : lift_ktree.
Hint Rewrite @lift_sum_elim : lift_ktree.

(* Here we show that we can implement [ITree.cat] using
   [tensor_ktree], [loop], and composition with the monoidal
   natural isomorphisms. *)
Section CatFromLoop.

Variable E : Type -> Type.

Theorem cat_from_loop {A B C} (ab : ktree E A B) (bc : ktree E B C) :
  loop (sym_ktree >=> ab ⊗ bc) ⩯ ab >=> bc.
Proof.
  rewrite tensor_ktree_slide.
  rewrite <- compose_ktree_assoc.
  rewrite loop_compose.
  rewrite tensor_swap.
  repeat rewrite <- compose_ktree_assoc.
  rewrite sym_nilpotent, id_ktree_left.
  rewrite compose_loop.
  erewrite yanking_ktree.
  rewrite id_ktree_right.
  reflexivity.
Qed.

End CatFromLoop.
