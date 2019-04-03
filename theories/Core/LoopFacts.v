(** * Facts about [aloop] and [loop] *)

(* begin hide *)
From Coq Require Import
     Program
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.UpToTausEquivalence.

Import ITreeNotations.
Import CatNotations.
Local Open Scope itree.
(* end hide *)

(** ** [ITree.aloop] *)

Lemma bind_aloop {E A B C} (f : A -> itree E A + B) (g : B -> itree E B + C): forall x,
    (ITree.aloop f x >>= ITree.aloop g)
  ≈ ITree.aloop (fun ab =>
       match ab with
       | inl a => inl (ITree._aloop id (fun a => Ret (inl a))
                                    (bimap (id_ _) inr (f a)))
       | inr b => apply_Fun (bimap (ITree.map inr) (id_ _)) (g b)
       end) (inl x).
Proof.
  gstep. gcofix CIH. intros.
  rewrite !unfold_aloop'. unfold ITree._aloop.
  destruct (f x) as [t | b]; cbn.
  - unfold id. rewrite bind_tau. gstep. constructor.
    rewrite !bind_bind.
    gclo eutt0_clo_bind. econstructor.
    { reflexivity. }
    intros ? _ [].
    rewrite bind_ret.
    eauto with paco.
  - rewrite bind_ret_. apply eutt0_tau_right.
    rewrite bind_ret_.
    revert b. gcofix CIH'. intros.
    rewrite !unfold_aloop'. unfold ITree._aloop.
    destruct (g b) as [t' | c]; cbn.
    + rewrite bind_map. gstep. constructor.
      gclo eutt0_clo_bind. econstructor; [reflexivity|].
      intros. subst. eauto with paco.
    + gstep. econstructor. reflexivity.
Qed.

Lemma eutt_aloop' {E I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E I1 + R1)
      (body2 : I2 -> itree E I2 + R2)
      (eutt_body
       : forall j1 j2, RI j1 j2 -> sum_rel (eutt RI) RR (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @eutt E _ _ RR (ITree.aloop body1 i1) (ITree.aloop body2 i2).
Proof.
  gstep. gcofix CIH.
  intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_aloop'.
  destruct eutt_body; cbn.
  - gstep. econstructor.
    gclo eutt0_clo_bind; econstructor.
    { eassumption. }
    intros. auto with paco.
  - gstep. econstructor. eauto.
Qed.

(** ** [loop] *)

Instance eq_itree_loop {E A B C} :
  Proper ((eq ==> eq_itree eq) ==> pointwise_relation _ (eq_itree eq))
         (@loop E A B C).
Proof.
  intros body1 body2 EQ_BODY a.
  unfold loop.
  eapply eq_itree_bind; auto.
  clear a; red. gcofix CIH; intros cb.
  rewrite 2 unfold_aloop'.
  destruct cb as [c | b]; cbn.
  - gstep. constructor.
    gclo eq_itree_clo_bind; econstructor; eauto.
    intros cb _ [].
    auto with paco.
  - gstep. constructor; auto.
Qed.

Instance eutt_loop {E A B C} :
  Proper (pointwise_relation _ (eutt eq) ==> pointwise_relation _ (eutt eq))
         (@loop E A B C).
Proof.
  intros body1 body2 EQ_BODY a.
  unfold loop.
  apply eutt_bind; auto.
  clear a; red.
  gstep; gcofix CIH.
  intros cb.
  rewrite 2 unfold_aloop'.
  destruct cb as [c | b]; cbn.
  - gstep. constructor.
    gclo eutt0_clo_bind; econstructor; eauto.
    intros cb' _ [].
    auto with paco.
  - gstep. constructor; auto.
Qed.

Lemma bind_loop2 {E A A' B C} (f : A' -> itree E A)
      (body  : C + A  -> itree E (C + B))
      (a' : A')
  : ITree.bind (f a') (loop body)
  ≈ loop (fun ca' =>
            match ca' with
            | inl c => body (inl c)
            | inr a' => a <- f a';; body (inr a)
            end) a'.
Proof.
  unfold loop.
  rewrite <- bind_bind.
  eapply eutt_bind; try reflexivity.
Qed.

Lemma bind_loop {E A B B' C}
      (f  : B -> itree E B')
      (body  : C + A -> itree E (C + B))
      (a : A)
  : loop body a >>= f
  ≅ loop (fun ca =>
            cb <- body ca ;;
            match cb with
            | inl c => Ret (inl c)
            | inr b => ITree.map inr (f b)
            end) a.
Proof.
  unfold loop.
  rewrite !bind_bind.
  eapply eq_itree_bind; try reflexivity.
  red.
  gcofix CIH.
  intros [c | b]; cbn.
  - rewrite bind_ret.
    rewrite 2 unfold_aloop'; cbn.
    rewrite bind_tau, !bind_bind.
    gstep. constructor.
    gclo eq_itree_clo_bind; econstructor.
    { reflexivity. }
    intros cb' _ [].
    auto with paco.
  - rewrite bind_map.
    rewrite unfold_aloop'; cbn.
    rewrite bind_ret.
    rewrite <- bind_ret2 at 1.
    gclo eq_itree_clo_bind; econstructor.
    { reflexivity. }
    intros b' _ [].
    rewrite unfold_aloop'. gstep. constructor; auto.
Qed.

Lemma loop_bind {E A B C C'} (f : C -> itree E C')
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
  rewrite bind_ret, !bind_bind.
  eapply eq_itree_bind; try reflexivity.
  intros [c | b].
  2:{ rewrite bind_ret.
      do 2 rewrite unfold_aloop'; cbn.
      red. gstep. constructor. auto.
  }
  revert c; gcofix CIH; intros c.
  rewrite bind_tau.
  rewrite unfold_aloop'; cbn.
  gstep. constructor.
  rewrite !bind_bind, bind_map.
  gclo eq_itree_clo_bind; econstructor; try reflexivity.
  intros ? _ [].
  rewrite unfold_aloop'; cbn.
  autorewrite with itree.
  gstep.
  constructor.
  gclo eq_itree_clo_bind; econstructor; try reflexivity.
  intros [] _ [].
  - auto with paco.
  - rewrite bind_ret.
    do 2 rewrite unfold_aloop'; cbn.
    gstep; constructor; auto.
Qed.

Lemma vanishing1_loop {E A B} (f : void + A -> itree E (void + B))
      (a : A) :
  loop f a ≅ ITree.map (apply unit_l) (f (inr a)).
Proof.
  unfold loop, ITree.map.
  eapply eq_itree_bind; try reflexivity.
  intros [[]|b].
  rewrite unfold_aloop'; reflexivity.
Qed.

Lemma vanishing2_loop {E A B C D} (f : D + (C + A) -> itree E (D + (C + B)))
      (a : A) :
    loop (loop f) a
  ≅ loop (fun dca => ITree.map assoc_l (f (apply_Fun assoc_r dca))) a.
Proof.
  unfold loop; cbn.
  rewrite !bind_bind, bind_map.
  eapply eq_itree_bind; try reflexivity.
  intros dcb.
  revert dcb; gcofix CIH; intros dcb.
  do 2 rewrite unfold_aloop'; destruct dcb as [d | [c | b]]; cbn.
  - (* d *)
    rewrite bind_tau, !bind_bind, bind_map.
    gstep. constructor.
    gclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros dcb' _ [].
    auto with paco.
  - (* c *)
    rewrite bind_ret, unfold_aloop'; cbn.
    rewrite !bind_bind, bind_map.
    gstep. constructor.
    gclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros dcb' _ [].
    auto with paco.
  - (* b *)
    rewrite bind_ret, unfold_aloop'; cbn.
    gstep. constructor; auto.
Qed.

Lemma superposing1_loop {E A B C D D'} (f : C + A -> itree E (C + B))
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
  rewrite map_bind, bind_map.
  eapply eq_itree_bind; try reflexivity.
  intros cb.
  unfold ITree.map.
  revert cb; gcofix CIH; intros cb.
  do 2 rewrite unfold_aloop'. (* why is this slow *)
  destruct cb as [c | b]; cbn.
  - rewrite bind_tau, !bind_bind.
    gstep. constructor.
    gclo eq_itree_clo_bind; econstructor; try reflexivity.
    intros cb' _ [].
    rewrite bind_ret.
    auto with paco.
  - rewrite bind_ret; gstep; constructor; auto.
Qed.

Lemma superposing2_loop {E A B C D D'} (f : C + A -> itree E (C + B))
      (g : D -> itree E D') (d : D) :
    ITree.map inr (g d)
  ≅ loop (fun cad =>
      match cad with
      | inl c => ITree.map (bimap id inl) (f (inl c))
      | inr (inl a) => ITree.map (bimap id inl) (f (inr a))
      | inr (inr d) => ITree.map (inr >>> inr)%cat (g d)
      end) (inr d).
Proof.
  unfold loop, ITree.map.
  rewrite !bind_bind.
  eapply eq_itree_bind; try reflexivity.
  intros d'.
  rewrite bind_ret, unfold_aloop'; reflexivity.
Qed.

Lemma yanking_loop {E A} (a : A) :
  @loop E _ _ _ swap a ≅ Tau (Ret a).
Proof.
  rewrite itree_eta; cbn; apply eq_itree_Tau.
  rewrite itree_eta; reflexivity.
Qed.
