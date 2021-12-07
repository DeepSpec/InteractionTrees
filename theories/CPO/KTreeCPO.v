From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     Logic.Classical
.

Require Import Lia.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq
     CPO.CPO
     CPO.ITreeApprox
     CPO.ITreeApproxSup
     CPO.ITreeCPO
     (* Basics.CategoryOps
     Basics.CategoryKleisli *)
.

From ExtLib Require Import
     Structures.Monad.

Definition strong_ktree_approx {R S E} RR (f g : R -> itree E S) :=
  forall x, strong_itree_approx RR (f x) (g x).

Definition weak_ktree_approx {R S E} RR (f g : R -> itree E S) :=
  forall x, weak_itree_approx RR (f x) (g x).

Definition ktree_monotone_approx {R S E} RR (seq : sequence (R -> itree E S) ) : Prop :=
  forall x, monotone_approx RR (apply_seq seq x).

Definition ktree_approx_sup {R S E} test_and_apply (seq : sequence (R -> itree E S) ) : R -> itree E S :=
  fun x => itree_approx_sup test_and_apply (apply_seq seq x). 

Global Instance ktree_weak_cpo {R S E} test_and_apply : weak_cpo (R -> itree E S) :=
  {|
    weak_leq := weak_ktree_approx eq;
    strong_leq := strong_ktree_approx eq;
    sup := ktree_approx_sup test_and_apply;
    weak_eq := fun k1 k2 => forall r, k1 r ≈ k2 r;
    strong_eq := fun k1 k2 => forall r, k1 r ≅ k2 r;
  |}.

Global Instance ktree_pointed_weak_cpo {R S E} test_and_apply : pointed_weak_cpo (@ktree_weak_cpo R S E test_and_apply) :=
{| bot := fun _ => ITree.spin |}.

Global Instance ktree_weak_cpo_laws {R S E} test_and_apply :
  test_and_apply_correct E test_and_apply ->
  weak_cpo_laws (@ktree_weak_cpo R S E test_and_apply).
Proof.
  intros Htaa.
  econstructor; cbn.
  - split; intros. unfold weak_ktree_approx. setoid_rewrite H.
    split; intros; apply weak_itree_approx_refl. unfold weak_ktree_approx in H.
    destruct H. apply weak_itree_approx_antisym; auto.
  - split; intros; unfold strong_ktree_approx. setoid_rewrite H.
    split; intros; apply strong_itree_approx_refl. destruct H.
    apply strong_itree_approx_antisym; auto.
  - intros. rewrite H. reflexivity.
  - intros. red. intros. apply strong_to_weak_itree_approx; auto.
  - intros. red in H. cbn in H. constructor; eauto.
    + cbn. unfold weak_ktree_approx, ktree_approx_sup. intros.
      unfold apply_seq. cbn. unfold map.
      set (fun n => seq n x) as seq'. assert (seq n x = seq' n). auto. rewrite H0.
      eapply sup_is_upper_bound; destruct Htaa; eauto.
      constructor; cbv; intros; subst; auto. red. intros. apply H. auto.
    + cbn. unfold weak_ktree_approx, ktree_approx_sup, apply_seq, map.
      intros. set (fun n => seq n x) as seq'.
      eapply sup_is_below_all_upper_bounds; eauto; destruct Htaa; eauto.
      constructor; cbv; intros; subst; auto. red. intros. apply H. auto. 
  - repeat intro. cbn in *. red in H. cbn in H.
    unfold ktree_approx_sup, apply_seq, map. 
    eapply proper_fun_seq'; auto. repeat red. intros; subst. apply H.
  - intros. unfold ktree_approx_sup, apply_seq, map.
    set (fun n => seq n r) as seq'. 
    rewrite sup_advance_eutt; destruct Htaa; auto.
    2 : constructor; cbv; intros; subst; auto.
    2 : { unfold seq';  red in H. red. intros. eapply H. auto. }
    unfold advance, seq'. reflexivity.
Unshelve.
 constructor; red; cbn; intros. reflexivity.
 rewrite H. reflexivity.
 rewrite <- H0. auto.
 constructor. red. cbn. intros. red. intros. apply weak_itree_approx_refl.
 red. cbn. unfold weak_ktree_approx. intros. eapply weak_itree_approx_trans_eq; eauto.
 constructor; red; cbn; intros. reflexivity. rewrite H. reflexivity.
 rewrite H. auto.
 constructor; red; cbn; unfold strong_ktree_approx. intros. apply strong_itree_approx_refl.
 intros. cbn in *. 
 eapply strong_itree_approx_mon with (RR1 := rcompose eq eq). intros. inv H1. auto.
 eapply strong_itree_approx_trans; eauto.
Qed.

Global Instance ktree_pointed_weak_cpo_laws {R S E} test_and_apply :
  test_and_apply_correct E test_and_apply ->
  pointed_weak_cpo_laws (@ktree_weak_cpo R S E test_and_apply) (ktree_pointed_weak_cpo test_and_apply).
Proof.
  intros. constructor. cbn. red. intros. apply strong_itree_approx_spin_bottom.
Qed.

Section Fixable.

Context (E : Type -> Type).
Context (taa : forall {A B C : Type} (e1 : E A) (a : A) (e2 : E B) (k : B -> C) (default : C) , C).
Context (Htaa : test_and_apply_correct E taa).

Instance E_itree_cpo {R} : weak_cpo (itree E R) := itree_weak_cpo taa.
Instance E_itree_cpo_laws {R} : weak_cpo_laws (@E_itree_cpo R) := itree_weak_cpo_laws taa Htaa.

Instance E_ktree_cpo {R S} : weak_cpo (R -> itree E S) := ktree_weak_cpo taa.
Instance E_ktree_cpo_laws {R S} : weak_cpo_laws (@E_ktree_cpo R S) := ktree_weak_cpo_laws taa Htaa.

(*consider renaming
  maybe this type needs to be more restrictive
 *)
Definition bind_rec {R S T : Type} (k : (R -> itree E S) -> (S -> itree E T))
           (rec : R -> itree E S) : R -> itree E T :=
  fun r => ITree.bind (rec r) (k rec).

Lemma bind_rec_scott_cont_aux_lub:
  forall (R S T : Type) (k : (R -> itree E S) -> S -> itree E T) (seq : sequence (R -> itree E S))
    (lim : R -> itree E S),
    (forall (seq0 : sequence (R -> itree E S)) (lim0 : R -> itree E S),
        supremum seq0 lim0 -> supremum (map k seq0) (k lim0)) ->
    supremum seq lim ->
    forall upper_bound : R -> itree E T,
      (forall n : nat, weak_leq (map (bind_rec k) seq n) upper_bound) ->
      weak_leq (bind_rec k lim) upper_bound.
Proof.
  intros R S T k seq lim Hk Hlim. cbn in *.
  unfold bind_rec. 
  unfold weak_ktree_approx. cbn. intros upper_bound Hub.
  intros x.
  assert (Hub' : forall (x : R) (n : nat),
        weak_itree_approx eq
          (map (fun (rec : R -> itree E S) (r : R) => ITree.bind (rec r) (k rec)) seq n x)
          (upper_bound x) ). auto.
  clear Hub. rename Hub' into Hub. specialize (Hub x).
  remember (upper_bound x) as ubx. 
  remember (lim x) as tlim.
  unfold map in Hub.
  remember (fun n => seq n x) as seq'.
  assert (Hub' : forall n, weak_itree_approx eq (ITree.bind (seq' n) (k (seq n) ) ) ubx ).
  subst; auto.
  clear Hub. rename Hub' into Hub.
  assert (supremum seq' tlim ).
  {
    subst. constructor.
    red. intros. destruct Hlim. apply Hmon; auto.
    cbn. destruct Hlim. intros. cbn in *. apply Hub0.
    intros. cbn in *. destruct Hlim.
    cbn in *. unfold weak_ktree_approx in *.
    set (sup seq) as ub. specialize (Hlub ub).
    eapply weak_itree_approx_trans_eq with (t2 := ub x).
    - unfold ub in *. eapply Hlub. unfold sup. cbn. unfold ktree_approx_sup.
      intros. assert (seq n x0 = apply_seq seq x0 n); auto.
      rewrite H0.
      eapply sup_is_upper_bound; try (destruct Htaa; auto; fail).
      constructor; red; intros; subst; auto. red. unfold apply_seq, map.
      intros. apply Hmon; auto.
    - unfold ub in *. unfold sup. cbn. unfold ktree_approx_sup.
      eapply sup_is_below_all_upper_bounds; try (destruct Htaa; auto; fail).
      constructor; red; intros; subst; auto. red. unfold apply_seq, map.
      intros. apply Hmon; auto.
  }
  (* set up for coinduction *)
  clear Heqtlim Hequbx upper_bound Heqseq'.
  generalize dependent tlim. generalize dependent ubx.
  generalize dependent seq. generalize dependent seq'.
  ginit. gcofix CIH. 
  intros seq' seq Hlim ubx Hubx tlim Htlim.
  destruct (observe tlim) eqn : Heqtlim; symmetry in Heqtlim; use_simpobs.
  - rewrite Heqtlim. rewrite bind_ret_l.
    assert (supremum seq' (Ret r0)).
    { destruct Htlim. setoid_rewrite Heqtlim in Hub. setoid_rewrite Heqtlim in Hlub.
      constructor; auto. }
    apply subst_scott_cont_aux_ret2 in H; auto. destruct H as [n Hn].
    specialize (Hubx n) as Hubx'. rewrite Hn in Hubx'. rewrite bind_ret_l in Hubx'.
    apply Hk in Hlim as Hlim'.
    unfold map in Hlim'. destruct Hlim'.
    enough (weak_itree_approx eq (k lim r0) ubx ).
    gfinal. right. eapply paco2_mon; eauto; intros; contradiction.
    specialize (Hk seq lim Hlim).
    set (sup (map k seq) ) as supkseq.
    assert (weak_eq (k lim) (sup (map k seq)) ).
    eapply supremum_unique; eauto. apply E_ktree_cpo_laws.
    apply CPO.sup_correct. auto.
    assert (weak_eq (sup (map k seq)) (sup (advance_n n (map k seq) )) ).
    eapply weak_eq_advance_n; auto. apply E_ktree_cpo_laws.
    cbn in H, H0. rewrite H. rewrite H0.
    eapply sup_is_below_all_upper_bounds; try ( destruct Htaa; eauto; fail).
    constructor; red; intros; subst; auto.
    destruct Hk; eauto. 
    { unfold apply_seq, map, advance_n. red. intros.
      eapply Hmon0. lia. }
    unfold apply_seq, map. unfold advance_n.
    assert (forall m, seq' (m + n) ≈ Ret r0 ).
    { intros. induction m; auto.
      cbn. destruct (@E_itree_cpo_laws S). apply weak_leq_po. cbn.
      split.
      - destruct Htlim. rewrite <- Heqtlim. cbn in Hub0. eauto.
      - rewrite <- IHm. destruct Htlim. 
        apply weaken_leq. eauto. }
    intros n0. specialize (Hubx (n0 + n)).
    setoid_rewrite H1 in Hubx. setoid_rewrite bind_ret_l in Hubx.
    rewrite PeanoNat.Nat.add_comm. auto.
  - rewrite Heqtlim. rewrite bind_tau. gstep. constructor. gfinal. left.
    eapply CIH; eauto. destruct Htlim. cbn in *. constructor; eauto.
    cbn. setoid_rewrite Heqtlim in Hub. setoid_rewrite tau_eutt in Hub. auto.
    cbn. setoid_rewrite Heqtlim in Hlub. setoid_rewrite tau_eutt in Hlub. auto.
  - rewrite Heqtlim. rewrite bind_vis.
    assert (exists (n : nat), exists kn, seq' n ≈ Vis e kn /\ (forall a, weak_itree_approx eq (kn a) (k0 a) )  ).
    assert (supremum seq' (Vis e k0)).
    destruct Htlim.
    setoid_rewrite Heqtlim in Hub. setoid_rewrite Heqtlim in Hlub. constructor; auto.
    apply subst_scott_cont_vis_seq_aux in H.
    decompose record H. eexists. eexists. split; eauto.
    rename x0 into n. rename x1 into kn.
    destruct Htlim. cbn in Hub. specialize (Hub n). 
    rewrite Heqtlim in Hub. rewrite H1 in Hub. pinversion  Hub.
    inj_existT. subst. auto.
    decompose record H. rename x0 into n. rename x1 into kn.
    specialize (Hubx n) as Hubxn. rewrite H0 in Hubxn.
    rewrite bind_vis in Hubxn. punfold Hubxn.
    red in Hubxn. cbn in *. remember (VisF e (fun x : X => ITree.bind (kn x) (k (seq n)))) as y.
    remember (observe ubx) as oubx. hinduction Hubxn before r; intros;
    inv Heqy; inj_existT; subst; use_simpobs.
    + pclearbot. rewrite Heqoubx. gstep. constructor.
      gfinal. left. eapply CIH with (seq' := peel_vis taa e0 a seq'  ) ; eauto.
      * intros. eapply peel_vis_upper_bound_aux; eauto. Unshelve. 3 : apply k0.
        intros. rewrite <- Heqtlim. destruct Htlim; apply Hub.
        setoid_rewrite Heqoubx in Hubx. eauto.
      * assert (supremum seq' (Vis e0 k0) ).
        destruct Htlim.
        setoid_rewrite Heqtlim in Hub. setoid_rewrite Heqtlim in Hlub. constructor; auto.
        apply peel_vis_supremum; auto.
    + rewrite Heqoubx. rewrite tau_euttge. eapply IHHubxn; eauto.
      setoid_rewrite Heqoubx in Hubx. setoid_rewrite tau_eutt in Hubx. auto.
Qed.
  

Lemma bind_rec_scott_cont_aux : forall R S T (k : (R -> itree E S) -> (S -> itree E T)) (seq : sequence (R -> itree E S) ) (lim : R -> itree E S),
    (forall (seq : sequence (R -> itree E S) ) lim, supremum seq lim -> supremum (map k seq) (k lim)  ) ->
    supremum seq lim ->
    supremum (map (bind_rec k) seq ) (bind_rec k lim).
Proof.
  intros R S T k seq lim Hk Hlim. assert (Hlim' : supremum seq lim); auto.
  constructor.
  - red. cbn. unfold bind_rec, map, strong_ktree_approx.
    destruct Hlim. intros. 
    eapply strong_itree_approx_bind with (RR := eq).
    + apply Hmon; auto.
    + intros; subst. apply Hk in Hlim'. unfold map in Hlim'.
      destruct Hlim'. eapply Hmon0; eauto.
  - destruct Hlim. cbn. unfold map. cbn. unfold bind_rec, weak_ktree_approx.
    intros. cbn in Hub.
    eapply weak_itree_approx_bind; eauto. apply Hub.
    intros; subst. specialize (Hk seq lim Hlim'). destruct Hk. 
    cbn in *. apply Hub0.
  - eapply bind_rec_scott_cont_aux_lub; eauto.
Qed.

Lemma bind_rec_scott_cont : forall R S T (k : (R -> itree E S) -> (S -> itree E T)),
    monotone_fun k ->
    weak_monotone_fun k ->
    scott_continuous k ->
    scott_continuous (bind_rec k).
Proof.
  intros. red. cbn. red in H1. cbn in H1.
  intros.
  assert (forall (seq : sequence (R -> itree E S) ) lim, supremum seq lim -> supremum (map k seq) (k lim)).
  { clear H2 seq. intros seq lim Hlim.  auto.
    assert (weak_eq lim (sup seq) ).
    eapply supremum_unique; eauto. apply E_ktree_cpo_laws.
    apply CPO.sup_correct; destruct Hlim; auto. 
    assert (monotone_seq (map k seq) ).
    red. unfold map. intros. eapply H. eauto. destruct Hlim; eauto.
    constructor; auto.
    - assert (monotone_seq seq). destruct Hlim; auto.
      cbn. unfold weak_ktree_approx. intros.
      eapply H0. destruct Hlim; auto.
    - intros. cbn in *. unfold weak_ktree_approx. intros.
      eapply weak_itree_approx_trans_eq with (t2 := k (ktree_approx_sup taa seq) x).
      + eapply H0. cbn. unfold weak_ktree_approx. intros. rewrite H2.
        apply weak_itree_approx_refl.
      + unfold map, weak_ktree_approx in H3. rewrite H1. 2 : destruct Hlim; auto.
        unfold ktree_approx_sup. apply sup_is_below_all_upper_bounds; try (destruct Htaa; auto; fail).
        constructor; red; intros; subst; auto.
        red. unfold apply_seq, map. intros. eapply H3; eauto.
         unfold weak_ktree_approx in H4. intros. apply H4.
   }
  specialize (bind_rec_scott_cont_aux R S T k seq (sup seq) H3 ) as Hscott.
  assert (supremum seq (sup seq)). apply CPO.sup_correct. auto.
  specialize (Hscott H4). 
  enough (weak_eq (bind_rec k (ktree_approx_sup taa seq)) (ktree_approx_sup taa (map (bind_rec k) seq))); auto. 
  eapply supremum_unique with (seq := map (bind_rec k) seq). apply  E_ktree_cpo_laws.
  - apply bind_rec_scott_cont_aux; auto.
  - enough (supremum (map (bind_rec k) seq) (sup (map (bind_rec k) seq) ) ); auto.
    apply CPO.sup_correct. destruct Hscott; auto.
Qed.

Definition ktree_fix {R S E} taa (f : (R -> itree E S) -> (R -> itree E S) ) : R -> itree E S :=
  @weak_cpo_fix (R -> itree E S) f (ktree_weak_cpo taa) (ktree_pointed_weak_cpo taa).

End Fixable.
