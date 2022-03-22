From Coq Require Import Morphisms String.

From ITree Require Import
     ITree
     ITreeFacts
     HeterogeneousRelations
     Events.MapDefault
     Events.State
     Events.StateFacts
     Events.Exception
     Events.ExceptionFacts
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.StrongBisimProper
.

From SecureExample Require Import
     Utils_tutorial
     LabelledImpInline
     LabelledImpHandler
     Lattice
     LabelledAsm
     LabelledImpInline2AsmNoninterferencePres
     LabelledImpInline2AsmCorrectness
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Section LabelledImpTypes.

Ltac case_leq l1 l2 := destruct (leq_dec sensitivity_lat l1 l2) as [Hleq | Hnleq].

Notation privacy_map := LabelledImp.privacy_map.

Definition labelled_equiv (Γ : privacy_map sensitivity_lat) (l : sensitivity) (σ1 σ2 : map)  : Prop :=
  forall x, leq (Γ x) l -> σ1 x = σ2 x.

Definition top2 {A B} : A -> B -> Prop := fun _ _ => True.

Instance labelled_equit_equiv {Γ l} : Equivalence (labelled_equiv Γ l).
Proof.
  constructor; unfold labelled_equiv.
  - red. intros; auto.
  - red. intros. symmetry; auto.
  - red. intros. rewrite H; auto.
Qed.

Notation impExcE := LabelledImp.impExcE.
Notation IOE := LabelledImp.IOE.
Notation E0 := (impExcE sensitivity_lat +' IOE sensitivity_lat).
Definition label_eqit_secure_impstate  (b1 b2 : bool) (Γ : privacy_map sensitivity_lat) (l : sensitivity) {R1 R2 : Type} (RR : R1 -> R2 -> Prop )
           (m1 : stateT (registers * map) (itree E0) R1)
           (m2 : stateT (registers * map ) (itree E0) R2) : Prop :=
  forall σ1 σ2 regs1 regs2, labelled_equiv Γ l σ1 σ2 -> eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 (labelled_equiv Γ l)) RR) b1 b2 l (m1 (regs1,σ1)) (m2 (regs2, σ2)).

Definition label_state_sec_eutt {R1 R2} priv l (RR : R1 -> R2 -> Prop) m1 m2 :=
  label_eqit_secure_impstate true true  priv l RR m1 m2.

#[local] Notation interp_imp_inline := (interp_imp_inline (E1 := impExcE sensitivity_lat) (E2 := IOE sensitivity_lat)).

Definition sem_stmt (s : stmt) := interp_imp_inline (denote_stmt s).

Definition sem_throw_stmt (s : stmt) := interp_imp_inline (throw_prefix (denote_stmt s) ).

Definition sem_expr (e : expr) := interp_imp_inline (denote_expr e).

Definition state_equiv {E R} (m1 m2 : stateT map (itree E) R) := forall (σ : map), m1 σ ≈ m2 σ.

Global Instance proper_eutt_secure_eutt  {E R1 R2 RR Label priv l} : Proper (@eutt E R1 R1 eq ==> @eutt E R2 R2 eq ==> iff)
                                                               (eqit_secure Label priv RR true true l).
Proof.
  eapply proper_eqit_secure_eqit.
Qed.

Global Instance proper_eq_itree_secure_eutt  {E R1 R2 RR Label priv l} : Proper (@eq_itree E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> iff)
                                                               (eqit_secure Label priv RR true true l).
Proof.
  repeat intro. assert (x ≈ y). rewrite H. reflexivity.
  assert (x0 ≈ y0). rewrite H0. reflexivity. rewrite H1. rewrite H2. tauto.
Qed.


(* not sure what is going on with this instance
Global Instance proper_state_equiv_label_state_sec_eutt {R1 R2 RR priv l} : Proper (@state_equiv _ R1 ==> @state_equiv _ R2 ==> iff) (@label_state_sec_eutt R1 R2 priv l RR).
Proof.
  repeat intro. split.
  - intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1). eapply proper_eutt_secure_eutt; eauto. symmetry. auto. symmetry. auto.
  - intros. intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1).  eapply proper_eutt_secure_eutt; eauto.
Qed.
*)
Context (Γ : privacy_map sensitivity_lat).

Variant secure_stmt_at_label (observer pc : sensitivity) (s : stmt) : Prop :=
  | ssal_leq : (leq pc observer) -> label_state_sec_eutt Γ observer eq (sem_stmt s) (sem_stmt s) -> secure_stmt_at_label observer pc s
  | ssal_nleq : (~ leq pc observer) -> label_state_sec_eutt Γ observer top2 (sem_stmt s) (ret tt) -> secure_stmt_at_label observer pc s.


Variant secure_expr_at_label (observer protection: sensitivity ) (e : expr) : Prop :=
  | seal_leq : (leq protection observer) -> label_state_sec_eutt Γ observer eq (sem_expr e) (sem_expr e) ->
               secure_expr_at_label observer protection e
  | seal_nleq : (~leq protection observer) -> (exists n:value, label_state_sec_eutt Γ observer top2 (sem_expr e) (ret n)) ->
                secure_expr_at_label observer protection e
.

Definition secure_expr l e := forall observer, secure_expr_at_label observer l e.

Definition secure_stmt pc s := forall observer, secure_stmt_at_label observer pc s.

Variant is_inl {A B : Type} : A + B -> Prop :=
  | is_inl_ev (a : A) : is_inl (inl a).

Variant secure_throw_stmt_at_label (observer pc : sensitivity) (s : stmt) : Prop :=
  | stsal_leq : leq pc observer -> label_state_sec_eutt Γ observer (sum_rel eq (fun l1 l2 => eqlat l1 bot /\ eqlat l2 bot) )
                                                       (sem_throw_stmt s) (sem_throw_stmt s) -> secure_throw_stmt_at_label observer pc s
  | stsal_nleq : (~ leq pc observer) -> label_state_sec_eutt Γ observer (fun sum _ => is_inl sum )
                                                            (sem_throw_stmt s) (ret tt ) ->  secure_throw_stmt_at_label observer pc s.

Definition secure_throw_stmt pc s := forall observer, secure_throw_stmt_at_label observer pc s.

Lemma expr_only_ret_aux1 e observer: forall (n : nat), label_state_sec_eutt Γ observer top2 (sem_expr e) (ret n) .
Proof.
  do 2 red. induction e; intros; unfold sem_expr; cbn; unfold interp_imp.
  - eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity. cbn.
    apply secure_eqit_ret. split; cbv; auto.
  - rewrite interp_state_ret. apply secure_eqit_ret. split; cbv; auto.
  - repeat setoid_rewrite interp_state_bind.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
    assert ( t ≈ ITree.bind (Ret (regs2, σ2, n)) (fun st => ITree.bind (Ret (fst st, n) ) (fun st => Ret (fst st,n))  )  ) end.
    repeat rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H0; try reflexivity.
    eapply secure_eqit_bind; try apply IHe1; eauto. intros [? ?] [? ?] [? ?]. inv H1. cbn in *. destruct p; destruct p0. cbn in *.
    eapply secure_eqit_bind; try apply IHe2; eauto. intros. cbn in *.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; auto.
    split; auto. cbn. inv H1. inv H5. etransitivity; eauto. reflexivity.
  - repeat setoid_rewrite interp_state_bind.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
    assert ( t ≈ ITree.bind (Ret (regs2, σ2, n)) (fun st => ITree.bind (Ret (fst st, n) ) (fun st => Ret (fst st,n))  )  ) end.
    repeat rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H0; try reflexivity.
    eapply secure_eqit_bind; try apply IHe1; eauto. intros [? ?] [? ?] [? ?]. inv H1. cbn in *. destruct p; destruct p0. cbn in *.
    eapply secure_eqit_bind; try apply IHe2; eauto. intros. cbn in *.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; auto.
    split; auto. cbn. inv H1. inv H5. etransitivity; eauto. reflexivity.
  - repeat setoid_rewrite interp_state_bind.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
    assert ( t ≈ ITree.bind (Ret (regs2, σ2, n)) (fun st => ITree.bind (Ret (fst st, n) ) (fun st => Ret (fst st,n))  )  ) end.
    repeat rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H0; try reflexivity.
    eapply secure_eqit_bind; try apply IHe1; eauto. intros [? ?] [? ?] [? ?]. inv H1. cbn in *. destruct p; destruct p0. cbn in *.
    eapply secure_eqit_bind; try apply IHe2; eauto. intros. cbn in *.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; auto.
    split; auto. cbn. inv H1. inv H5. etransitivity; eauto. reflexivity.
Qed.

Lemma expr_only_ret e observer:  exists n : value, label_state_sec_eutt Γ observer top2 (sem_expr e) (ret n) .
Proof.
  exists 0. apply expr_only_ret_aux1.
Qed.

Hint Resolve sensitivity_latlaws : core.

Lemma secure_expr_upward_close e l1 l2 : leq l1 l2 ->
                                         secure_expr l1 e -> secure_expr l2 e.
Proof.
  intros Hl He observer. specialize (He observer).
  inv He.
  - case_leq l2 observer.
    + left; auto.
    + right; auto. apply expr_only_ret.
  - case_leq l2 observer.
    + exfalso. eapply H. eapply leq_trans_lat; eauto.
    + right; auto.
Qed.

Lemma state_secure_eutt_equiv_ret_aux:
  forall R RR t1 t2 (observer : sensitivity) (r1 r2 : R),
    Equivalence RR ->
    RR r1 r2 ->
    (forall (σ1 σ2 : map) (regs1 regs2 : registers),
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 (labelled_equiv Γ observer)) RR) true
                    true observer (interp_imp_inline t1 (regs1,σ1)) (Ret(regs2, σ2,r1))) ->
    (forall (σ1 σ2 : map) (regs1 regs2 : registers),
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 (labelled_equiv Γ observer)) RR) true
                    true observer (interp_imp_inline t2 (regs1,σ1)) (Ret(regs2, σ2,r2))) ->
    forall (σ1 σ2 : map) (regs1 regs2 : registers),
      labelled_equiv Γ observer σ1 σ2 ->
      eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 (labelled_equiv Γ observer)) RR) true
                  true observer (interp_imp_inline t1 (regs1, σ1))
                  (interp_imp_inline t2 (regs2, σ2)).
Proof.
  intros R RR t1 t2 observer r1 r2 HRR Hr12 Hr1 Hr2 s1 s2 reg1 regs2 Hs12.
  set ((product_rel (product_rel top2 (labelled_equiv Γ observer)) RR)) as Rst.
  apply eqit_secure_RR_imp with (RR1 := rcompose Rst Rst).
  { intros [ [? ?] ?] [ [? ? ] ?] [? ?]. destruct r5. cbn in *. unfold Rst in *.
    inv REL1. inv REL2.
    split. split; [cbv; auto | cbn in *].
    - inv H. inv H1. cbn in *. etransitivity; eauto.
    - inv H1. inv H. cbn in *. etransitivity; eauto.
  }
  eapply eqit_secure_trans; eauto. eapply eqit_secure_sym.
  apply eqit_secure_RR_imp with (RR1 := Rst).
  { intros. split.
    split; [cbv; auto | unfold Rst in *].
    inv PR. inv H. symmetry. auto. inv PR. symmetry. auto.
  }
  assert (eqit_secure _ (priv_exc_io _) Rst true true observer (Ret (regs2, s2, r2) ) (Ret (regs2, s2,r1))).
  { apply secure_eqit_ret. unfold Rst in *. split; auto; cbv; auto. symmetry. auto. }
  apply eqit_secure_RR_imp with (RR1 := rcompose Rst Rst).
  {
    intros [ [? ?] ?] [ [? ? ] ?] [? ?]. destruct r5. cbn in *. unfold Rst in *.
    inv REL1. inv REL2.
    split. split; [cbv; auto | cbn in *].
    - inv H0. inv H2. cbn in *. etransitivity; eauto.
    - inv H0. inv H2. cbn in *. etransitivity; eauto.
  }
  eapply eqit_secure_trans; try apply Hr2; eauto. reflexivity.
Qed.

Lemma state_secure_eutt_throw_ret_aux:
  forall t1 t2  (observer : sensitivity),
    label_state_sec_eutt Γ observer
                         (fun (sum : unit + sensitivity) (_ : unit) =>
                            is_inl sum) (interp_imp_inline (throw_prefix t1))
                         (ret tt) ->
    label_state_sec_eutt Γ observer
                         (fun (sum : unit + sensitivity) (_ : unit) =>
                            is_inl sum) (interp_imp_inline (throw_prefix t2))
                         (ret tt) ->
    forall (σ3 σ4 : map) (regs1 regs2 : registers),
      labelled_equiv Γ observer σ3 σ4 ->
      eqit_secure _ (priv_exc_io sensitivity_lat)
                  (product_rel (product_rel top2 (labelled_equiv Γ observer))
                               (sum_rel eq
                                        (fun l1 l2 : sensitivity =>
                                           eqlat l1 bot /\ eqlat l2 bot))) true
                  true observer
                  (interp_imp_inline
                                (throw_prefix t1) (regs1, σ3))
                  (interp_imp_inline
                                (throw_prefix t2) (regs2, σ4)).
Proof.
  intros t1 t2 observer Ht1 Ht2 σ3 σ4 regs1 regs2 Hσ.
  do 2 red in Ht1, Ht2. cbn in *. set (product_rel
             (@product_rel registers _ registers _ top2 (labelled_equiv Γ observer))
             (fun (sum : unit + sensitivity)
                (_ : unit) => is_inl sum)) as Rst.
  set (product_rel (@product_rel registers _ registers _ top2 (labelled_equiv Γ observer)) (fun (sum1 sum2 : unit + sensitivity) => is_inl sum1 /\ is_inl sum2)  ) as Rst'.
  eapply eqit_secure_RR_imp with (RR1 := Rst').
  { unfold Rst'.
    intros [ [? ?] [ [] | ?] ] [ [? ?] [ [] | ?] ] [ [? ?] [? ?] ]; cbn in *; inv H1; inv H2.
    split. split; auto. cbn. constructor. auto.
  }
  eapply eqit_secure_RR_imp with (RR1 := rcompose Rst (rcompose eq (fun x1 x2 => Rst x2 x1)) ).
  { unfold Rst.
    intros [ [? ?] [ [] | ?] ] [ [? ?] [ [] | ?] ]; intro Hrcomp; unfold Rst'.
    - split. split; auto. cbv. auto. cbn. inv Hrcomp. inv REL1. inv H. inv REL2. inv REL0. etransitivity; eauto.
      cbn in *. inv H. symmetry. auto. split; constructor.
    - inv Hrcomp. inv REL2. inv REL3. inv H0.
    - inv Hrcomp. inv REL2. inv REL3. inv REL1. inv H1. inv H2.
    - inv Hrcomp. inv REL2. inv REL3. inv REL1. inv H1. inv H2.
  }
  eapply eqit_secure_trans; try eapply Ht1; eauto. eapply eqit_secure_trans with (t2 := (Ret (regs2, σ4, tt) ) ).
  apply secure_eqit_ret. reflexivity. auto. apply eqit_secure_sym. eapply Ht2. reflexivity.
Qed.


Lemma state_secure_eutt_ret_aux:
  forall R t1 t2 (observer : sensitivity) (r1 r2 : R),
    (forall (σ1 σ2 : map) (regs1 regs2 : registers),
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 (labelled_equiv Γ observer)) (@top2 R R)) true
                    true observer (interp_imp_inline t1 (regs1, σ1)) (Ret(regs2, σ2,r1))) ->
    (forall (σ1 σ2 : map) (regs1 regs2 : registers),
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 (labelled_equiv Γ observer)) (@top2 R R)) true
                    true observer (interp_imp_inline t2 (regs1, σ1)) (Ret(regs2, σ2,r2))) ->
    (forall (σ1 σ2 : map) (regs1 regs2 : registers),
      labelled_equiv Γ observer σ1 σ2 ->
      eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 (labelled_equiv Γ observer)) top2) true
                  true observer (interp_imp_inline t1 (regs1, σ1))
                  (interp_imp_inline t2 (regs2, σ2))).
Proof.
  intros. eapply state_secure_eutt_equiv_ret_aux; eauto. 2 : cbv; auto.
  constructor; constructor.
Qed.
Notation update := LabelledImp.update.
Lemma update_labelled_equiv_invisible:
  forall (x : var) (observer : sensitivity) Γ,
    ~ leq (Γ x) observer ->
    forall (σ1 : map) (v : value) (σ2 : map),
      labelled_equiv Γ observer σ1 σ2 -> labelled_equiv Γ observer (update x v σ1) (σ2).
Proof.
  intros x observer Γ' H σ1 v σ2 H2.
  red. red in H2. intros.
  unfold update. destruct (x =? x0) eqn : Heq; auto.
  exfalso. apply H. apply eqb_eq in Heq. subst; auto.
Qed.

Lemma update_labelled_equiv_visible:
  forall (x : var) (observer : sensitivity) Γ,
    leq (Γ x) observer ->
    forall (σ1 : map) (v : value) (σ2 : map),
      labelled_equiv Γ observer σ1 σ2 -> labelled_equiv Γ observer (update x v σ1) (update x v σ2).
Proof.
  intros x observer Γ' H σ1 v σ2 H2.
  red. red in H2. intros. unfold update.
  destruct (x =? x0) eqn : Heq; auto.
Qed.

Lemma assign_well_typed_correct x e pc l : secure_expr l e -> leq (join l pc) (Γ x) -> secure_stmt pc (Assign x e).
Proof.
  intros Hle Hx.
  assert (Hpc : leq pc (Γ x) ).
  { eapply leq_trans_lat; eauto. apply leq_join_r; auto. }
  assert (Hl : leq l (Γ x) ).
  { eapply leq_trans_lat; try apply Hx; auto. apply leq_join_l; eauto. }
  assert (He : secure_expr (Γ x) e ).
  { eapply secure_expr_upward_close with (l2:= Γ x); eauto. }
  intros observer.
  specialize ( He observer). inv He.
  - left. eapply leq_trans_lat; eauto.
    do 2 red in H0. do 2 red. intros. unfold sem_stmt.
    cbn. unfold interp_imp. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? ?] [? ?] [? ?].
    cbn in H2, H3. subst. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
    cbn. inv H2. destruct p; destruct p0. apply secure_eqit_ret; split; auto. cbn.
    split; auto. cbn in *; subst. apply update_labelled_equiv_visible; auto.
  - case_leq pc observer.
    + left; auto.
      destruct H0 as [n Hn]. unfold sem_stmt.
      cbn. unfold interp_imp_inline, interp_asm. do 2 red. intros. setoid_rewrite interp_state_bind.
      do 2 red in Hn.
      eapply secure_eqit_bind with (RR := product_rel (product_rel top2 (labelled_equiv Γ observer)) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [ [? ?] ?] [ [? ?] ?] [ [? ?] ?]. cbn in *. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn. apply secure_eqit_ret. split. 2 : cbv; auto. split; cbn; auto.
      apply update_labelled_equiv_invisible; auto. symmetry.
      apply update_labelled_equiv_invisible;  auto.
      symmetry; auto.
    + right; auto.
      destruct H0 as [n Hn]. unfold sem_stmt. cbn.
      do 2 red in Hn. do 2 red. intros. unfold sem_stmt. cbn.
      setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [ [? ?] ?] [ [? ?] ?] [ [? ?] ?]. cbn in *.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn.
      apply secure_eqit_ret; split; auto.
      cbn. split; auto. apply update_labelled_equiv_invisible; auto.
Qed.

Lemma throw_prefix_denote_expr e : @throw_prefix sensitivity value (Reg +' Memory +' IOE sensitivity_lat) (denote_expr e) ≈ (ITree.bind (denote_expr e) (fun v => Ret (inl v))).
Proof.
  induction e; cbn.
  - setoid_rewrite bind_trigger. setoid_rewrite throw_prefix_ev.
    apply eqit_Vis. setoid_rewrite throw_prefix_ret. intros. rewrite tau_eutt. reflexivity.
  - rewrite throw_prefix_ret, bind_ret_l. reflexivity.
  - setoid_rewrite throw_prefix_bind. setoid_rewrite IHe1. repeat rewrite bind_bind.
    eapply eqit_bind'; try reflexivity. intros; subst. rewrite bind_ret_l. rewrite throw_prefix_bind.
    rewrite IHe2. repeat rewrite bind_bind. eapply eqit_bind'; try reflexivity. intros; subst. repeat rewrite bind_ret_l.
    rewrite throw_prefix_ret. reflexivity.
  - setoid_rewrite throw_prefix_bind. setoid_rewrite IHe1. repeat rewrite bind_bind.
    eapply eqit_bind'; try reflexivity. intros; subst. rewrite bind_ret_l. rewrite throw_prefix_bind.
    rewrite IHe2. repeat rewrite bind_bind. eapply eqit_bind'; try reflexivity. intros; subst. repeat rewrite bind_ret_l.
    rewrite throw_prefix_ret. reflexivity.
  - setoid_rewrite throw_prefix_bind. setoid_rewrite IHe1. repeat rewrite bind_bind.
    eapply eqit_bind'; try reflexivity. intros; subst. rewrite bind_ret_l. rewrite throw_prefix_bind.
    rewrite IHe2. repeat rewrite bind_bind. eapply eqit_bind'; try reflexivity. intros; subst. repeat rewrite bind_ret_l.
    rewrite throw_prefix_ret. reflexivity.
Qed.

Lemma expr_only_ret' e s : exists n, sem_expr e s ≈ Ret(s, n).
Proof.
  unfold sem_expr, interp_imp_inline, interp_asm. cbn. destruct s.
  induction e.
  - cbn. setoid_rewrite interp_state_trigger. cbn. repeat setoid_rewrite bind_ret_l.
    cbn. eexists; reflexivity.
  - cbn. setoid_rewrite interp_state_ret.
    eexists; reflexivity.
  - destruct IHe1 as [n1 IHn1]. destruct IHe2 as [n2 IHn2].
    cbn. setoid_rewrite interp_state_bind. setoid_rewrite IHn1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_state_bind. setoid_rewrite IHn2.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_state_ret.
    eexists; reflexivity.
  - destruct IHe1 as [n1 IHn1]. destruct IHe2 as [n2 IHn2].
    cbn. setoid_rewrite interp_state_bind. setoid_rewrite IHn1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_state_bind. setoid_rewrite IHn2.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_state_ret.
    eexists; reflexivity.
  - destruct IHe1 as [n1 IHn1]. destruct IHe2 as [n2 IHn2].
    cbn. setoid_rewrite interp_state_bind. setoid_rewrite IHn1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_state_bind. setoid_rewrite IHn2.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_state_ret.
    eexists; reflexivity.
Qed.

Lemma assign_well_typed_correct' x e pc l : secure_expr l e -> leq (join l pc) (Γ x) -> secure_throw_stmt pc (Assign x e).
Proof.
  intros Hle Hx.
  assert (Hpc : leq pc (Γ x) ).
  { eapply leq_trans_lat; eauto. apply leq_join_r; auto. }
  assert (Hl : leq l (Γ x) ).
  { eapply leq_trans_lat; try apply Hx; auto. apply leq_join_l; eauto. }
  assert (He : secure_expr (Γ x) e ).
  { eapply secure_expr_upward_close with (l2:= Γ x); eauto. }
  intros observer.
  specialize ( He observer). inv He.
  - left. eapply leq_trans_lat; eauto.
    do 2 red in H0. do 2 red. intros. unfold sem_throw_stmt.
    cbn. setoid_rewrite throw_prefix_bind. unfold interp_imp_inline, interp_asm. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind with (RR := product_rel (product_rel top2 (labelled_equiv Γ observer)) (fun sum1 sum2 => sum1 = sum2 /\ is_inl sum1) ).
    + intros [[ regs3 σ3] [v1 | l1] ] [ [regs4 σ4] [v2 | l2] ] [ [ _ Hσ] Hr]; inv Hr; try inv H3; try discriminate.
      cbn. cbn in H2. inv H2. setoid_rewrite throw_prefix_ev. setoid_rewrite interp_state_vis. cbn.
      repeat rewrite bind_ret_l. setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_tau. setoid_rewrite interp_state_ret.
      cbn. eapply proper_eutt_secure_eutt; repeat rewrite tau_eutt; try reflexivity. apply secure_eqit_ret.
      split; cbn; auto. split. cbv; auto. cbn in *. apply update_labelled_equiv_visible; auto.
    + eapply proper_eutt_secure_eutt. eapply eutt_interp_state_eq. apply throw_prefix_denote_expr. reflexivity.
      reflexivity.
      setoid_rewrite interp_state_bind. setoid_rewrite throw_prefix_denote_expr.
      setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind; eauto. intros [ [regs3 σ3] v1] [ [regs4 σ4] v2] [ [ _ Hσ] Hr]. cbn in Hr; subst. setoid_rewrite interp_state_ret. apply secure_eqit_ret. split; auto. split; auto. red. auto. cbn. split; auto. constructor.
  - case_leq pc observer.
    + left; auto.
      destruct H0 as [n Hn]. unfold sem_throw_stmt.
      cbn. unfold interp_imp_inline, interp_asm. do 2 red. intros. setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
      setoid_rewrite interp_state_bind. repeat rewrite bind_bind.
      assert (label_state_sec_eutt Γ observer top2
         (sem_expr e) (sem_expr e)).
      { do 2 red. intros. eapply state_secure_eutt_ret_aux; eauto; apply Hn. }
      eapply secure_eqit_bind; try apply H1; auto. intros [ [regs3 σ3] v1] [ [regs4 σ4] v2] [ [ _ Hσ] Hv].
      setoid_rewrite interp_state_ret. cbn. setoid_rewrite bind_ret_l. cbn. setoid_rewrite throw_prefix_ev.
      setoid_rewrite interp_state_vis. cbn. setoid_rewrite bind_ret_l. setoid_rewrite interp_state_tau.
      eapply proper_eutt_secure_eutt; repeat rewrite tau_eutt; try reflexivity.
      setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret. cbn. apply secure_eqit_ret.
      split; cbn; try constructor; auto. cbn.
      apply update_labelled_equiv_invisible; auto. symmetry.
      apply update_labelled_equiv_invisible;  auto. symmetry. auto.
    + right; auto.
      destruct H0 as [n Hn]. unfold sem_throw_stmt. cbn.
      assert (label_state_sec_eutt Γ observer top2
         (sem_expr e) (sem_expr e)).
      { do 2 red. intros. eapply state_secure_eutt_ret_aux; eauto; apply Hn. }
      do 2 red. intros. unfold interp_imp_inline, interp_asm.
      setoid_rewrite throw_prefix_bind. unfold interp_imp. setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
      specialize (expr_only_ret' e (regs1, σ1)) as [n' Hn'].
      setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite Hn'; try reflexivity. rewrite bind_bind.
      rewrite bind_ret_l. setoid_rewrite interp_state_ret. rewrite bind_ret_l. cbn.
      setoid_rewrite throw_prefix_ev. setoid_rewrite interp_state_vis. cbn. rewrite bind_ret_l.
      rewrite interp_state_tau. eapply proper_eutt_secure_eutt; repeat rewrite tau_eutt; try reflexivity.
      setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret. cbn. apply secure_eqit_ret.
      split; try constructor; auto. cbn. constructor. cbn. apply update_labelled_equiv_invisible; auto.
Qed.



Lemma assign_only_ret e x σ regs : exists σ', sem_stmt (Assign x e) (regs, σ) ≈ Ret (regs, σ', tt).
Proof.
  unfold sem_stmt, interp_imp_inline, interp_asm. cbn.
  setoid_rewrite interp_state_bind. specialize (expr_only_ret' e (regs, σ) ) as He.
  destruct He as [n Hn]. setoid_rewrite Hn. setoid_rewrite bind_ret_l.
  setoid_rewrite interp_state_trigger. cbn. eexists; reflexivity.
Qed.

Lemma output_well_typed_correct l1 le pc e :
  secure_expr le e -> leq (join le pc) l1 ->
  secure_stmt pc (Output l1 e).
Proof.
  intros He0 Hle1.
  assert (Hle : leq le l1).
  { eapply leq_trans_lat; eauto. apply leq_join_l; auto. }
  assert (Hpc : leq pc l1).
  { eapply leq_trans_lat; try apply Hle1; auto. apply leq_join_r; eauto.  }
  assert (He : secure_expr l1 e ).
  { eapply secure_expr_upward_close with (l1 := le); eauto. }
  intros observer. specialize (He observer).
  inv He.
  - assert (Hobs : leq pc observer). eapply leq_trans_lat; eauto.
    left; auto.
    do 2 red in H0. do 2 red. intros. unfold sem_stmt. cbn.
    unfold interp_imp_inline, interp_asm. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [ [? ?] ?] [ [? ?] ?] [ [_ ?] ?].
    cbn in H2, H3. subst. cbn. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
    cbn. setoid_rewrite bind_trigger. cbn.
    apply eqit_secure_public_Vis; try apply H.
    intros []. apply secure_eqit_ret; auto. split; auto. split; auto. cbv; auto.
  - case_leq pc observer.
    + left; auto. destruct H0 as [n Hn]. do 2 red in Hn. cbn in Hn.
      unfold sem_stmt. cbn. unfold interp_imp_inline, interp_asm. do 2 red.
      intros. setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind with (RR := product_rel (product_rel top2 (labelled_equiv Γ observer)) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn in H1. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn. setoid_rewrite bind_trigger. apply eqit_secure_private_VisLR; auto.
      constructor; apply tt. constructor; apply tt. intros [] [].
      apply secure_eqit_ret. repeat (split; auto).
    + right; auto. destruct H0 as [n Hn]. do 2 red in Hn.
      do 2 red. intros. unfold sem_stmt. cbn.
      unfold interp_imp_inline, interp_asm. setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [ [? ?] ?] [ [? ?] ?] [ [? ?] ?]. cbn in *.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn. setoid_rewrite bind_trigger. cbn.
      apply eqit_secure_private_VisL; auto. constructor; apply tt.
      intros []. apply secure_eqit_ret; auto. repeat (split; auto).
Qed.

Notation E1 := (Reg +' Memory +' IOE sensitivity_lat).

Lemma throw_prefix_output l1 e : throw_prefix (E := E1) (denote_stmt (Output l1 e) ) ≈
        v <- denote_expr e;; trigger (LabelledImp.LabelledPrint sensitivity_lat l1 v);; Ret (inl tt).
Proof.
  cbn. rewrite throw_prefix_bind. rewrite throw_prefix_denote_expr. rewrite bind_bind.
  eapply eqit_bind'; try reflexivity. intros; subst. rewrite bind_ret_l. setoid_rewrite throw_prefix_ev.
  rewrite bind_trigger. apply eqit_Vis. intros []. rewrite tau_eutt. rewrite throw_prefix_ret. reflexivity.
Qed.

Lemma output_well_typed_correct' l1 le pc e :
  secure_expr le e -> leq (join le pc) l1 ->
  secure_throw_stmt pc (Output l1 e).
Proof.
  intros He0 Hle1.
  assert (Hle : leq le l1).
  { eapply leq_trans_lat; eauto. apply leq_join_l; auto. }
  assert (Hpc : leq pc l1).
  { eapply leq_trans_lat; try apply Hle1; auto. apply leq_join_r; eauto.  }
  assert (He : secure_expr l1 e ).
  { eapply secure_expr_upward_close with (l1 := le); eauto. }
  intros observer. specialize (He observer).
  inv He.
  - assert (Hobs : leq pc observer). eapply leq_trans_lat; eauto.
    left; auto.
    do 2 red in H0. do 2 red. intros. unfold sem_throw_stmt.
     unfold interp_imp_inline, interp_asm.
    eapply proper_eutt_secure_eutt; try rewrite throw_prefix_output; try reflexivity.
    setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto.
    intros [ [? ?] ?] [ [? ?] ?] [ [ _ ?] ?].
    cbn in H2, H3. subst. cbn. eapply proper_eutt_secure_eutt; try rewrite interp_state_bind, interp_state_trigger; try reflexivity.
    cbn. setoid_rewrite bind_trigger. setoid_rewrite bind_vis.
    apply eqit_secure_public_Vis; try apply H.
    intros []. setoid_rewrite bind_ret_l. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    cbn. split; auto. repeat (split; auto). constructor. auto.
  - case_leq pc observer.
    + left; auto. destruct H0 as [n Hn]. do 2 red in Hn. cbn in Hn.
      unfold sem_throw_stmt. do 2 red. intros. unfold interp_imp_inline, interp_asm.
      eapply proper_eutt_secure_eutt; try rewrite throw_prefix_output; try reflexivity.
      cbn. unfold interp_imp.
      setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind with (RR := product_rel (product_rel top2 (labelled_equiv Γ observer)) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [ [? ?] ?] [ [? ?] ?] [ [ _ ?] ?]. cbn in H2.
      setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite interp_state_trigger; try reflexivity. cbn.
      setoid_rewrite bind_bind. setoid_rewrite bind_trigger. apply eqit_secure_private_VisLR; auto.
      all : try (constructor; apply tt; fail). intros [] []. setoid_rewrite bind_ret_l.
      setoid_rewrite interp_state_ret. apply secure_eqit_ret. split; try constructor; auto.
    + right; auto. destruct H0 as [n Hn]. do 2 red in Hn.
      do 2 red. intros. unfold sem_throw_stmt.
      unfold interp_imp_inline, interp_asm.
      eapply proper_eutt_secure_eutt; try rewrite throw_prefix_output; try reflexivity.
      setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [ [? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn. setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try rewrite interp_state_trigger; try reflexivity. cbn.
      rewrite bind_bind, bind_trigger. apply eqit_secure_private_VisL; auto. constructor; constructor.
      intros []. rewrite bind_ret_l. rewrite interp_state_ret.
      apply secure_eqit_ret; auto. repeat (split; auto).
Qed.

Lemma seq_well_typed_correct pc s1 s2 :
  secure_stmt pc s1 -> secure_stmt pc s2 ->
  secure_stmt pc (Seq s1 s2).
Proof.
  intros Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  inv Hc1obs.
  - do 2 red in H0. left; auto. unfold sem_stmt.
    cbn. unfold interp_imp_inline, interp_asm. do 2 red. intros. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [ [ ? ?] [] ] [ [ ? ?] [] ] [ [ _ ?] ?].
    cbn in *. clear H3. cbn.
    inv Hc2obs; try apply H4; auto.
    do 2 red in H4.
    eapply eqit_secure_RR_imp with (RR1 := product_rel (product_rel top2 ( labelled_equiv Γ observer)) top2 ).
    { intros [ ? [] ] [? [] ] [? ?] . split; auto. }
    eapply state_secure_eutt_ret_aux; try apply H4; eauto.
    (* I think this ends up being fine*)
  - right; auto. unfold sem_stmt, interp_imp_inline, interp_asm. cbn. do 2 red. intros.
    setoid_rewrite interp_state_bind.
    inv Hc2obs.
    { exfalso. apply H. auto. }
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
    rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
    eapply secure_eqit_bind; try eapply H0; auto.
    intros [ [ ? ?] ?] [ [? ?] ?] [ [ _ ?] ?]. apply H3; auto.
Qed.

Lemma seq_well_typed_correct' pc s1 s2 :
  secure_throw_stmt pc s1 -> secure_throw_stmt pc s2 ->
  secure_throw_stmt pc (Seq s1 s2).
Proof.
  intros Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  inv Hc1obs.
  - do 2 red in H0. left; auto. unfold sem_throw_stmt.
    cbn. unfold interp_imp_inline, interp_asm. do 2 red. intros. setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto.
    intros [ [ ? σ3] [ [] | ?] ] [ [ ? σ4] [ [] | ? ]] [ [ _ Hσ] Hr] ; inv Hr.
    + cbn. inv Hc2obs; try contradiction. eapply H3; eauto.
    + destruct H4; subst; cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret. split; try constructor; auto.
      constructor.
  - right; auto. unfold sem_throw_stmt, interp_imp_inline, interp_asm. cbn. do 2 red. intros.
    setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    inv Hc2obs; try contradiction.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
    rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
    eapply secure_eqit_bind; try eapply H0; auto.
    intros [ [ ? σ3] [ [] | ?] ] [ [ ? σ4]  [] ] [ [ _ Hσ] Hr] ; inv Hr.
    cbn. eapply H3; eauto.
Qed.

Lemma if_well_typed_correct pc le e s1 s2 :
  secure_expr le e -> secure_stmt (join pc le) s1 -> secure_stmt (join pc le) s2 ->
  secure_stmt pc (If e s1 s2).
Proof.
  intros He Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  specialize (He observer).
  inv Hc1obs; inv Hc2obs; try contradiction.
  - left. eapply leq_trans_lat; eauto. apply leq_join_l; auto.
    inv He. 2 : { exfalso. apply H3. eapply leq_trans_lat; eauto. apply leq_join_r; auto. }
    unfold sem_stmt, interp_imp_inline, interp_asm.
    cbn. do 2 red. intros. setoid_rewrite interp_state_bind. eapply secure_eqit_bind; try apply H4; auto.
    intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn in H6, H7. subst. cbn. destruct v0; eauto.
  - case_leq pc observer.
    + left; auto. unfold sem_stmt, interp_imp_inline, interp_asm. cbn. do 2 red. intros.
      setoid_rewrite interp_state_bind.
      inv He; try contradiction.
      * eapply secure_eqit_bind; try apply H5; eauto.
        intros [ [ ? ?] ?] [ [? ?] ?] [ [ _ ?] ?]. cbn in H7, H6. cbn. subst. do 2 red in H0, H2.
        eapply eqit_secure_RR_imp with (RR1 := product_rel (product_rel top2 (labelled_equiv Γ observer)) top2 ).
        { intros [ [ ? ?] [] ] [ [? ?] [] ] [ [ _ ?] ?]. repeat (split; auto). }
        destruct v0; try eapply  state_secure_eutt_ret_aux; cbn in *; eauto.
      * destruct H5 as [n Hn]. do 2 red in Hn.
        eapply secure_eqit_bind; try eapply  state_secure_eutt_ret_aux; cbn in Hn; eauto.
        intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn. cbn in H6.
        eapply eqit_secure_RR_imp with (RR1 := product_rel (product_rel top2 (labelled_equiv Γ observer)) top2 ).
        { intros [ [ ? ?] [] ] [ [ ? ?] [] ] [ [ _ ?] ?]. repeat (split; auto). }
        destruct v; destruct v0;
        try eapply state_secure_eutt_ret_aux; try apply H0; try apply H2; eauto.
     + right; auto. do 2 red. intros. unfold sem_stmt, interp_imp_inline, interp_asm. cbn.
       setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, 0)) (fun st => Ret (fst st, tt) ))) end.
       rewrite bind_ret_l. reflexivity.
       eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
       inv He.
       * eapply secure_eqit_bind with (RR := product_rel (product_rel top2 (labelled_equiv Γ observer)) top2) .
         2 : {  apply expr_only_ret_aux1; auto. }
         intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn. destruct v; cbn in *; eauto.
       * destruct H6. eapply secure_eqit_bind; try apply expr_only_ret_aux1; auto.
         intros [ [? ?] ?] [ [? ?] ?] [ [ _ ?] ?]. cbn. destruct v; cbn in *; eauto.
Qed.

Lemma if_well_typed_correct' pc le e s1 s2 :
  secure_expr le e -> secure_throw_stmt (join pc le) s1 -> secure_throw_stmt (join pc le) s2 ->
  secure_throw_stmt pc (If e s1 s2).
Proof.
  intros He Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  specialize (He observer).
  inv Hc1obs; inv Hc2obs; try contradiction.
  - left. eapply leq_trans_lat; eauto. apply leq_join_l; auto.
    inv He. 2 : { exfalso. apply H3. eapply leq_trans_lat; eauto. apply leq_join_r; auto. }
    unfold sem_throw_stmt, interp_imp_inline, interp_asm.
    cbn. do 2 red. intros. setoid_rewrite throw_prefix_bind.
    eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
    rewrite bind_bind. setoid_rewrite interp_state_bind; setoid_rewrite bind_ret_l.
    eapply secure_eqit_bind; try apply H4; auto.
    intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn in H6, H7. subst. cbn. destruct v0; eauto.
  - (* ~ leq (join pc le) observer  *)
    case_leq pc observer.
    + (* leq pc observer *)
      left; auto. unfold sem_throw_stmt, interp_imp_inline, interp_asm. cbn. do 2 red. intros.
      setoid_rewrite throw_prefix_bind.
      setoid_rewrite interp_state_bind.
      inv He; try contradiction.
      * (* leq le observer *)
        eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
        setoid_rewrite interp_state_bind. repeat rewrite bind_bind.
        eapply secure_eqit_bind; try eapply H6; eauto.
        setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l; cbn.
        intros [ [ ? σ3] v1 ] [ [? σ4] v2 ] [ [ _ Hσ] Hv]; cbn in Hv; subst. destruct v2; cbn; eauto;
        try eapply state_secure_eutt_throw_ret_aux; eauto.
      * eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
        setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
        destruct H5 as [n Hn].
        eapply secure_eqit_bind; try eapply state_secure_eutt_ret_aux; try eapply Hn; eauto.
        intros [ [ ?  σ3] v1] [ [ ? σ4] v2] [ [ _ Hσ] _ ]. setoid_rewrite interp_state_ret. cbn.
        setoid_rewrite bind_ret_l. cbn. destruct v1; destruct v2; try eapply state_secure_eutt_throw_ret_aux; eauto.
   + (* ~ leq pc observer *)
     right; auto. unfold sem_throw_stmt, interp_imp_inline, interp_asm. cbn. do 2 red. intros. setoid_rewrite throw_prefix_bind.
     setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, 0)) (fun st => Ret (fst st, tt) ))) end.
     rewrite bind_ret_l. reflexivity.
     eapply proper_eutt_secure_eutt; try apply H5; try reflexivity.
     inv He.
     * eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
       eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
       setoid_rewrite interp_state_bind. rewrite bind_bind.
       eapply secure_eqit_bind; try eapply expr_only_ret_aux1; eauto.
       intros [ [ ? σ3] v1] [ [ ? σ4] v2] [ [ _ Hσ] _ ]. setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
       cbn. destruct v1; cbn in *; eauto.
     * destruct H6 as [n Hn]. eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try apply H4; try reflexivity.
       setoid_rewrite interp_state_bind. rewrite bind_bind.
       eapply secure_eqit_bind; try eapply expr_only_ret_aux1; eauto.
       setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
       intros [ [ ? σ3] v1] [ [ ? σ4] v2] [ [ _ Hσ] _ ]. destruct v1; cbn in *; eauto.
Qed.

Lemma while_well_typed_correct e s :
  secure_expr bot e -> secure_stmt bot s ->
  secure_stmt bot (While e s).
Proof.
  intros He Hc. red. intros.
  assert (leq bot observer); cbn; auto.
  specialize (He observer).
  specialize (Hc observer).
  inv He; inv Hc; try contradiction.
  left; auto. unfold sem_stmt, interp_imp. cbn. unfold while.
  specialize @interp_state_iter' as Hisi. red in Hisi. do 2 red. intros.
  setoid_rewrite Hisi. eapply secure_eqit_iter with (RA := product_rel (product_rel top2 (labelled_equiv Γ observer)) eq).
  { repeat (split; auto). }
  intros [ [? ?] [] ] [ [ ? ?] [] ] [ [ _ ?] ?]. cbn.
  setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
  eapply secure_eqit_bind; try apply H1; auto.
  intros [ [ ? ?] ?] [ [? ?] ?] [ [_ ?] ?]. cbn. cbn in H7, H8; subst. destruct v0.
  - setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    apply secure_eqit_ret. constructor. repeat (split; auto).
  - setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
    eapply secure_eqit_bind; try apply H3; auto.
    intros [ [ ? ?] [] ] [ [ ? ?] [] ] [ [ _ ?] ?]. cbn. cbn in H8.
    setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    apply secure_eqit_ret. constructor. repeat (split; auto).
Qed.

Lemma while_well_typed_correct' e s :
  secure_expr bot e -> secure_throw_stmt bot s ->
  secure_throw_stmt bot (While e s).
Proof.
  intros He Hc. red. intros.
  assert (leq bot observer); cbn; auto.
  specialize (He observer).
  specialize (Hc observer).
  inv He; inv Hc; try contradiction.
  left; auto. unfold sem_throw_stmt in *.
  cbn. do 2 red. intros. unfold interp_imp_inline, interp_asm in *. setoid_rewrite throw_prefix_iter.
  specialize @interp_state_iter' as Hisi. red in Hisi.
  setoid_rewrite Hisi. cbn.
  eapply secure_eqit_iter with (RA := product_rel (product_rel top2 (labelled_equiv Γ observer)) eq ).
  repeat (split; auto). intros [ [ ? σ3] [] ] [ [ ? σ4] [] ] [ [ _ Hσ] _]. cbn.
  setoid_rewrite throw_prefix_bind. repeat setoid_rewrite interp_state_bind.
  repeat rewrite bind_bind.
  eapply proper_eutt_secure_eutt;
    try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
  setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
  eapply secure_eqit_bind; try eapply H1; eauto.
  intros [ [ ? σ5] v1] [ [ ? σ6] v2] [ [ _ Hσ'] Heq]; cbn in Heq; subst. cbn.
  setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
  destruct v2.
  - cbn. setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret.
    setoid_rewrite bind_ret_l. cbn. setoid_rewrite interp_state_ret.
    setoid_rewrite bind_ret_l. cbn. apply secure_eqit_ret. constructor. repeat (split; auto).
    constructor. auto.
  - setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    setoid_rewrite bind_bind. eapply secure_eqit_bind; try eapply H3; eauto.
    intros [ [ ? σ7] [ [] | l1] ] [ [ ? σ8] [ [] | l2] ] [ [ _ Hσ''] Hsum]; inv Hsum.
    + cbn. setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret.
      setoid_rewrite bind_ret_l. cbn. setoid_rewrite interp_state_ret.
      setoid_rewrite bind_ret_l. cbn. apply secure_eqit_ret.
      constructor. repeat (split; auto).
    + cbn. setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
      cbn. setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
      cbn. apply secure_eqit_ret. destruct H7; subst. constructor.
      repeat (split; auto). constructor. auto.
Qed.

Lemma well_typed_raise : secure_stmt bot (Raise bot).
Proof.
  red. intros. left. cbn. auto.
  red. red. intros. unfold sem_stmt, interp_imp_inline, interp_asm.
  cbn. setoid_rewrite interp_state_bind. eapply secure_eqit_bind with (RR := eq).
  intros [ _ [] ].
  eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
  cbn. setoid_rewrite bind_trigger. apply eqit_secure_public_Vis.
  cbn. auto. intros [].
Qed.

Lemma well_typed_raise' : secure_throw_stmt bot (Raise bot).
Proof.
  red. intros. left. apply leq_bot; auto.
  red. red. intros. unfold sem_throw_stmt, interp_imp_inline, interp_asm. cbn.
  setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
  eapply secure_eqit_bind with (RR :=  (product_rel (product_rel top2 (labelled_equiv Γ observer)) (fun r1 r2 : void + sensitivity => r1 = inr (@bot sensitivity_lat) /\ r2 = inr  (@bot sensitivity_lat))) ).
  - intros [ [ ? σ3] [ [] | l1 ] ] [ [ ? σ4] [ [] | l2 ] ] Heq; subst. cbn. destruct Heq. cbn in *. subst.
    destruct H1. injection H1; injection H2; intros; subst.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret.
    split; auto. constructor. split; auto.
  - setoid_rewrite throw_prefix_exc. setoid_rewrite interp_state_ret. apply secure_eqit_ret.
    repeat (split; auto).
Qed.


Lemma try_catch_public_exc R RR (t1 t2 catch1 catch2 : itree _ R ) observer :
  label_state_sec_eutt Γ observer (sum_rel RR (fun l1 l2 => eqlat l1 bot /\ eqlat l2 bot) )
                       (interp_imp_inline (throw_prefix t1) ) (interp_imp_inline (throw_prefix t2) )  ->
  label_state_sec_eutt Γ observer RR (interp_imp_inline t1) (interp_imp_inline t2) ->
  label_state_sec_eutt Γ observer RR (interp_imp_inline catch1) (interp_imp_inline catch2) ->
  label_state_sec_eutt Γ observer RR
              (interp_imp_inline (try_catch t1 (fun _ => catch1))) (interp_imp_inline (try_catch t2 (fun _ => catch2))).
Proof.
  unfold interp_imp_inline, interp_asm. intros Hthrow Hsect Hsecc σ1 σ2 regs1 regs2 Hσ.
  (* try_catch_to_throw_prefix *)
  eapply proper_eutt_secure_eutt; try setoid_rewrite try_catch_to_throw_prefix;
    try setoid_rewrite interp_state_bind; try reflexivity.
  eapply secure_eqit_bind; eauto.
  intros [ [ ? σ3] [r1 | l1] ] [ [? σ4] [r2 | l2] ] Htry; destruct Htry as [ [ _ Hσ34] Hsum];
    inv Hsum.
  - cbn. repeat rewrite interp_state_ret. apply secure_eqit_ret.
    repeat (split; auto).
  - destruct H1; subst. cbn. apply Hsecc. auto.
Qed.

Lemma try_catch_throw_secure_stmt pc s catch :
  secure_stmt pc s -> secure_throw_stmt pc s -> secure_stmt pc catch ->
  secure_stmt pc (TryCatch s catch).
Proof.
  intros Hs Hthrows Hcatch. intros observer.
  specialize (Hs observer). specialize (Hthrows observer). specialize (Hcatch observer).
  inv Hs; inv Hthrows; inv Hcatch; try contradiction.
  - left; auto. unfold sem_stmt. cbn. eapply try_catch_public_exc; eauto.
  - right; auto. unfold sem_stmt. cbn. cbn in H2. unfold sem_throw_stmt in H2.
    do 2 red. intros. eapply H0 in H5 as H6. cbn in H6. unfold interp_imp_inline, interp_asm.
    eapply proper_eutt_secure_eutt; try setoid_rewrite try_catch_to_throw_prefix; try reflexivity.
    setoid_rewrite <- bind_ret_r at 6.
    setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto.
    intros [ [ ? σ3] [ [] | l] ] [ [ ? σ4] []] [ [ _ Hσ] Hsum]; inv Hsum. cbn.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; cbv; eauto.
    Unshelve. all : auto.
Qed.

Lemma try_catch_throw_secure_stmt' pc s catch :
  secure_stmt pc s -> secure_throw_stmt pc s -> secure_throw_stmt pc catch ->
  secure_throw_stmt pc (TryCatch s catch).
Proof.
  intros Hs1 Hs2 Hcatch observer.
  specialize (Hs1 observer). specialize (Hs2 observer). specialize (Hcatch observer).
  inv Hs1; inv Hs2; inv Hcatch; try contradiction.
  - left; auto. unfold sem_throw_stmt in *. cbn.
    do 2 red. intros. unfold interp_imp_inline, interp_asm in *.
    eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_of_try_catch;
       try setoid_rewrite try_catch_to_throw_prefix; try reflexivity.
    setoid_rewrite interp_state_bind.
    setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    setoid_rewrite bind_bind. clear H0.
    eapply secure_eqit_bind; try eapply H2; eauto.
    try reflexivity.
    intros [ [ ? σ3] [ [] | l1] ] [ [ ? σ4] [ [] | l2] ] [ [ _ Hσ] Hsum]; inv Hsum; cbn.
    + setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret.
      setoid_rewrite bind_ret_l. cbn. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. repeat (split; auto). constructor. auto.
    + setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
      destruct H7; subst. cbn. eauto.
  - right; auto. unfold sem_throw_stmt in *. cbn.
    do 2 red. intros.
    unfold interp_imp_inline, interp_asm in *.
    eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_of_try_catch;
       try setoid_rewrite try_catch_to_throw_prefix; try reflexivity.
    setoid_rewrite throw_prefix_bind. rewrite bind_bind.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (regs2, σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
     rewrite bind_ret_l. reflexivity.
     eapply proper_eutt_secure_eutt; try rewrite H6; try reflexivity.
     unfold interp_imp_inline, interp_asm. setoid_rewrite interp_state_bind.
     eapply secure_eqit_bind; try eapply H2; eauto.
     intros [ [ ? σ3] [[] | l] ] [ [ ? σ4] [] ] [ [ _ Hσ] Hsum]; inv Hsum.
     cbn. rewrite throw_prefix_ret, bind_ret_l. rewrite interp_state_ret.
     apply secure_eqit_ret. repeat (split; auto).
Qed.

Lemma well_typed_skip pc : secure_stmt pc Skip.
Proof.
  intro observer. case_leq pc observer.
  - left; auto. unfold sem_stmt, interp_imp_inline, interp_asm. do 2 red. intros.
    cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    repeat (split; auto).
  - right; auto. unfold sem_stmt, interp_imp_inline, interp_asm. do 2 red. intros.
    cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    repeat (split; auto).
Qed.

Lemma well_typed_skip' pc : secure_throw_stmt pc Skip.
Proof.
  intro observer. case_leq pc observer.
  - left; auto. unfold sem_throw_stmt, interp_imp_inline, interp_asm. do 2 red. intros.
    cbn. setoid_rewrite throw_prefix_ret.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    repeat (split; auto). constructor. auto.
  - right; auto. unfold sem_throw_stmt, interp_imp_inline, interp_asm. do 2 red. intros.
    cbn. setoid_rewrite throw_prefix_ret.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    repeat (split; auto).
Qed.

Inductive well_typed_expr : sensitivity -> expr -> Prop :=
  | wte_lit l n : well_typed_expr l (Lit n)
  | wte_var x l : leq (Γ x) l -> well_typed_expr l (Var x)
  | wte_plus l1 l2 l3 e1 e2 : well_typed_expr l1 e1 -> well_typed_expr l2 e2 ->
                              eqlat (join l1 l2) l3 ->
                              well_typed_expr l3 (Plus e1 e2)
  | wte_min l1 l2 l3 e1 e2 : well_typed_expr l1 e1 -> well_typed_expr l2 e2 ->
                             eqlat (join l1 l2) l3 ->
                             well_typed_expr l3 (Minus e1 e2)
  | wte_mult l1 l2 l3 e1 e2 : well_typed_expr l1 e1 -> well_typed_expr l2 e2 ->
                              eqlat (join l1 l2) l3 ->
                              well_typed_expr l3 (Mult e1 e2)
.

(* rework this definition to have only public exceptions*)
Inductive well_typed_stmt : sensitivity -> stmt -> Prop :=
  | wts_manual pc s : secure_stmt pc s /\ secure_throw_stmt pc s /\ valid_stmt s -> well_typed_stmt pc s
  | wts_skip pc : well_typed_stmt pc Skip
  | wts_seq pc s1 s2 : well_typed_stmt pc s1 -> well_typed_stmt pc s2 ->
                                   well_typed_stmt pc  (Seq s1 s2)
  | wts_assign pc l x e : well_typed_expr l e -> leq (join l pc) (Γ x) ->
                          well_typed_stmt pc (Assign x e)
  | wts_print pc le lp e : well_typed_expr le e -> leq (join le pc) lp ->
                           well_typed_stmt pc (Output lp e)
  | wts_if pc le e s1 s2 : well_typed_expr le e -> well_typed_stmt (join pc le) s1 -> well_typed_stmt (join pc le) s2 ->
                                       well_typed_stmt pc (If e s1 s2)
  | wts_while e s : well_typed_expr bot e -> well_typed_stmt bot s ->
                         well_typed_stmt bot (While e s)
  | wts_raise : well_typed_stmt bot (Raise bot)
  | wts_try pc s1 s2 : well_typed_stmt pc s1 -> well_typed_stmt pc s2 ->
                                   well_typed_stmt pc (TryCatch s1 s2)
.

Instance proper_eqlat_expr : Proper (eqlat ==> eq ==> Basics.flip Basics.impl) well_typed_expr.
Proof.
  intros l1 l2 Hl e1 e2 He. subst. intro Htype.
  generalize dependent l1. induction Htype.
  - intros. constructor.
  - intros. constructor. destruct sensitivity_latlaws. rewrite Hl. auto.
  - intros. destruct sensitivity_latlaws. rewrite <- H in Hl.
    econstructor; eauto. rewrite Hl. reflexivity.
  - intros. destruct sensitivity_latlaws.
    econstructor; eauto. rewrite Hl. auto.
  - intros. destruct sensitivity_latlaws. rewrite <- H in Hl.
    econstructor; eauto. rewrite Hl. reflexivity.
Qed.

Instance proper_eqlat_expr' : Proper (eqlat ==> eq ==> Basics.impl) well_typed_expr.
Proof.
  intros l1 l2 Hl e1 e2 He. subst. intro Htype.
  generalize dependent l2. induction Htype.
  - intros. constructor.
  - intros. constructor. destruct sensitivity_latlaws. rewrite <- Hl. auto.
  - intros. destruct sensitivity_latlaws. rewrite Hl in H.
    econstructor; eauto.
  - intros. destruct sensitivity_latlaws. rewrite Hl in H.
    econstructor; eauto.
  - intros. destruct sensitivity_latlaws. rewrite Hl in H.
    econstructor; eauto.
Qed.

Lemma well_typed_expr_upward_close l1 l2 e : leq l1 l2 -> well_typed_expr l1 e -> well_typed_expr l2 e.
Proof.
  revert l1 l2.
  induction e; intros; try inv H0.
  - constructor. eapply leq_trans_lat; eauto.
  - constructor.
  - cbn in H. setoid_rewrite <- H. destruct sensitivity_latlaws.
    econstructor; try reflexivity; eauto. eapply IHe1; eauto.
    apply leq_trans_lat with (l2 := join_sense l0 l3); auto.
    apply leq_join_l; auto. rewrite H6. cbn in *. destruct l1; auto.
    eapply IHe2; eauto.
    apply leq_trans_lat with (l2 := join_sense l0 l3); auto.
    apply leq_join_r; auto. rewrite H6. auto.
  - cbn in H. setoid_rewrite <- H. destruct sensitivity_latlaws.
    econstructor; try reflexivity; eauto. eapply IHe1; eauto.
    apply leq_trans_lat with (l2 := join_sense l0 l3); auto.
    apply leq_join_l; auto. rewrite H6. cbn. destruct l1; auto.
    eapply IHe2; eauto.
    apply leq_trans_lat with (l2 := join_sense l0 l3); auto.
    apply leq_join_r; auto. rewrite H6. auto.
  - cbn in H. setoid_rewrite <- H. destruct sensitivity_latlaws.
    econstructor; try reflexivity; eauto. eapply IHe1; eauto.
    apply leq_trans_lat with (l2 := join_sense l0 l3); auto.
    apply leq_join_l; auto. rewrite H6. cbn. destruct l1; auto.
    eapply IHe2; eauto.
    apply leq_trans_lat with (l2 := join_sense l0 l3); auto.
    apply leq_join_r; auto. rewrite H6. auto.
Qed.

Lemma well_typed_expr_correct l e : well_typed_expr l e -> secure_expr l e.
Proof.
  revert l. red. induction e; intros l Htype observer.
  - inv Htype. case_leq l observer.
    + left; auto. unfold sem_expr. cbn. unfold interp_imp_inline, interp_asm.
      do 2 red. intros. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn.
      unfold get. apply secure_eqit_ret; repeat (split; auto). cbn.
      red in H. apply H. eapply leq_trans_lat; eauto.
    + right; auto. apply expr_only_ret.
  - case_leq l observer.
    + left; auto. unfold sem_expr. cbn. unfold interp_imp_inline, interp_asm. do 2 red.
      intros. setoid_rewrite interp_state_ret. apply secure_eqit_ret.
      repeat (split; auto).
    + right; auto. exists 0. unfold sem_expr. cbn. unfold interp_imp_inline, interp_asm. do 2 red.
      intros. setoid_rewrite interp_state_ret. apply secure_eqit_ret. repeat (split; auto).
  - inv Htype.
    assert (well_typed_expr l e1 ). eapply well_typed_expr_upward_close; eauto.
    eapply leq_trans_lat with (l2 := join_sense l1 l2); auto. apply leq_join_l; auto.
    cbn. destruct sensitivity_latlaws. rewrite H4. destruct l; auto.
    assert (well_typed_expr l e2 ). eapply well_typed_expr_upward_close; eauto.
    apply leq_trans_lat with (l2 := join_sense l1 l2); auto. apply leq_join_r; auto.
    cbn. destruct sensitivity_latlaws. rewrite H4. destruct l; auto.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp_inline, interp_asm. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [ [ ? s3] r1] [ [ ? s4] r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H6; eauto.
      intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. repeat (split; auto). inv H7. auto.
    + right; auto. apply expr_only_ret.
  - inv Htype.
    assert (well_typed_expr l e1 ). eapply well_typed_expr_upward_close; eauto.
    eapply leq_trans_lat with (l2 := join_sense l1 l2); auto. apply leq_join_l; auto.
    cbn. destruct sensitivity_latlaws. rewrite H4. destruct l; auto.
    assert (well_typed_expr l e2 ). eapply well_typed_expr_upward_close; eauto.
    apply leq_trans_lat with (l2 := join_sense l1 l2); auto. apply leq_join_r; auto.
    cbn. destruct sensitivity_latlaws. rewrite H4. destruct l; auto.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp_inline, interp_asm. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [ [ ? s3] r1] [ [ ? s4] r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H6; eauto.
      intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. repeat (split; auto). inv H7. auto.
    + right; auto. apply expr_only_ret.
  - inv Htype.
    assert (well_typed_expr l e1 ). eapply well_typed_expr_upward_close; eauto.
    eapply leq_trans_lat with (l2 := join_sense l1 l2); auto. apply leq_join_l; auto.
    cbn. destruct sensitivity_latlaws. rewrite H4. destruct l; auto.
    assert (well_typed_expr l e2 ). eapply well_typed_expr_upward_close; eauto.
    apply leq_trans_lat with (l2 := join_sense l1 l2); auto. apply leq_join_r; auto.
    cbn. destruct sensitivity_latlaws. rewrite H4. destruct l; auto.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp_inline, interp_asm. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [ [ ? s3] r1] [ [ ? s4] r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H6; eauto.
      intros [ [ ? ?] ?] [ [ ? ?] ?] [ [ _ ?] ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. repeat (split; auto). inv H7. auto.
    + right; auto. apply expr_only_ret.
Qed.

Lemma well_typed_stmt_sound s pc : well_typed_stmt pc s -> secure_stmt pc s.
Proof.
  intros Htype. enough (secure_stmt pc s /\ secure_throw_stmt pc s); try tauto.
  induction Htype; eauto; try tauto.
  - (* Skip *) split; try apply well_typed_skip; try apply well_typed_skip'.
  - (* Seq *)
    split; try apply seq_well_typed_correct; try apply seq_well_typed_correct'; tauto.
  - (* Assign *)
    split; try eapply assign_well_typed_correct; try eapply assign_well_typed_correct';
      try apply well_typed_expr_correct; eauto.
  - (* Output *)
    split; try eapply output_well_typed_correct; try eapply output_well_typed_correct';
      try apply well_typed_expr_correct; eauto.
  - (* If *)
    apply well_typed_expr_correct in H.
    split; try eapply if_well_typed_correct; try eapply if_well_typed_correct'; eauto; try tauto.
  - (* While *)
    destruct IHHtype. apply well_typed_expr_correct in H.
    split; try eapply while_well_typed_correct; try eapply while_well_typed_correct'; eauto.
  - (* Raise *)
    split; try eapply well_typed_raise; try eapply well_typed_raise'; eauto.
  - (* TryCatch *)
    destruct IHHtype1. destruct IHHtype2.
    split; try eapply try_catch_throw_secure_stmt; try eapply try_catch_throw_secure_stmt'; eauto.
Qed.

Lemma well_typed_stmt_valid s pc : well_typed_stmt pc s -> valid_stmt s.
Proof.
  intros Htype. induction Htype; try tauto; constructor; eauto.
Qed.

Lemma secure_stmt_lower_pc:
  forall (pc2 : sensitivity) (s : stmt),
    secure_stmt pc2 s -> forall pc1 : L, leq pc1 pc2 -> secure_stmt pc1 s.
Proof.
  intros pc2 s H pc1 Hpc observer.
  specialize (H observer). inv H.
  - left. eapply leq_trans_lat; eauto. auto.
  - case_leq pc1 observer.
    + left; auto. cbn in H1. intros σ1 σ2 regs1 regs2 Hσ.
      eapply eqit_secure_RR_imp with (RR1 := product_rel (product_rel top2 (labelled_equiv Γ observer)) top2 ).
        { intros [? [] ] [? [] ] [? ?]. split; auto. }
      eapply state_secure_eutt_equiv_ret_aux; eauto.
      constructor. all : try cbv; tauto.
    + right; auto.
Qed.

Lemma secure_throw_stmt_lower_pc:
  forall (pc : sensitivity) (s : stmt),
    secure_throw_stmt pc s -> forall pc1 : L, leq pc1 pc -> secure_throw_stmt pc1 s.
Proof.
  intros pc s H pc1 Hpc observer.
  specialize (H observer). inv H.
  - left. eapply leq_trans_lat; eauto. auto.
  - case_leq pc1 observer.
    + left; auto. cbn in H1. intros σ1 σ2 Hσ.
      eapply state_secure_eutt_throw_ret_aux; eauto.
    + right; auto.
Qed.

End LabelledImpTypes.
