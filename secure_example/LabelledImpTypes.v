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
     LabelledImp
     LabelledImpHandler
     Lattice
     LabelledAsm
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Section LabelledImpTypes.
Context (Labels : Lattice).
Context (LabelLattice : LatticeLaws Labels).


Arguments interp_imp {Labels} {R}.
Arguments denote_expr {Labels}.
Notation label := (@T Labels).

Ltac case_leq l1 l2 := destruct (leq_dec Labels l1 l2) as [Hleq | Hnleq].

Definition labelled_equiv (Γ : privacy_map Labels) (l : label) (σ1 σ2 : map)  : Prop :=
  forall x, leq (Γ x) l -> σ1 x = σ2 x.

Definition top2 {A B} : A -> B -> Prop := fun _ _ => True.

Instance labelled_equit_equiv {Γ l} : Equivalence (labelled_equiv Γ l).
Proof.
  constructor; unfold labelled_equiv.
  - red. intros; auto.
  - red. intros. symmetry; auto.
  - red. intros. rewrite H; auto.
Qed.

Definition label_eqit_secure_impstate  (b1 b2 : bool) (Γ : privacy_map Labels) (l : label) {R1 R2 : Type} (RR : R1 -> R2 -> Prop )
           (m1 : stateT map (itree ((impExcE Labels) +' (IOE Labels))) R1)
           (m2 : stateT map (itree ((impExcE Labels) +' (IOE Labels))) R2) : Prop :=
  forall σ1 σ2, labelled_equiv Γ l σ1 σ2 -> eqit_secure _ (priv_exc_io Labels) (product_rel (labelled_equiv Γ l) RR) b1 b2 l (m1 σ1) (m2 σ2).

Definition label_state_sec_eutt {R1 R2} priv l (RR : R1 -> R2 -> Prop) m1 m2 :=
  label_eqit_secure_impstate true true  priv l RR m1 m2.

Definition sem_stmt (s : stmt Labels) := interp_imp (denote_stmt Labels s).

Definition sem_throw_stmt (s : stmt Labels) := interp_imp (throw_prefix (denote_stmt Labels s) ).

Definition sem_expr (e : expr) := interp_imp (denote_expr e).

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

Global Instance proper_state_equiv_label_state_sec_eutt {R1 R2 RR priv l} : Proper (@state_equiv _ R1 ==> @state_equiv _ R2 ==> iff) (@label_state_sec_eutt R1 R2 priv l RR).
Proof.
  repeat intro. split.
  - intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1). eapply proper_eutt_secure_eutt; eauto. symmetry. auto. symmetry. auto.
  - intros. intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1).  eapply proper_eutt_secure_eutt; eauto.
Qed.

Context (Γ : privacy_map Labels).

Variant secure_stmt_at_label (observer pc : label) (s : stmt Labels) : Prop :=
  | ssal_leq : (leq pc observer) -> label_state_sec_eutt Γ observer eq (sem_stmt s) (sem_stmt s) -> secure_stmt_at_label observer pc s
  | ssal_nleq : (~ leq pc observer) -> label_state_sec_eutt Γ observer top2 (sem_stmt s) (ret tt) -> secure_stmt_at_label observer pc s.


Variant secure_expr_at_label (observer protection: label ) (e : expr) : Prop :=
  | seal_leq : (leq protection observer) -> label_state_sec_eutt Γ observer eq (sem_expr e) (sem_expr e) ->
               secure_expr_at_label observer protection e
  | seal_nleq : (~leq protection observer) -> (exists n:value, label_state_sec_eutt Γ observer top2 (sem_expr e) (ret n)) ->
                secure_expr_at_label observer protection e
.

Definition secure_expr l e := forall observer, secure_expr_at_label observer l e.

Definition secure_stmt pc s := forall observer, secure_stmt_at_label observer pc s.

Variant is_inl {A B : Type} : A + B -> Prop :=
  | is_inl_ev (a : A) : is_inl (inl a).

Variant secure_throw_stmt_at_label (observer pc : label) (s : stmt Labels) : Prop :=
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
    assert ( t ≈ ITree.bind (Ret (σ2, n)) (fun st : map * nat => ITree.bind (Ret (fst st, n) ) (fun st : map * nat => Ret (fst st,n))  )  ) end.
    { repeat rewrite bind_ret_l. reflexivity. }
    eapply proper_eutt_secure_eutt; try apply H0; try reflexivity.
    eapply secure_eqit_bind; try apply IHe1; eauto. intros [? ?] [? ?] [? ?]. cbn in *.
    eapply secure_eqit_bind; try apply IHe2; eauto. intros [? ?] [? ?] [? ?]. cbn in *.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; auto.
  - repeat setoid_rewrite interp_state_bind.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
    assert ( t ≈ ITree.bind (Ret (σ2, n)) (fun st : map * nat => ITree.bind (Ret (fst st, n) ) (fun st : map * nat => Ret (fst st,n))  )  ) end.
    { repeat rewrite bind_ret_l. reflexivity. }
    eapply proper_eutt_secure_eutt; try apply H0; try reflexivity.
    eapply secure_eqit_bind; try apply IHe1; eauto. intros [? ?] [? ?] [? ?]. cbn in *.
    eapply secure_eqit_bind; try apply IHe2; eauto. intros [? ?] [? ?] [? ?]. cbn in *.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; auto.
   - repeat setoid_rewrite interp_state_bind.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
    assert ( t ≈ ITree.bind (Ret (σ2, n)) (fun st : map * nat => ITree.bind (Ret (fst st, n) ) (fun st : map * nat => Ret (fst st,n))  )  ) end.
    { repeat rewrite bind_ret_l. reflexivity. }
    eapply proper_eutt_secure_eutt; try apply H0; try reflexivity.
    eapply secure_eqit_bind; try apply IHe1; eauto. intros [? ?] [? ?] [? ?]. cbn in *.
    eapply secure_eqit_bind; try apply IHe2; eauto. intros [? ?] [? ?] [? ?]. cbn in *.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; auto.
Qed.

Lemma expr_only_ret e observer:  exists n : value, label_state_sec_eutt Γ observer top2 (sem_expr e) (ret n) .
Proof.
  exists 0. apply expr_only_ret_aux1.
Qed.

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
  forall R RR t1 t2 (observer : label) (r1 r2 : R),
    Equivalence RR ->
    RR r1 r2 ->
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io Labels) (product_rel (labelled_equiv Γ observer) RR) true
                    true observer (interp_imp t1 σ1) (Ret(σ2,r1))) ->
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io Labels) (product_rel (labelled_equiv Γ observer) RR) true
                    true observer (interp_imp t2 σ1) (Ret(σ2,r2))) ->
    forall σ1 σ2 : map,
      labelled_equiv Γ observer σ1 σ2 ->
      eqit_secure _ (priv_exc_io Labels) (product_rel (labelled_equiv Γ observer) RR) true
                  true observer (interp_state (handle_imp _) t1 σ1)
                  (interp_state (handle_imp _) t2 σ2).
Proof.
  intros R RR t1 t2 observer r1 r2 HRR Hr12 Hr1 Hr2 s1 s2 Hs12.
  set ((product_rel (labelled_equiv Γ observer) RR)) as Rst.
  apply eqit_secure_RR_imp with (RR1 := rcompose Rst Rst).
  { intros [? ?] [? ?] [? ?]. destruct r3. cbn in *. unfold Rst in *.
    split. 2 : cbv; auto. destruct REL1 as [REL1 _]. destruct REL2 as [REL2 _].
    cbn in *. etransitivity; eauto. destruct REL1. destruct REL2.  cbn in *. etransitivity; eauto. }
  eapply eqit_secure_trans; eauto. eapply eqit_secure_sym.
  apply eqit_secure_RR_imp with (RR1 := Rst).
  { intros. split. 2 : cbv; auto. unfold Rst in PR. destruct PR.
    symmetry. auto. destruct x0. destruct x1. unfold Rst in *. destruct PR. symmetry. auto. }
  assert (eqit_secure _ (priv_exc_io Labels) Rst true true observer (Ret (s2, r2) ) (Ret (s2,r1))).
  { apply secure_eqit_ret. unfold Rst in *. split; auto; cbv; auto. symmetry. auto. }
  apply eqit_secure_RR_imp with (RR1 := rcompose Rst Rst).
  { intros [? ?] [? ?] [? ?]. destruct r3. cbn in *. unfold Rst in *.
    split. 2 : cbv; auto. destruct REL1 as [REL1 _]. destruct REL2 as [REL2 _].
    cbn in *. etransitivity; eauto. destruct REL1. destruct REL2. etransitivity; eauto. }
  eapply eqit_secure_trans; try apply Hr2; eauto. reflexivity.
Qed.

Lemma state_secure_eutt_throw_ret_aux:
  forall t1 t2  (observer : label),
    label_state_sec_eutt Γ observer
                         (fun (sum : unit + label) (_ : unit) =>
                            is_inl sum) (interp_state (handle_imp _) (throw_prefix t1))
                         (ret tt) ->
    label_state_sec_eutt Γ observer
                         (fun (sum : unit + label) (_ : unit) =>
                            is_inl sum) (interp_state (handle_imp _) (throw_prefix t2))
                         (ret tt) ->
    forall σ3 σ4 : map,
      labelled_equiv Γ observer σ3 σ4 ->
      eqit_secure _ (priv_exc_io Labels)
                  (product_rel (labelled_equiv Γ observer)
                               (sum_rel eq
                                        (fun l1 l2 : label =>
                                           eqlat l1 bot /\ eqlat l2 bot))) true
                  true observer
                  (interp_state (handle_imp _)
                                (throw_prefix t1) σ3)
                  (interp_state (handle_imp _)
                                (throw_prefix t2) σ4).
Proof.
  intros t1 t2 observer Ht1 Ht2 σ3 σ4 Hσ.
  do 2 red in Ht1, Ht2. cbn in *. set (product_rel
             (labelled_equiv Γ observer)
             (fun (sum : unit + label)
                (_ : unit) => is_inl sum)) as Rst.
  set (product_rel (labelled_equiv Γ observer) (fun (sum1 sum2 : unit + label) => is_inl sum1 /\ is_inl sum2)  ) as Rst'.
  eapply eqit_secure_RR_imp with (RR1 := Rst').
  { unfold Rst'. intros [σ1 [ [] | l1] ] [σ2 [ [] | l2] ] [Hσ' [Hr1 Hr2] ]; inv Hr1; inv Hr2.
    split; auto. constructor. auto. }
  eapply eqit_secure_RR_imp with (RR1 := rcompose Rst (rcompose eq (fun x1 x2 => Rst x2 x1)) ).
  { unfold Rst. intros [σ1  r1 ] [σ2 r2 ] Hr. inv Hr. inv REL2. destruct REL1. destruct REL3.
    inv H0. inv H2. unfold Rst'. destruct r3. cbn in *. subst. split; try split; try (constructor; auto).
    cbn. symmetry in H1. etransitivity; eauto. }
  eapply eqit_secure_trans; try eapply Ht1; eauto. eapply eqit_secure_trans with (t2 := (Ret (σ4, tt) ) ).
  apply secure_eqit_ret. auto. apply eqit_secure_sym. eapply Ht2. reflexivity.
Qed.


Lemma state_secure_eutt_ret_aux:
  forall R t1 t2 (observer : label) (r1 r2 : R),
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io Labels) (product_rel (labelled_equiv Γ observer) (@top2 R R)) true
                    true observer (interp_imp t1 σ1) (Ret(σ2,r1))) ->
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure _ (priv_exc_io Labels) (product_rel (labelled_equiv Γ observer) (@top2 R R)) true
                    true observer (interp_imp t2 σ1) (Ret(σ2,r2))) ->
    forall σ1 σ2 : map,
      labelled_equiv Γ observer σ1 σ2 ->
      eqit_secure _ (priv_exc_io Labels) (product_rel (labelled_equiv Γ observer) top2) true
                  true observer (interp_state (handle_imp _) t1 σ1)
                  (interp_state (handle_imp _) t2 σ2).
Proof.
  intros R t1 t2 observer r1 r2 Hr1 Hr2 s1 s2 Hs12.
  eapply state_secure_eutt_equiv_ret_aux; eauto. 2: cbv; auto.
  constructor; constructor.
Qed.

Lemma update_labelled_equiv_invisible:
  forall (x : var) (observer : label) Γ,
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
  forall (x : var) (observer : label) Γ,
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
    cbn. apply secure_eqit_ret; split; auto. cbn. cbn in *; subst; apply update_labelled_equiv_visible; auto.
  - case_leq pc observer.
    + left; auto.
      destruct H0 as [n Hn]. unfold sem_stmt.
      cbn. unfold interp_imp. do 2 red. intros. setoid_rewrite interp_state_bind.
      do 2 red in Hn.
      eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [? ?] [? ?] [? ?]. cbn in H1. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn. apply secure_eqit_ret. split. 2 : cbv; auto. cbn.
      apply update_labelled_equiv_invisible; auto. symmetry.
      apply update_labelled_equiv_invisible;  auto.
      symmetry; auto.
    + right; auto.
      destruct H0 as [n Hn]. unfold sem_stmt. cbn.
      do 2 red in Hn. do 2 red. intros. unfold sem_stmt. cbn.
      setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [? ?] [? ?] [? ?]. cbn in H3.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn.
      apply secure_eqit_ret; split; auto.
      cbn. apply update_labelled_equiv_invisible; auto.
Qed.

Lemma throw_prefix_denote_expr e : throw_prefix (denote_expr e) ≈ (ITree.bind (denote_expr e) (fun v => Ret (inl v))).
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
  unfold sem_expr, interp_imp. cbn.
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
    cbn. setoid_rewrite throw_prefix_bind. unfold interp_imp. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) (fun sum1 sum2 => sum1 = sum2 /\ is_inl sum1) ).
    + intros [σ3 [v1 | l1] ] [σ4 [v2 | l2] ] [Hσ Hr]; inv Hr; try inv H3; try discriminate.
      cbn. setoid_rewrite throw_prefix_ev. setoid_rewrite interp_state_vis. cbn.
      repeat rewrite bind_ret_l. setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_tau. setoid_rewrite interp_state_ret.
      cbn. eapply proper_eutt_secure_eutt; repeat rewrite tau_eutt; try reflexivity. apply secure_eqit_ret.
      split; cbn; auto. injection H2; intros; subst. apply update_labelled_equiv_visible; auto.
    + eapply proper_eutt_secure_eutt; try rewrite throw_prefix_denote_expr; try reflexivity.
      setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind; eauto. intros [σ3 v1] [σ4 v2] [Hσ Hr]. cbn in Hr; subst. setoid_rewrite interp_state_ret. apply secure_eqit_ret.
      split; auto. cbn. split; auto. constructor.
  - case_leq pc observer.
    + left; auto.
      destruct H0 as [n Hn]. unfold sem_throw_stmt.
      cbn. unfold interp_imp. do 2 red. intros. setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
      setoid_rewrite interp_state_bind. repeat rewrite bind_bind.
      assert (label_state_sec_eutt Γ observer top2
         (sem_expr e) (sem_expr e)).
      { do 2 red. intros. eapply state_secure_eutt_ret_aux; eauto; apply Hn. }
      eapply secure_eqit_bind; try apply H1; auto. intros [σ3 v1] [σ4 v2] [Hσ Hv].
      setoid_rewrite interp_state_ret. cbn. setoid_rewrite bind_ret_l. cbn. setoid_rewrite throw_prefix_ev.
      setoid_rewrite interp_state_vis. cbn. setoid_rewrite bind_ret_l. setoid_rewrite interp_state_tau.
      eapply proper_eutt_secure_eutt; repeat rewrite tau_eutt; try reflexivity.
      setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret. cbn. apply secure_eqit_ret.
      split; cbn; try constructor; auto.
      apply update_labelled_equiv_invisible; auto. symmetry.
      apply update_labelled_equiv_invisible;  auto. symmetry. auto.
    + right; auto.
      destruct H0 as [n Hn]. unfold sem_throw_stmt. cbn.
      assert (label_state_sec_eutt Γ observer top2
         (sem_expr e) (sem_expr e)).
      { do 2 red. intros. eapply state_secure_eutt_ret_aux; eauto; apply Hn. }
      do 2 red. intros.
      setoid_rewrite throw_prefix_bind. unfold interp_imp. setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
      specialize (expr_only_ret' e σ1) as [n' Hn'].
      setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite Hn'; try reflexivity. rewrite bind_bind.
      rewrite bind_ret_l. setoid_rewrite interp_state_ret. rewrite bind_ret_l. cbn.
      setoid_rewrite throw_prefix_ev. setoid_rewrite interp_state_vis. cbn. rewrite bind_ret_l.
      rewrite interp_state_tau. eapply proper_eutt_secure_eutt; repeat rewrite tau_eutt; try reflexivity.
      setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret. cbn. apply secure_eqit_ret.
      split; try constructor; auto. cbn. apply update_labelled_equiv_invisible; auto.
Qed.



Lemma assign_only_ret e x σ : exists σ', sem_stmt (Assign x e) σ ≈ Ret (σ', tt).
Proof.
  unfold sem_stmt, interp_imp. cbn.
  setoid_rewrite interp_state_bind. specialize (expr_only_ret' e σ) as He.
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
    unfold interp_imp. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? ?] [? ?] [? ?].
    cbn in H2, H3. subst. cbn. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
    cbn. setoid_rewrite bind_trigger. cbn.
    apply eqit_secure_public_Vis; try apply H.
    intros []. apply secure_eqit_ret; auto. split; auto.
  - case_leq pc observer.
    + left; auto. destruct H0 as [n Hn]. do 2 red in Hn. cbn in Hn.
      unfold sem_stmt. cbn. unfold interp_imp. do 2 red.
      intros. setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [? ?] [? ?] [? ?]. cbn in H1. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn. setoid_rewrite bind_trigger. apply eqit_secure_private_VisLR; auto.
      constructor; apply tt. constructor; apply tt. intros [] [].
      apply secure_eqit_ret. split; auto.
    + right; auto. destruct H0 as [n Hn]. do 2 red in Hn.
      do 2 red. intros. unfold sem_stmt. cbn.
      unfold interp_imp. setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [? ?] [? ?] [? ?]. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn. setoid_rewrite bind_trigger. cbn.
      apply eqit_secure_private_VisL; auto. constructor; apply tt.
      intros []. apply secure_eqit_ret; auto. split; auto.
Qed.

Lemma throw_prefix_output l1 e :  throw_prefix (denote_stmt Labels (Output l1 e) ) ≈
        v <- denote_expr e;; trigger (LabelledPrint Labels l1 v);; Ret (inl tt).
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
    eapply proper_eutt_secure_eutt; try rewrite throw_prefix_output; try reflexivity. unfold interp_imp.
    setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto.
    intros [? ?] [? ?] [? ?].
    cbn in H2, H3. subst. cbn. eapply proper_eutt_secure_eutt; try rewrite interp_state_bind, interp_state_trigger; try reflexivity.
    cbn. setoid_rewrite bind_trigger. setoid_rewrite bind_vis.
    apply eqit_secure_public_Vis; try apply H.
    intros []. setoid_rewrite bind_ret_l. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    cbn. split; auto. constructor. auto.
  - case_leq pc observer.
    + left; auto. destruct H0 as [n Hn]. do 2 red in Hn. cbn in Hn.
      unfold sem_throw_stmt. do 2 red. intros.
      eapply proper_eutt_secure_eutt; try rewrite throw_prefix_output; try reflexivity.
      cbn. unfold interp_imp.
      setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [? ?] [? ?] [? ?]. cbn in H2.
      setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try setoid_rewrite interp_state_trigger; try reflexivity. cbn.
      setoid_rewrite bind_bind. setoid_rewrite bind_trigger. apply eqit_secure_private_VisLR; auto.
      all : try (constructor; apply tt; fail). intros [] []. setoid_rewrite bind_ret_l.
      setoid_rewrite interp_state_ret. apply secure_eqit_ret. split; try constructor; auto.
    + right; auto. destruct H0 as [n Hn]. do 2 red in Hn.
      do 2 red. intros. unfold sem_throw_stmt.
      eapply proper_eutt_secure_eutt; try rewrite throw_prefix_output; try reflexivity.
      unfold interp_imp.
      setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [? ?] [? ?] [? ?]. cbn. setoid_rewrite interp_state_bind.
      eapply proper_eutt_secure_eutt; try rewrite interp_state_trigger; try reflexivity. cbn.
      rewrite bind_bind, bind_trigger. apply eqit_secure_private_VisL; auto. constructor; constructor.
      intros []. rewrite bind_ret_l. rewrite interp_state_ret.
      apply secure_eqit_ret; auto. split; auto. constructor.
Qed.

Lemma seq_well_typed_correct pc s1 s2 :
  secure_stmt pc s1 -> secure_stmt pc s2 ->
  secure_stmt pc (Seq s1 s2).
Proof.
  intros Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  inv Hc1obs.
  - do 2 red in H0. left; auto. unfold sem_stmt.
    cbn. unfold interp_imp. do 2 red. intros. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? [] ] [? [] ] [? ?].
    clear H3. cbn in H2. cbn.
    inv Hc2obs; try apply H4; auto.
    do 2 red in H4.
    eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
    { intros [ ? [] ] [? [] ] [? ?] . split; auto. }
    eapply state_secure_eutt_ret_aux; try apply H4; eauto.
    (* I think this ends up being fine*)
  - right; auto. unfold sem_stmt, interp_imp. cbn. do 2 red. intros.
    setoid_rewrite interp_state_bind.
    inv Hc2obs.
    { exfalso. apply H. auto. }
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
    rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
    eapply secure_eqit_bind; try eapply H0; auto.
    intros [? ?] [? ?] [? ?]. apply H3; auto.
Qed.

Lemma seq_well_typed_correct' pc s1 s2 :
  secure_throw_stmt pc s1 -> secure_throw_stmt pc s2 ->
  secure_throw_stmt pc (Seq s1 s2).
Proof.
  intros Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  inv Hc1obs.
  - do 2 red in H0. left; auto. unfold sem_throw_stmt.
    cbn. unfold interp_imp. do 2 red. intros. setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto.
    intros [σ3 [ [] | ?] ] [σ4 [ [] | ?]] [Hσ Hr] ; inv Hr.
    + cbn. inv Hc2obs; try contradiction. eapply H3; eauto.
    + destruct H4; subst; cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret. split; try constructor; auto.
  - right; auto. unfold sem_throw_stmt, interp_imp. cbn. do 2 red. intros.
    setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    inv Hc2obs; try contradiction.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
    rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
    eapply secure_eqit_bind; try eapply H0; auto.
    intros [σ3 [ [] | ?] ] [σ4 [] ] [Hσ Hr] ; inv Hr.
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
    unfold sem_stmt, interp_imp.
    cbn. do 2 red. intros. setoid_rewrite interp_state_bind. eapply secure_eqit_bind; try apply H4; auto.
    intros [? ?] [? ?] [? ?]. cbn in H6, H7. subst. cbn. destruct v0; eauto.
  - case_leq pc observer.
    + left; auto. unfold sem_stmt, interp_imp. cbn. do 2 red. intros.
      setoid_rewrite interp_state_bind.
      inv He; try contradiction.
      * eapply secure_eqit_bind; try apply H5; eauto.
        intros [? ?] [? ?] [? ?]. cbn in H7, H6. cbn. subst. do 2 red in H0, H2.
        eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
        { intros [? [] ] [? [] ] [? ?]. split; auto. }
        destruct v0; try eapply  state_secure_eutt_ret_aux; cbn in *; eauto.
      * destruct H5 as [n Hn]. do 2 red in Hn.
        eapply secure_eqit_bind; try eapply  state_secure_eutt_ret_aux; cbn in Hn; eauto.
        intros [? ?] [? ?] [? ?]. cbn. cbn in H6.
        eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
        { intros [? [] ] [? [] ] [? ?]. split; auto. }
        destruct v; destruct v0;
        try eapply state_secure_eutt_ret_aux; try apply H0; try apply H2; eauto.
     + right; auto. do 2 red. intros. unfold sem_stmt, interp_imp. cbn.
       setoid_rewrite interp_state_bind.
       match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, 0)) (fun st => Ret (fst st, tt) ))) end.
       rewrite bind_ret_l. reflexivity.
       eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
       inv He.
       * eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2) .
         2 : { apply expr_only_ret_aux1; auto. }
         intros [? ?] [? ?] [? ?]. cbn. destruct v; cbn in *; eauto.
       * destruct H6. eapply secure_eqit_bind; try apply expr_only_ret_aux1; auto.

         intros [? ?] [? ?] [? ?]. cbn. destruct v; cbn in *; eauto.
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
    unfold sem_throw_stmt, interp_imp.
    cbn. do 2 red. intros. setoid_rewrite throw_prefix_bind.
    eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
    rewrite bind_bind. setoid_rewrite interp_state_bind; setoid_rewrite bind_ret_l.
    eapply secure_eqit_bind; try apply H4; auto.
    intros [? ?] [? ?] [? ?]. cbn in H6, H7. subst. cbn. destruct v0; eauto.
  - (* ~ leq (join pc le) observer  *)
    case_leq pc observer.
    + (* leq pc observer *)
      left; auto. unfold sem_throw_stmt, interp_imp. cbn. do 2 red. intros.
      setoid_rewrite throw_prefix_bind.
      setoid_rewrite interp_state_bind.
      inv He; try contradiction.
      * (* leq le observer *)
        eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
        setoid_rewrite interp_state_bind. repeat rewrite bind_bind.
        eapply secure_eqit_bind; try eapply H6; eauto.
        setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l; cbn.
        intros [σ3 v1 ] [σ4 v2 ] [Hσ Hv]; cbn in Hv; subst. destruct v2; cbn; eauto;
        try eapply state_secure_eutt_throw_ret_aux; eauto.
      * eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
        setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
        destruct H5 as [n Hn].
        eapply secure_eqit_bind; try eapply state_secure_eutt_ret_aux; try eapply Hn; eauto.
        intros [σ3 v1] [σ4 v2] [Hσ _ ]. setoid_rewrite interp_state_ret. cbn.
        setoid_rewrite bind_ret_l. cbn. destruct v1; destruct v2; try eapply state_secure_eutt_throw_ret_aux; eauto.
   + (* ~ leq pc observer *)
     right; auto. unfold sem_throw_stmt, interp_imp. cbn. do 2 red. intros. setoid_rewrite throw_prefix_bind.
     setoid_rewrite interp_state_bind.
     match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, 0)) (fun st => Ret (fst st, tt) ))) end.
     rewrite bind_ret_l. reflexivity.
     eapply proper_eutt_secure_eutt; try apply H5; try reflexivity.
     inv He.
     * eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
       eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
       setoid_rewrite interp_state_bind. rewrite bind_bind.
       eapply secure_eqit_bind; try eapply expr_only_ret_aux1; eauto.
       intros [σ3 v1] [σ4 v2] [Hσ _ ]. setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
       cbn. destruct v1; cbn in *; eauto.
     * destruct H6 as [n Hn]. eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_denote_expr; try apply H4; try reflexivity.
       setoid_rewrite interp_state_bind. rewrite bind_bind.
       eapply secure_eqit_bind; try eapply expr_only_ret_aux1; eauto.
       setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
       intros [σ3 v1] [σ4 v2] [Hσ _ ]. destruct v1; cbn in *; eauto.
Qed.

Lemma while_well_typed_correct e s :
  secure_expr bot e -> secure_stmt bot s ->
  secure_stmt bot (While e s).
Proof.
  intros He Hc. red. intros.
  assert (leq bot observer).
  { cbn. destruct LabelLattice.
    setoid_rewrite <- join_comm. rewrite <- join_unit. reflexivity. }
  specialize (He observer).
  specialize (Hc observer).
  inv He; inv Hc; try contradiction.
  left; auto. unfold sem_stmt, interp_imp. cbn. unfold while.
  specialize @interp_state_iter' as Hisi. red in Hisi. do 2 red. intros.
  setoid_rewrite Hisi. eapply secure_eqit_iter with (RA := product_rel (labelled_equiv Γ observer) eq).
  { split; auto. }
  intros [? [] ] [? [] ] [? ?]. cbn.
  setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
  eapply secure_eqit_bind; try apply H1; auto.
  intros [? ?] [? ?] [? ?]. cbn. cbn in H7, H8; subst. destruct v0.
  - setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    apply secure_eqit_ret. constructor. split; auto.
  - setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
    eapply secure_eqit_bind; try apply H3; auto.
    intros [? [] ] [? [] ] [? ?]. cbn. cbn in H8.
    setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    apply secure_eqit_ret. constructor. split; auto.
Qed.

Lemma while_well_typed_correct' e s :
  secure_expr bot e -> secure_throw_stmt bot s ->
  secure_throw_stmt bot (While e s).
Proof.
  intros He Hc. red. intros.
  assert (leq bot observer).
  { cbn. destruct LabelLattice.
    setoid_rewrite <- join_comm. rewrite <- join_unit. reflexivity. }
  specialize (He observer).
  specialize (Hc observer).
  inv He; inv Hc; try contradiction.
  left; auto. unfold sem_throw_stmt in *.
  cbn. do 2 red. intros. setoid_rewrite throw_prefix_iter.
  unfold interp_imp in *.
  specialize @interp_state_iter' as Hisi. red in Hisi.
  setoid_rewrite Hisi. cbn.
  eapply secure_eqit_iter with (RA := product_rel (labelled_equiv Γ observer) eq ).
  split; auto. intros [σ3 [] ] [σ4 [] ] [Hσ _]. cbn.
  setoid_rewrite throw_prefix_bind. repeat setoid_rewrite interp_state_bind.
  repeat rewrite bind_bind.
  eapply proper_eutt_secure_eutt;
    try setoid_rewrite throw_prefix_denote_expr; try reflexivity.
  setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
  eapply secure_eqit_bind; try eapply H1; eauto.
  intros [σ5 v1] [σ6 v2] [Hσ' Heq]; cbn in Heq; subst. cbn.
  setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
  destruct v2.
  - cbn. setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret.
    setoid_rewrite bind_ret_l. cbn. setoid_rewrite interp_state_ret.
    setoid_rewrite bind_ret_l. cbn. apply secure_eqit_ret. constructor. split; auto.
    constructor. auto.
  - setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    setoid_rewrite bind_bind. eapply secure_eqit_bind; try eapply H3; eauto.
    intros [σ7 [ [] | l1] ] [σ8 [ [] | l2] ] [Hσ'' Hsum]; inv Hsum.
    + cbn. setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret.
      setoid_rewrite bind_ret_l. cbn. setoid_rewrite interp_state_ret.
      setoid_rewrite bind_ret_l. cbn. apply secure_eqit_ret.
      constructor. split; auto.
    + cbn. setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
      cbn. setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
      cbn. apply secure_eqit_ret. destruct H7; subst. constructor.
      split; auto. constructor. auto.
Qed.

Lemma well_typed_raise : secure_stmt bot (Raise bot).
Proof.
  red. intros. left.
  destruct LabelLattice. cbn.
  setoid_rewrite <- join_comm. rewrite <- join_unit. reflexivity.
  red. red. intros. unfold sem_stmt, interp_imp.
  cbn. setoid_rewrite interp_state_bind. eapply secure_eqit_bind with (RR := eq).
  intros [ _ [] ].
  eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
  cbn. setoid_rewrite bind_trigger. apply eqit_secure_public_Vis.
  cbn. destruct LabelLattice.
  setoid_rewrite <- join_comm. rewrite <- join_unit. reflexivity. intros [].
Qed.

Lemma well_typed_raise' : secure_throw_stmt bot (Raise bot).
Proof.
  red. intros. left. apply leq_bot; auto.
  red. red. intros. unfold sem_throw_stmt, interp_imp. cbn.
  setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
  eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer)  (fun r1 r2 => r1 = inr bot /\ r2 = inr bot) ).
  - intros [σ3 [ [] | l1 ] ] [σ4 [ [] | l2 ] ] Heq; subst. cbn. destruct Heq. cbn in *. subst.
    destruct H1. injection H1; injection H2; intros; subst.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret.
    split; auto. constructor. split; destruct LabelLattice; reflexivity.
  - setoid_rewrite throw_prefix_exc. setoid_rewrite interp_state_ret. apply secure_eqit_ret.
    split; auto.
Qed.


Lemma try_catch_public_exc R RR (t1 t2 catch1 catch2 : itree _ R ) observer :
  label_state_sec_eutt Γ observer (sum_rel RR (fun l1 l2 => eqlat l1 bot /\ eqlat l2 bot) )
                       (interp_imp (throw_prefix t1) ) (interp_imp (throw_prefix t2) )  ->
  label_state_sec_eutt Γ observer RR (interp_imp t1) (interp_imp t2) ->
  label_state_sec_eutt Γ observer RR (interp_imp catch1) (interp_imp catch2) ->
  label_state_sec_eutt Γ observer RR
              (interp_imp (try_catch t1 (fun _ => catch1))) (interp_imp (try_catch t2 (fun _ => catch2))).
Proof.
  unfold interp_imp. intros Hthrow Hsect Hsecc σ1 σ2 Hσ.
  (* try_catch_to_throw_prefix *)
  eapply proper_eutt_secure_eutt; try setoid_rewrite try_catch_to_throw_prefix;
    try setoid_rewrite interp_state_bind; try reflexivity.
  eapply secure_eqit_bind; eauto.
  intros [σ3 [r1 | l1] ] [σ4 [r2 | l2] ] Htry; destruct Htry as [ Hσ34 Hsum];
    inv Hsum.
  - cbn. repeat rewrite interp_state_ret. apply secure_eqit_ret.
    split; auto.
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
    do 2 red. intros. apply H0 in H5 as H6. cbn in H6. unfold interp_imp.
    eapply proper_eutt_secure_eutt; try setoid_rewrite try_catch_to_throw_prefix; try reflexivity.
    setoid_rewrite <- bind_ret_r at 6.
    setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto.
    intros [σ3 [ [] | l] ] [σ4 []] [Hσ Hsum]; inv Hsum. cbn.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; cbv; auto.
Qed.

Lemma try_catch_throw_secure_stmt' pc s catch :
  secure_stmt pc s -> secure_throw_stmt pc s -> secure_throw_stmt pc catch ->
  secure_throw_stmt pc (TryCatch s catch).
Proof.
  intros Hs1 Hs2 Hcatch observer.
  specialize (Hs1 observer). specialize (Hs2 observer). specialize (Hcatch observer).
  inv Hs1; inv Hs2; inv Hcatch; try contradiction.
  - left; auto. unfold sem_throw_stmt in *. cbn.
    do 2 red. intros.
    eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_of_try_catch;
       try setoid_rewrite try_catch_to_throw_prefix; try reflexivity.
    unfold interp_imp in *. setoid_rewrite interp_state_bind.
    setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    setoid_rewrite bind_bind. clear H0.
    eapply secure_eqit_bind; try eapply H2; eauto.
    try reflexivity.
    intros [σ3 [ [] | l1] ] [σ4 [ [] | l2] ] [Hσ Hsum]; inv Hsum; cbn.
    + setoid_rewrite throw_prefix_ret. setoid_rewrite interp_state_ret.
      setoid_rewrite bind_ret_l. cbn. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. split; auto. constructor. auto.
    + setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
      destruct H7; subst. cbn. eauto.
  - right; auto. unfold sem_throw_stmt in *. cbn.
    do 2 red. intros.
    eapply proper_eutt_secure_eutt; try setoid_rewrite throw_prefix_of_try_catch;
       try setoid_rewrite try_catch_to_throw_prefix; try reflexivity.
    setoid_rewrite throw_prefix_bind. rewrite bind_bind.
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
     rewrite bind_ret_l. reflexivity.
     eapply proper_eutt_secure_eutt; try rewrite H6; try reflexivity.
     unfold interp_imp. setoid_rewrite interp_state_bind.
     eapply secure_eqit_bind; try eapply H2; eauto.
     intros [σ3 [[] | l] ] [σ4 [] ] [Hσ Hsum]; inv Hsum.
     cbn. rewrite throw_prefix_ret, bind_ret_l. rewrite interp_state_ret.
     apply secure_eqit_ret. split; auto. constructor; auto.
Qed.

Lemma well_typed_skip pc : secure_stmt pc Skip.
Proof.
  intro observer. case_leq pc observer.
  - left; auto. unfold sem_stmt, interp_imp. do 2 red. intros.
    cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    split; auto.
  - right; auto. unfold sem_stmt, interp_imp. do 2 red. intros.
    cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    split; auto. cbv. auto.
Qed.

Lemma well_typed_skip' pc : secure_throw_stmt pc Skip.
Proof.
  intro observer. case_leq pc observer.
  - left; auto. unfold sem_throw_stmt, interp_imp. do 2 red. intros.
    cbn. setoid_rewrite throw_prefix_ret.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    split; auto. constructor. auto.
  - right; auto. unfold sem_throw_stmt, interp_imp. do 2 red. intros.
    cbn. setoid_rewrite throw_prefix_ret.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    split; auto. constructor.
Qed.

Inductive well_typed_expr : label -> expr -> Prop :=
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
Inductive well_typed_stmt : label -> stmt Labels -> Prop :=
  | wts_manual pc s : secure_stmt pc s /\ secure_throw_stmt pc s -> well_typed_stmt pc s
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
  - intros. constructor. destruct LabelLattice. rewrite Hl. auto.
  - intros. destruct LabelLattice. rewrite <- H in Hl.
    econstructor; eauto. rewrite Hl. reflexivity.
  - intros. destruct LabelLattice.
    econstructor; eauto. rewrite Hl. auto.
  - intros. destruct LabelLattice. rewrite <- H in Hl.
    econstructor; eauto. rewrite Hl. reflexivity.
Qed.

Instance proper_eqlat_expr' : Proper (eqlat ==> eq ==> Basics.impl) well_typed_expr.
Proof.
  intros l1 l2 Hl e1 e2 He. subst. intro Htype.
  generalize dependent l2. induction Htype.
  - intros. constructor.
  - intros. constructor. destruct LabelLattice. rewrite <- Hl. auto.
  - intros. destruct LabelLattice. rewrite Hl in H.
    econstructor; eauto.
  - intros. destruct LabelLattice. rewrite Hl in H.
    econstructor; eauto.
  - intros. destruct LabelLattice. rewrite Hl in H.
    econstructor; eauto.
Qed.

Lemma well_typed_expr_upward_close l1 l2 e : leq l1 l2 -> well_typed_expr l1 e -> well_typed_expr l2 e.
Proof.
  revert l1 l2.
  induction e; intros; try inv H0.
  - constructor. eapply leq_trans_lat; eauto.
  - constructor.
  - cbn in H. setoid_rewrite <- H. destruct LabelLattice.
    econstructor; try reflexivity; eauto. eapply IHe1; eauto.
    apply leq_trans_lat with (l2 := join l0 l3); auto.
    apply leq_join_l; auto. rewrite H6. cbn. apply join_idempot; auto.
    eapply IHe2; eauto.
    apply leq_trans_lat with (l2 := join l0 l3); auto.
    apply leq_join_r; auto. rewrite H6. auto.
  - cbn in H. setoid_rewrite <- H. destruct LabelLattice.
    econstructor; try reflexivity; eauto. eapply IHe1; eauto.
    apply leq_trans_lat with (l2 := join l0 l3); auto.
    apply leq_join_l; auto. rewrite H6. cbn. apply join_idempot; auto.
    eapply IHe2; eauto.
    apply leq_trans_lat with (l2 := join l0 l3); auto.
    apply leq_join_r; auto. rewrite H6. auto.
  - cbn in H. setoid_rewrite <- H. destruct LabelLattice.
    econstructor; try reflexivity; eauto. eapply IHe1; eauto.
    apply leq_trans_lat with (l2 := join l0 l3); auto.
    apply leq_join_l; auto. rewrite H6. cbn. apply join_idempot; auto.
    eapply IHe2; eauto.
    apply leq_trans_lat with (l2 := join l0 l3); auto.
    apply leq_join_r; auto. rewrite H6. auto.
Qed.

Lemma well_typed_expr_correct l e : well_typed_expr l e -> secure_expr l e.
Proof.
  revert l. red. induction e; intros l Htype observer.
  - inv Htype. case_leq l observer.
    + left; auto. unfold sem_expr. cbn. unfold interp_imp.
      do 2 red. intros. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn.
      unfold get. apply secure_eqit_ret; split; auto. cbn.
      red in H. apply H. eapply leq_trans_lat; eauto.
    + right; auto. apply expr_only_ret.
  - case_leq l observer.
    + left; auto. unfold sem_expr. cbn. unfold interp_imp. do 2 red.
      intros. setoid_rewrite interp_state_ret. apply secure_eqit_ret.
      split; auto.
    + right; auto. exists 0. unfold sem_expr. cbn. unfold interp_imp. do 2 red.
      intros. setoid_rewrite interp_state_ret. apply secure_eqit_ret. split; auto.
      cbv. auto.
  - inv Htype.
    assert (well_typed_expr l e1 ). eapply well_typed_expr_upward_close; eauto.
    eapply leq_trans_lat with (l2 := join l1 l2); auto. apply leq_join_l; auto.
    cbn. destruct LabelLattice. rewrite H4. apply join_idempot; auto.
    assert (well_typed_expr l e2 ). eapply well_typed_expr_upward_close; eauto.
    apply leq_trans_lat with (l2 := join l1 l2); auto. apply leq_join_r; auto.
    cbn. destruct LabelLattice. rewrite H4. apply join_idempot; auto.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [s3 r1] [s4 r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H6; eauto.
      intros [? ?] [? ?] [? ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. split; auto.
    + right; auto. apply expr_only_ret.
  - inv Htype.
    assert (well_typed_expr l e1 ). eapply well_typed_expr_upward_close; eauto.
    eapply leq_trans_lat with (l2 := join l1 l2); auto. apply leq_join_l; auto.
    cbn. destruct LabelLattice. rewrite H4. apply join_idempot; auto.
    assert (well_typed_expr l e2 ). eapply well_typed_expr_upward_close; eauto.
    apply leq_trans_lat with (l2 := join l1 l2); auto. apply leq_join_r; auto.
    cbn. destruct LabelLattice. rewrite H4. apply join_idempot; auto.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [s3 r1] [s4 r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H6; eauto.
      intros [? ?] [? ?] [? ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. split; auto.
    + right; auto. apply expr_only_ret.
  - inv Htype.
    assert (well_typed_expr l e1 ). eapply well_typed_expr_upward_close; eauto.
    eapply leq_trans_lat with (l2 := join l1 l2); auto. apply leq_join_l; auto.
    cbn. destruct LabelLattice. rewrite H4. apply join_idempot; auto.
    assert (well_typed_expr l e2 ). eapply well_typed_expr_upward_close; eauto.
    apply leq_trans_lat with (l2 := join l1 l2); auto. apply leq_join_r; auto.
    cbn. destruct LabelLattice. rewrite H4. apply join_idempot; auto.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [s3 r1] [s4 r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H6; eauto.
      intros [? ?] [? ?] [? ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. split; auto.
    + right; auto. apply expr_only_ret.
Qed.

Lemma well_typed_stmt_sound s pc : well_typed_stmt s pc -> secure_stmt s pc.
Proof.
  intros Htype. enough (secure_stmt s pc /\ secure_throw_stmt s pc); try tauto.
  induction Htype; eauto.
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

Lemma secure_stmt_lower_pc:
  forall (pc2 : label) (s : stmt Labels),
    secure_stmt pc2 s -> forall pc1 : L, leq pc1 pc2 -> secure_stmt pc1 s.
Proof.
  intros pc2 s H pc1 Hpc observer.
  specialize (H observer). inv H.
  - left. eapply leq_trans_lat; eauto. auto.
  - case_leq pc1 observer.
    + left; auto. cbn in H1. intros σ1 σ2 Hσ.
      eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
        { intros [? [] ] [? [] ] [? ?]. split; auto. }
      eapply state_secure_eutt_equiv_ret_aux; eauto.
      constructor. all : try cbv; tauto.
    + right; auto.
Qed.

Lemma secure_throw_stmt_lower_pc:
  forall (pc : label) (s : stmt Labels),
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
(* would need to slightly refactor well_typed_stmt to be true will this formulation
Lemma lower_pc_sound s pc1 pc2 :
  leq pc1 pc2 -> well_typed_stmt pc2 s -> well_typed_stmt pc1 s.
Proof.
  intros Hpc Hs. generalize dependent pc1. induction Hs; intros.
  - constructor. destruct H. split. eapply secure_stmt_lower_pc; eauto.
    eapply secure_throw_stmt_lower_pc; eauto.
  - apply wts_skip.
  - apply wts_seq; eauto.
  - eapply wts_assign; eauto. eapply leq_trans_lat; eauto.
    destruct l; destruct pc; destruct pc1; cbv; auto; contradiction.
  - eapply wts_print; eauto. eapply leq_trans_lat; eauto.
    destruct le; destruct pc; destruct pc1; cbv; auto; contradiction.
  - eapply wts_if; eauto. eapply IHHs1. 2: eapply IHHs2.
    all :  destruct le; destruct pc; destruct pc1; cbv; auto; contradiction.
  - destruct pc1; try contradiction. eapply wts_while; eauto.
  - apply wts_raise. eapply leq_trans_lat; eauto.
  - apply wts_try; eauto.
Qed.
*)

End LabelledImpTypes.


(*
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.

Section Examples.

  Context (X : var).

  Definition sdec_body :=
    (If (Var X)
                 (Assign X (Minus (Var X) (Lit 1) ) )
                 (Raise Private)
             ).

  Definition sdec : stmt :=
   TryCatch
     ( While (Lit 1) sdec_body)
     Skip.

  Definition sdec_opt : stmt :=
    Assign X (Lit 0).

  Lemma sdec_body_eq σ : (sem_stmt sdec_body σ ≈ if (Nat.eqb (σ X) 0)
                                               then v <- trigger (inl1 (Throw sensitivity Private));; match (v : void) with end
                                               else Ret (update X (σ X - 1) σ, tt))%itree.
  Proof.
    unfold sem_stmt, interp_imp. cbn. setoid_rewrite interp_state_bind.
    setoid_rewrite interp_state_trigger. cbn. rewrite bind_ret_l. cbn. unfold get.
    destruct (σ X) eqn : Heq.
    - rewrite <- EqNat.beq_nat_refl. cbn. rewrite interp_state_bind. cbn.
      setoid_rewrite interp_state_trigger. cbn. repeat rewrite bind_bind. repeat rewrite bind_trigger. cbn.
      apply eqit_Vis. intros [].
    - specialize (Nat.eqb_neq) as Hn. assert (S v <> 0). intro. discriminate.
      apply Hn in H. rewrite H. setoid_rewrite bind_trigger. rewrite bind_vis. rewrite interp_state_vis.
      cbn. repeat rewrite bind_ret_l. cbn. rewrite interp_state_trigger.
      tau_steps. setoid_rewrite Heq. cbn. reflexivity.
  Qed.

  Lemma throw_sdec_body_eq σ : (sem_throw_stmt sdec_body σ ≈ if (Nat.eqb (σ X) 0)
                                               then Ret (σ, inr Private)
                                               else Ret (update X (σ X - 1) σ, inl tt))%itree.
  Proof.
    unfold sem_throw_stmt, interp_imp. cbn. setoid_rewrite bind_trigger.
    setoid_rewrite throw_prefix_ev. setoid_rewrite interp_state_vis. cbn.
    rewrite bind_ret_l. repeat setoid_rewrite tau_eutt. cbn.
    unfold get. destruct (σ X) eqn : Heq.
    - cbn. rewrite throw_prefix_bind. setoid_rewrite throw_prefix_exc. rewrite bind_ret_l.
      setoid_rewrite interp_state_ret. reflexivity.
    - specialize (Nat.eqb_neq) as Hn. assert (S v <> 0). intro. discriminate.
      apply Hn in H. rewrite H. repeat setoid_rewrite bind_trigger. rewrite throw_prefix_bind.
      rewrite interp_state_bind. setoid_rewrite throw_prefix_ev. rewrite interp_state_vis.
      repeat rewrite bind_bind. cbn. rewrite bind_ret_l. tau_steps.
      setoid_rewrite Heq. reflexivity.
  Qed.


  Lemma while_sdec_body_eq σ0 : sem_stmt (While (Lit 1) sdec_body ) σ0 ≈
                                        ITree.iter (fun '(σ, u) =>
                                                      if (Nat.eqb (σ X) 0)
                                                      then v <- trigger (inl1 (Throw sensitivity Private));;
                                                           match (v : void) with end
                                                      else Ret (inl (update X (σ X - 1) σ, tt)))
                                        (σ0, tt).
  Proof.
    unfold sem_stmt, interp_imp. unfold denote_stmt. fold denote_stmt. unfold while.
    specialize @interp_state_iter' as Hisi. red in Hisi.
    setoid_rewrite Hisi.
    eapply eutt_iter' with (RI := product_rel eq eq); try (split; auto; fail).
    intros [σ1 [] ] [σ2 [] ] [ Hσ _ ]. cbn in Hσ. rewrite Hσ.
    remember sdec_body as s. cbn.
    setoid_rewrite interp_state_bind. setoid_rewrite interp_state_ret.
    rewrite bind_bind. repeat rewrite bind_ret_l. cbn.
    setoid_rewrite interp_state_bind. rewrite bind_bind.
    rewrite Heqs. setoid_rewrite sdec_body_eq.
    destruct (σ2 X =? 0)%nat.
    - setoid_rewrite bind_bind. setoid_rewrite bind_trigger.
      apply eqit_Vis. intros [].
    - setoid_rewrite interp_state_ret. repeat rewrite bind_ret_l. cbn.
      apply eqit_Ret. constructor. split; auto.
   Qed.

  Lemma while_sdec_body_eq' σ0 : sem_throw_stmt (While (Lit 1) sdec_body ) σ0 ≈
                                         ITree.iter (fun '(σ, u) =>
                                                       if (Nat.eqb (σ X) 0)
                                                       then Ret (inr (σ, inr Private))
                                                      else Ret (inl (update X (σ X - 1) σ, tt)))
                                        (σ0, tt).
  Proof.
    unfold sem_throw_stmt, interp_imp. unfold denote_stmt. fold denote_stmt. unfold while.
    specialize @interp_state_iter' as Hisi. red in Hisi. setoid_rewrite throw_prefix_iter.
    setoid_rewrite Hisi.
    eapply eutt_iter' with (RI := eq); auto.
    intros [σ1 [] ] [σ2 [] ] Heq. injection Heq; intros; subst. remember (sdec_body) as s.
    cbn. setoid_rewrite interp_state_bind. setoid_rewrite bind_ret_l.
    repeat rewrite bind_bind. rewrite Heqs.
    setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    setoid_rewrite throw_sdec_body_eq. destruct (σ2 X =? 0)%nat.
    - rewrite bind_bind, bind_ret_l. cbn. rewrite interp_state_ret. rewrite bind_ret_l. setoid_rewrite interp_state_ret.
      rewrite bind_ret_l. cbn. apply eqit_Ret. constructor; auto.
    - rewrite bind_bind, bind_ret_l. cbn. rewrite throw_prefix_ret. rewrite interp_state_ret. rewrite bind_ret_l.
      setoid_rewrite interp_state_ret.
      rewrite bind_ret_l. cbn. apply eqit_Ret. constructor. auto.
  Qed.



  Lemma sdec_eq σ0 : sem_stmt sdec σ0 ≈ Ret (update X 0 σ0 ,tt).
  Proof.
    unfold sdec. remember (While (Lit 1) sdec_body ) as s.
    unfold sem_stmt, interp_imp. cbn.
    setoid_rewrite try_catch_to_throw_prefix.
    setoid_rewrite interp_state_bind.  rewrite Heqs. clear Heqs s. setoid_rewrite while_sdec_body_eq'.
    remember (σ0 X) as X0. generalize dependent σ0. induction X0; intros.
    - setoid_rewrite unfold_iter. rewrite <- HeqX0. cbn. rewrite bind_bind.
      repeat rewrite bind_ret_l. cbn. repeat rewrite bind_bind, bind_ret_l. rewrite bind_ret_l.
      cbn. enough (σ0 = update X 0 σ0). rewrite H at 1. reflexivity.
      apply functional_extensionality. intros Y. unfold update.
      destruct (X =? Y) eqn : Heq; auto. apply eqb_eq in Heq. subst. auto.
    - rewrite unfold_iter. rewrite <- HeqX0. cbn. rewrite bind_bind. rewrite bind_ret_l.
      rewrite tau_eutt. assert (X0 - 0 = X0). lia. rewrite H.
      rewrite IHX0. 2 : { unfold update. rewrite eqb_refl. auto. }
      enough (update X 0 (update X X0 σ0) = update X 0 σ0). rewrite H0. reflexivity.
      unfold update. apply functional_extensionality. intros Y.
      destruct (X =? Y) eqn : Heq; auto.
  Qed.

  Lemma sdec_sdec_opt σ : sem_stmt sdec σ ≈ sem_stmt sdec_opt σ.
  Proof.
    unfold sdec_opt. unfold sem_stmt at 2. unfold interp_imp. cbn.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_state_trigger. cbn.
    apply sdec_eq.
  Qed.

End Examples.

*)
