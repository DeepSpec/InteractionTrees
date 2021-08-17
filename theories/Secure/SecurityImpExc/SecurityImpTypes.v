From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Events.Exception
     Events.ExceptionFacts
     Core.Divergence
     Dijkstra.TracesIT
     Dijkstra.ITrace
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.SecurityImpExc.SecurityImp
     Secure.SecurityImpExc.SecurityImpHandler
     Secure.StrongBisimProper
     Secure.SecurityImpExc.RaiseException
     Secure.SecurityImpExc.ITreeForall
.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Instance sense_preorder_in : Preorder := sense_preorder.

Notation label := sensitivity.

Definition labelled_equiv (Γ : privacy_map) (l : label) (σ1 σ2 : map)  : Prop :=
  forall x, leq (Γ x) l -> σ1 x = σ2 x.

Instance labelled_equit_equiv {Γ l} : Equivalence (labelled_equiv Γ l).
Proof.
  constructor; unfold labelled_equiv.
  - red. intros; auto.
  - red. intros. symmetry; auto.
  - red. intros. rewrite H; auto.
Qed.

Definition label_eqit_secure_impstate  (b1 b2 : bool) (Γ : privacy_map) (l : label) {R1 R2 : Type} (RR : R1 -> R2 -> Prop )
           (m1 : stateT map (itree (impExcE +' IOE)) R1) (m2 : stateT map (itree (impExcE +' IOE)) R2) : Prop :=
  forall σ1 σ2, labelled_equiv Γ l σ1 σ2 -> eqit_secure sense_preorder priv_exc_io (product_rel (labelled_equiv Γ l) RR) b1 b2 l (m1 σ1) (m2 σ2).

Definition label_state_sec_eutt {R1 R2} priv l (RR : R1 -> R2 -> Prop) m1 m2 :=
  label_eqit_secure_impstate true true  priv l RR m1 m2.

Definition sem_stmt (s : stmt) := interp_imp (denote_stmt s).

Definition sem_expr (e : expr) := interp_imp (denote_expr e).

Definition state_equiv {E R} (m1 m2 : stateT map (itree E) R) := forall (σ : map), m1 σ ≈ m2 σ.

Instance proper_eutt_secure_eutt  {E R1 R2 RR Label priv l} : Proper (@eutt E R1 R1 eq ==> @eutt E R2 R2 eq ==> iff)
                                                               (eqit_secure Label priv RR true true l).
Proof.
  eapply proper_eqit_secure_eqit.
Qed.

Instance proper_eq_itree_secure_eutt  {E R1 R2 RR Label priv l} : Proper (@eq_itree E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> iff)
                                                               (eqit_secure Label priv RR true true l).
Proof.
  repeat intro. assert (x ≈ y). rewrite H. reflexivity. 
  assert (x0 ≈ y0). rewrite H0. reflexivity. rewrite H1. rewrite H2. tauto.
Qed.

Instance proper_state_equiv_label_state_sec_eutt {R1 R2 RR priv l} : Proper (@state_equiv _ R1 ==> @state_equiv _ R2 ==> iff) (@label_state_sec_eutt R1 R2 priv l RR).
Proof.
  repeat intro. split.
  - intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1). eapply proper_eutt_secure_eutt; eauto. symmetry. auto. symmetry. auto.
  - intros. intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1).  eapply proper_eutt_secure_eutt; eauto.
Qed.
(* this is the notion of finiteness I want to work with 
   note that the linearness of these ITrees is part of what makes it enough
   otherwise I would need a more Forall like coinductive predicate
   I want to move a bunch of this raise exception stuff to another file
*)

Definition state_try_catch {E R} (m : stateT map (itree (impExcE +' E) ) R)  := 
                                   fun σ => try_catch (m σ).




Context (Γ : privacy_map).

Variant secure_stmt_at_label (observer pc lexn : label) (s : stmt) : Prop :=
  | ssal_leq : (leq pc observer) -> label_state_sec_eutt Γ observer eq (sem_stmt s) (sem_stmt s) -> secure_stmt_at_label observer pc lexn s
  | ssal_nleq : (~ leq pc observer) -> label_state_sec_eutt Γ observer top2 (sem_stmt s) (ret tt) -> secure_stmt_at_label observer pc lexn s.


Variant secure_expr_at_label (observer protection: label ) (e : expr) : Prop :=
  | seal_leq : (leq protection observer) -> label_state_sec_eutt Γ observer eq (sem_expr e) (sem_expr e) -> 
               secure_expr_at_label observer protection e
  | seal_nleq : (~leq protection observer) -> (exists n:value, label_state_sec_eutt Γ observer top2 (sem_expr e) (ret n)) ->
                secure_expr_at_label observer protection e
.

Definition secure_expr l e := forall observer, secure_expr_at_label observer l e.

Definition secure_stmt pc lexn c := forall observer, secure_stmt_at_label observer pc lexn c.

Inductive well_typed_expr : sensitivity -> expr -> Prop :=
  | wte_lit l n : well_typed_expr l (Lit n)
  | wte_var x l : leq (Γ x) l -> well_typed_expr l (Var x)
  | wte_plus l1 l2 e1 e2 : well_typed_expr l1 e1 -> well_typed_expr l2 e2 ->
                           well_typed_expr (join l1 l2) (Plus e1 e2)
  | wte_min l1 l2 e1 e2 : well_typed_expr l1 e1 -> well_typed_expr l2 e2 ->
                           well_typed_expr (join l1 l2) (Minus e1 e2)
  | wte_mult l1 l2 e1 e2 : well_typed_expr l1 e1 -> well_typed_expr l2 e2 ->
                           well_typed_expr (join l1 l2) (Mult e1 e2)
.


Inductive well_typed_stmt : sensitivity -> sensitivity -> stmt -> Prop :=
  | wts_manual pc lexn s : secure_stmt pc lexn s -> well_typed_stmt pc lexn s
  | wts_skip pc : well_typed_stmt pc Public Skip
  | wts_seq pc lexn1 lexn2 s1 s2 : well_typed_stmt pc lexn1 s1 -> well_typed_stmt (join lexn1 pc) lexn2 s2 ->
                                   well_typed_stmt pc (join lexn1 lexn2) (Seq s1 s2)
  | wts_assign pc l x e : well_typed_expr l e -> leq (join l pc) (Γ x) ->
                          well_typed_stmt pc Public (Assign x e)
  | wts_print pc le lp e : well_typed_expr le e -> leq (join le pc) lp ->
                           well_typed_stmt pc Public (Output lp e)
  | wts_if pc le lexn1 lexn2 e s1 s2 : well_typed_expr le e -> well_typed_stmt (join pc le) lexn1 s1 -> well_typed_stmt (join pc le) lexn2 s2 ->
                                       well_typed_stmt pc (join lexn1 lexn2) (If e s1 s2)
  | wts_while lexn e s : well_typed_expr Public e -> well_typed_stmt Public lexn s ->
                         well_typed_stmt Public lexn (While e s)
  | wts_raise pc l : leq pc l -> well_typed_stmt pc l (Raise l)
  | wts_try pc lexn1 lexn2 s1 s2 : well_typed_stmt pc lexn1 s1 -> well_typed_stmt (join lexn1 pc) lexn2 s2 ->
                                   well_typed_stmt pc lexn2 (TryCatch s1 s2)
.



Lemma well_typed_expr_upward_close l1 l2 e : leq l1 l2 -> well_typed_expr l1 e -> well_typed_expr l2 e.
Proof.
  revert l1 l2.
  induction e; intros; try inv H0.
  - constructor. eapply leq_sense_trans; eauto.
  - constructor.
  - assert (l2 = join l2 l2). destruct l2; auto. rewrite H0. constructor.
    + eapply IHe1; eauto. eapply IHe1; eauto. apply leq_sense_join_l.
    + eapply IHe2; eauto. eapply IHe2; eauto. apply leq_sense_join_r.
  - assert (l2 = join l2 l2). destruct l2; auto. rewrite H0. constructor.
    + eapply IHe1; eauto. eapply IHe1; eauto. apply leq_sense_join_l.
    + eapply IHe2; eauto. eapply IHe2; eauto. apply leq_sense_join_r.
  - assert (l2 = join l2 l2). destruct l2; auto. rewrite H0. constructor.
    + eapply IHe1; eauto. eapply IHe1; eauto. apply leq_sense_join_l.
    + eapply IHe2; eauto. eapply IHe2; eauto. apply leq_sense_join_r.
Qed.

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


Lemma well_typed_expr_correct l e : well_typed_expr l e -> secure_expr l e.
Proof.
  revert l. red. induction e; intros l Htype observer.
  - inv Htype. case_leq l observer.
    + left; auto. unfold sem_expr. cbn. unfold interp_imp.
      do 2 red. intros. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn.
      unfold get. apply secure_eqit_ret; split; auto. cbn.
      red in H0. apply H0. eapply leq_sense_trans; eauto.
    + right; auto. apply expr_only_ret.
  - case_leq l observer.
    + left; auto. unfold sem_expr. cbn. unfold interp_imp. do 2 red.
      intros. setoid_rewrite interp_state_ret. apply secure_eqit_ret.
      split; auto.
    + right; auto. exists 0. unfold sem_expr. cbn. unfold interp_imp. do 2 red.
      intros. setoid_rewrite interp_state_ret. apply secure_eqit_ret. split; auto.
      cbv. auto.
  - inv Htype.
    assert (well_typed_expr (join l1 l2) e1 ). eapply well_typed_expr_upward_close; eauto. apply leq_sense_join_l.
    assert (well_typed_expr (join l1 l2) e2 ). eapply well_typed_expr_upward_close; eauto. apply leq_sense_join_r.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H4; eauto.
      intros [s3 r1] [s4 r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [? ?] [? ?] [? ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. split; auto.
    + right; auto. apply expr_only_ret.
  - inv Htype.
    assert (well_typed_expr (join l1 l2) e1 ). eapply well_typed_expr_upward_close; eauto. apply leq_sense_join_l.
    assert (well_typed_expr (join l1 l2) e2 ). eapply well_typed_expr_upward_close; eauto. apply leq_sense_join_r.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H4; eauto.
      intros [s3 r1] [s4 r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [? ?] [? ?] [? ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. split; auto.
    + right; auto. apply expr_only_ret.
  - inv Htype.
    assert (well_typed_expr (join l1 l2) e1 ). eapply well_typed_expr_upward_close; eauto. apply leq_sense_join_l.
    assert (well_typed_expr (join l1 l2) e2 ). eapply well_typed_expr_upward_close; eauto. apply leq_sense_join_r.
    apply IHe1 with (observer := observer) in H.
    apply IHe2 with (observer := observer) in H0. inv H; inv H0; try contradiction.
    + left; auto.
      unfold sem_expr. cbn. unfold interp_imp. do 2 red. intros.
      repeat setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind. 2 : eapply H4; eauto.
      intros [s3 r1] [s4 r2] Hprod. destruct Hprod. cbn in *. subst.
      eapply secure_eqit_bind. 2 : eapply H5; eauto.
      intros [? ?] [? ?] [? ?]. cbn in *. subst. setoid_rewrite interp_state_ret.
      apply secure_eqit_ret. split; auto.
    + right; auto. apply expr_only_ret.
Qed.

Lemma state_secure_eutt_ret_aux:
  forall R t1 t2 (observer : sensitivity) (r1 r2 : R),
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure sense_preorder priv_exc_io (product_rel (labelled_equiv Γ observer) (@top2 R R)) true
                    true observer (interp_imp t1 σ1) (Ret(σ2,r1))) ->
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        eqit_secure sense_preorder priv_exc_io (product_rel (labelled_equiv Γ observer) (@top2 R R)) true
                    true observer (interp_imp t2 σ1) (Ret(σ2,r2))) ->
    forall σ1 σ2 : map,
      labelled_equiv Γ observer σ1 σ2 ->
      eqit_secure sense_preorder priv_exc_io (product_rel (labelled_equiv Γ observer) top2) true
                  true observer (interp_state handle_imp t1 σ1)
                  (interp_state handle_imp t2 σ2).
Proof.
  intros R t1 t2 observer r1 r2 Hr1 Hr2 s1 s2 Hs12.
  set ((product_rel (labelled_equiv Γ observer) top2)) as Rst.
  apply eqit_secure_RR_imp with (RR1 := rcompose Rst Rst).
  { intros [? ?] [? ?] [? ?]. destruct r3. cbn in *. unfold Rst in *.
    split. 2 : cbv; auto. destruct REL1 as [REL1 _]. destruct REL2 as [REL2 _].
    cbn in *. etransitivity; eauto. }
  eapply eqit_secure_trans; eauto. eapply eqit_secure_sym.
  apply eqit_secure_RR_imp with (RR1 := Rst).
  { intros. split. 2 : cbv; auto. unfold Rst in PR. destruct PR.
    symmetry. auto. }
  assert (eqit_secure sense_preorder priv_exc_io Rst true true observer (Ret (s2, r2) ) (Ret (s2,r1))).
  { apply secure_eqit_ret. unfold Rst in *. split; auto; cbv; auto. }
  apply eqit_secure_RR_imp with (RR1 := rcompose Rst Rst).
  { intros [? ?] [? ?] [? ?]. destruct r3. cbn in *. unfold Rst in *.
    split. 2 : cbv; auto. destruct REL1 as [REL1 _]. destruct REL2 as [REL2 _].
    cbn in *. etransitivity; eauto. }
  eapply eqit_secure_trans; try apply Hr2; eauto. reflexivity. 
Qed.

Lemma update_labelled_equiv_invisible:
  forall (x : var) (observer : sensitivity),
    ~ leq (Γ x) observer ->
    forall (σ1 : map) (v : value) (σ2 : map),
      labelled_equiv Γ observer σ1 σ2 -> labelled_equiv Γ observer (update x v σ1) (σ2).
Proof.
  intros x observer H σ1 v σ2 H2.
  red. red in H2. intros.
  unfold update. destruct (x =? x0) eqn : Heq; auto.
  exfalso. apply H. apply eqb_eq in Heq. subst; auto.
Qed.

Lemma update_labelled_equiv_visible:
  forall (x : var) (observer : sensitivity),
    leq (Γ x) observer ->
    forall (σ1 : map) (v : value) (σ2 : map),
      labelled_equiv Γ observer σ1 σ2 -> labelled_equiv Γ observer (update x v σ1) (update x v σ2).
Proof.
  intros x observer H σ1 v σ2 H2.
  red. red in H2. intros. unfold update. 
  destruct (x =? x0) eqn : Heq; auto.
Qed.

Lemma assign_well_typed_correct x e pc lexn : well_typed_stmt pc lexn (Assign x e) -> secure_stmt pc lexn (Assign x e).
Proof.
  red. intros. 
  inv H; auto.
  assert (Hpc : leq pc (Γ x) ).
  { eapply leq_sense_trans; eauto. apply leq_sense_join_r. }
  assert (Hl : leq l (Γ x) ).
  { eapply leq_sense_trans; try apply H5. apply leq_sense_join_l. }
  assert (He : well_typed_expr (Γ x) e ).
  { eapply well_typed_expr_upward_close with (l2:= Γ x); eauto. }
  apply well_typed_expr_correct in He. 
  specialize ( He observer). inv He.
  - left. eapply leq_sense_trans; eauto.
    do 2 red in H0. do 2 red. intros. unfold sem_stmt.
    cbn. unfold interp_imp. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? ?] [? ?] [? ?].
    cbn in H2, H3. subst. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
    cbn. apply secure_eqit_ret; split; auto. cbn. apply update_labelled_equiv_visible; auto. 
  - case_leq pc observer.
    + left; auto.
      destruct H0 as [n Hn]. unfold sem_stmt.
      cbn. unfold interp_imp. do 2 red. intros. setoid_rewrite interp_state_bind.
      do 2 red in Hn.
      eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [? ?] [? ?] [? ?]. clear H3. cbn in H2. cbn.
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
      eapply proper_eutt_secure_eutt; try apply H2; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [? ?] [? ?] [? ?]. cbn in H3.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn.
      apply secure_eqit_ret; split; auto. 
      cbn. apply update_labelled_equiv_invisible; auto.
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

Lemma assign_only_ret e x σ : exists σ', sem_stmt (Assign x e) σ ≈ Ret (σ', tt).
Proof.
  unfold sem_stmt, interp_imp. cbn.
  setoid_rewrite interp_state_bind. specialize (expr_only_ret' e σ) as He.
  destruct He as [n Hn]. setoid_rewrite Hn. setoid_rewrite bind_ret_l.
  setoid_rewrite interp_state_trigger. cbn. eexists; reflexivity.
Qed.



Lemma assign_max_exception_label x e lexn : max_exception_label lexn (sem_stmt (Assign x e) ).
Proof.
  red. intros. red in H. destruct H as [σ Hσ]. 
  specialize (assign_only_ret e x σ) as Haor. destruct Haor as [σ' Haor].
  setoid_rewrite Haor in Hσ. exfalso. eapply raises_exception_ret; eauto.
Qed.


From Paco Require Import paco.
Lemma output_max_exception_label e lexn l : max_exception_label lexn (sem_stmt (Output l e ) ).
Proof.
  red. intros. exfalso. red in H. destruct H as [s Hs].
  unfold sem_stmt, interp_imp in Hs. cbn in Hs. setoid_rewrite interp_state_bind in Hs.
  specialize (expr_only_ret' e s) as Hes. destruct Hes as [n Hn]. rewrite Hn in Hs.
  rewrite bind_ret_l in Hs. setoid_rewrite interp_state_trigger in Hs. cbn in Hs.
  rewrite bind_trigger in Hs. red in Hs. destruct Hs as [t' [Hconv Ht'] ].
  symmetry in Ht'. apply eqit_inv_bind_vis in Ht'.
  destruct Ht' as [Ht' | Ht'].
  - destruct Ht' as [kxa [Heq Hbind] ]. 
    rewrite Heq in Hconv. inversion Hconv.
    + symmetry in H. eapply eqit_inv_ret_vis; eauto.
    + pinversion H; subst; ITrace.inj_existT; subst.
      rewrite <- REL in H0. clear H REL. destruct b. specialize (Hbind tt).
      inversion H0.
      * rewrite H in Hbind. rewrite bind_ret_l in Hbind. setoid_rewrite bind_trigger in Hbind.
        pinversion Hbind.
      * setoid_rewrite H in Hbind. setoid_rewrite bind_vis in Hbind. pinversion Hbind.
  - destruct Ht' as [ [] [? ?] ]. setoid_rewrite bind_trigger in H0.
    pinversion H0; subst;  ITrace.inj_existT; subst. discriminate.
Qed.


Lemma output_well_typed_correct l1 lexn pc e : 
  well_typed_stmt pc lexn (Output l1 e) -> secure_stmt pc lexn (Output l1 e).
Proof.
  red. intros. inv H; auto.
  assert (Hle : leq le l1).
  { eapply leq_sense_trans; eauto. apply leq_sense_join_l. }
  assert (Hpc : leq pc l1).
  { eapply leq_sense_trans; try apply H5. apply leq_sense_join_r. }
  assert (He : well_typed_expr l1 e ).
  { eapply well_typed_expr_upward_close with (l1 := le); eauto. }
  apply well_typed_expr_correct in He. specialize (He observer).
  inv He.
  - assert (Hobs : leq pc observer). eapply leq_sense_trans; eauto.
    left; auto.
    do 2 red in H0. do 2 red. intros. unfold sem_stmt. cbn.
    unfold interp_imp. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? ?] [? ?] [? ?].
    cbn in H2, H3. subst. cbn. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
    cbn. setoid_rewrite bind_trigger. cbn.
    apply eqit_secure_public_Vis; try apply H.
    intros []. apply secure_eqit_ret; auto.
  - case_leq pc observer.
    + left; auto. destruct H0 as [n Hn]. do 2 red in Hn. cbn in Hn.
      unfold sem_stmt. cbn. unfold interp_imp. do 2 red. 
      intros. setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [? ?] [? ?] [? ?]. cbn in H2. clear H3. cbn.
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
      eapply proper_eutt_secure_eutt; try apply H2; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [? ?] [? ?] [? ?]. cbn. 
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn. setoid_rewrite bind_trigger. cbn.
      apply eqit_secure_private_VisL; auto. constructor; apply tt.
      intros []. apply secure_eqit_ret; auto.
Qed.

Lemma seq_well_typed_correct pc lexn1 lexn2 s1 s2 : 
  secure_stmt pc lexn1 s1 -> secure_stmt (join lexn1 pc) lexn2 s2 ->
  secure_stmt pc (join lexn1 lexn2) (Seq s1 s2).
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
    { exfalso. apply H. eapply leq_sense_trans; try apply H2. apply leq_sense_join_r. }
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
    rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
    eapply secure_eqit_bind; try eapply H0; auto.
    intros [? ?] [? ?] [? ?]. apply H3; auto.
Qed.


Lemma if_well_typed_correct pc le lexn1 lexn2 e s1 s2 :
  secure_expr le e -> secure_stmt (join pc le) lexn1 s1 -> secure_stmt (join pc le) (lexn2) s2 ->
  secure_stmt pc (join lexn1 lexn2) (If e s1 s2).
Proof.
  intros He Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  specialize (He observer).
  inv Hc1obs; inv Hc2obs; try contradiction.
  - left. eapply leq_sense_trans; eauto. apply leq_sense_join_l.
    inv He. 2 : { exfalso. apply H3. eapply leq_sense_trans; eauto. apply leq_sense_join_r. }
    unfold sem_stmt, interp_imp.
    cbn. do 2 red. intros. setoid_rewrite interp_state_bind. eapply secure_eqit_bind; try apply H4; auto.
    intros [? ?] [? ?] [? ?]. cbn in H6, H7. subst. cbn. destruct v0; eauto.
  - case_leq pc observer.
    + left; auto. unfold sem_stmt, interp_imp. cbn. do 2 red. intros.
      setoid_rewrite interp_state_bind.
      inv He; try contradiction.
      * eapply secure_eqit_bind; try apply H5; eauto.
        intros [? ?] [? ?] [? ?]. cbn in H8, H7. cbn. subst. do 2 red in H0, H2.
        eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
        { intros [? [] ] [? [] ] [? ?]. split; auto. } 
        destruct v0; try eapply  state_secure_eutt_ret_aux; cbn in *; eauto.
      * destruct H6 as [n Hn]. do 2 red in Hn. 
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
       eapply proper_eutt_secure_eutt; try apply H5; try reflexivity.
       inv He.
       * eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2) .
         2 : { apply expr_only_ret_aux1; auto. }
         intros [? ?] [? ?] [? ?]. cbn. destruct v; cbn in *; eauto.
       * destruct H7. eapply secure_eqit_bind; try apply expr_only_ret_aux1; auto.
         intros [? ?] [? ?] [? ?]. cbn. destruct v; cbn in *; eauto.
Qed.

Lemma if_max_label lexn1 lexn2 e s1 s2: max_exception_label lexn1 (sem_stmt s1) -> max_exception_label lexn2 (sem_stmt s2) ->
                                        max_exception_label (join lexn1 lexn2) (sem_stmt (If e s1 s2)).
Proof.
  intros Hc1 Hc2. unfold sem_stmt, interp_imp. cbn. red. intros. red in H.
  destruct H as [s Hs]. red in Hs. destruct Hs as [t' [Hconv Ht'] ].
  setoid_rewrite interp_state_bind in Ht'. specialize (expr_only_ret' e s) as [n Hn].
  rewrite Hn in Ht'. rewrite bind_ret_l in Ht'. cbn in Ht'. destruct n.
  + enough (leq l' lexn2). eapply leq_sense_trans; eauto. apply leq_sense_join_r.
    apply Hc2. exists s. red. exists t'. split; auto.
  + enough (leq l' lexn1). eapply leq_sense_trans; eauto. apply leq_sense_join_l.
    apply Hc1. exists s. red. exists t'. split; auto.
Qed.

(* maybe it would be easier to solve this problem in a more abstract way with monads rather than stmts*)
Lemma while_max_label lexn e s : max_exception_label lexn (sem_stmt s) ->
                                 max_exception_label lexn (sem_stmt (While e s)).
Proof.
  intros Hc. apply max_exception_label_coind_imp_ind. intros.
  assert (forall σ, max_exception_label_coind lexn (sem_stmt s σ)  ).
  apply max_exception_label_coind_flip_imp_ind; auto. 
  unfold sem_stmt, interp_imp. cbn. unfold while.
  specialize @interp_state_iter' as Hisi. red in Hisi. 
  setoid_rewrite Hisi.
  unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree.
  cbn. eapply itree_forall_iter_ev. intros [s' [] ].
  setoid_rewrite interp_state_bind. cbn. specialize (expr_only_ret' e s') as [n Hn].
  rewrite Hn. rewrite bind_ret_l. cbn. destruct n.
  - rewrite interp_state_ret. rewrite bind_ret_l. cbn. pfold. constructor. auto.
  - apply itree_forall_bind with (PS := fun _ => True).
    + setoid_rewrite interp_state_bind. 
      apply itree_forall_bind with (PS := fun _ => True); try apply H.
      intros . setoid_rewrite interp_state_ret. pfold. constructor. auto.
    + intros. pfold. constructor. auto.
Qed.

Lemma while_well_typed_correct lexn e s :
  secure_expr Public e -> secure_stmt Public lexn s ->
  secure_stmt Public lexn (While e s).
Proof.
  intros He Hc. red. intros.
  assert (leq Public observer).
  { destruct observer; cbv; auto. }
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


Lemma try_catch_well_typed_correct lexn1 lexn2 s1 s2 pc :
  secure_stmt pc lexn1 s1 -> max_exception_label lexn1 (sem_stmt s1) ->
  secure_stmt (join pc lexn1) lexn2 s2 -> max_exception_label lexn2 (sem_stmt s2) ->
  secure_stmt pc lexn2 (TryCatch s1 s2).
Proof.
  intros Hc1 Hec1 Hc2 Hec2. red. intros. specialize (Hc1 observer).
  inv Hc1.
  - left; auto. unfold sem_stmt. cbn. unfold interp_imp.
    do 2 red. intros. do 2 red in H0. apply H0 in H1.
    case_leq lexn1 observer.
    + (* in this case all exceptions are visible, with this constraint everything is 
         is fine, because visible exceptions must match up on both sides *) admit.
    + (* in this case there might be invisble exceptions 
         but maybe the pc somehow saved us from making any mistakes
       *)
    specialize (Hc2 observer). inv Hc2.
Abort.
          
(* I'm actually a bit confused as to why this went through so easily 
   why don't I need to do case analysis on whether exceptions are output?
 *)
(* Today, 


  1: work out definition for exception part of legical relation
  2: work out Seq case

*)
