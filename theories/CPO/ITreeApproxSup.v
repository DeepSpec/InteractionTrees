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
.

Section test.

  Variant stateE : Type -> Type :=
    | Get : stateE nat
    | Put : nat -> stateE unit.

  Definition test_and_apply_ex {A B C: Type} (e1 : stateE A) (a : A) (e2 : stateE B) (k : B -> C) 
    (default : C) : C.
  inv e1; inv e2.
  - exact (k a).
  - exact default.
  - exact default.
  - exact (k a).
  Defined.

  Lemma test_and_apply_correct_ex {A C : Type} (e : stateE A) (a : A) (k : A -> C) (default : C) : 
    test_and_apply_ex e a e k default = (k a).
  Proof.
    destruct e. cbv. auto. cbv. auto.
  Qed.

End test.


Section ITreeApproxSup.
  Context {E : Type -> Type} {R : Type}.

  Context (test_and_apply : forall {A B C : Type} (e1 : E A) (a : A) (e2 : E B) (k : B -> C) (default : C) , C).

  Context (test_and_apply_correct_eq : forall A C (e : E A) (a : A) (k : A -> C) (default : C), test_and_apply A A C e a e k default = k a  ).

  Context (test_and_apply_correct_type_eq : forall A C (e1 e2 : E A) (a : A) (k : A -> C) (default : C), test_and_apply A A C e1 a e2 k default = k a  ).


  Context (test_and_apply_correct_neq : forall A B C (e1 : E A) (e2 : E B) a k (default :C),
              ~ JMeq e1 e2 ->
              test_and_apply A B C e1 a e2 k default = default).

  Context (E_injective : forall (A B : Type), E A = E B -> A = B).

  Arguments test_and_apply {A B C}.

  Definition spin_seq : sequence (itree E R) := fun n => ITree.spin.

  CoFixpoint peel_tau_elem' (ot : itree' E R) : itree E R :=
    match ot with
    | RetF r => Ret r
    | TauF t0 => t0
    | VisF e k => Vis e (fun a => peel_tau_elem' (observe (k a) ) ) end.

  Definition peel_tau_elem t := peel_tau_elem' (observe t).

  Definition peel_tau (seq : sequence (itree E R) ) : sequence (itree E R) :=
    fun n => peel_tau_elem (seq n).

  Instance peel_tau_elem_proper : Proper (@eq_itree E R R eq ==> eq_itree eq) (peel_tau_elem).
  Proof.
    intros t1 t2 Ht12. generalize dependent t2. revert t1. ginit. gcofix CIH.
    intros. pinversion Ht12; try inv CHECK; subst.
    - gstep. red. unfold observe. cbn. rewrite <- H0. rewrite <- H. constructor. auto.
    - gfinal. right. eapply paco2_mon with (r := bot2); intros; try contradiction.
      pstep. red. unfold observe. cbn. rewrite <- H0. rewrite <- H.  pstep_reverse.
    - gstep. red. unfold observe. cbn. rewrite <- H0. rewrite <- H.  constructor.
      gfinal. left. eauto.
 Qed.

  Lemma peel_tau_elem_ret r : peel_tau_elem (Ret r) ≅ Ret r.
  Proof.
    pstep. red. cbv. constructor. auto.
  Qed.

  Lemma peel_tau_elem_tau t : peel_tau_elem (Tau t) ≅ t.
  Proof.
    pstep. red. cbv.
    enough (t ≅ t). punfold H. reflexivity.
  Qed.

  Lemma peel_tau_elem_vis A (e : E A) k : peel_tau_elem (Vis e k) ≅ Vis e (fun a => peel_tau_elem (k a) ).
  Proof.
    pstep. red. unfold observe at 1. cbn. constructor.
    left. enough (peel_tau_elem (k v) ≅ (peel_tau_elem (k v) )  ). auto.
    reflexivity.
  Qed.

  Lemma peel_tau_eutt t : peel_tau_elem t ≈ t.
  Proof.
    ginit. revert t. gcofix CIH. intros t.
    destruct (observe t) eqn : Heq; symmetry in Heq; use_simpobs.
    - repeat rewrite Heq. rewrite peel_tau_elem_ret. gstep. constructor; auto.
    - repeat rewrite Heq. rewrite peel_tau_elem_tau. rewrite tau_euttge.
      gfinal. right. assert (t0 ≈ t0). reflexivity.
      eapply paco2_mon; eauto. intros; contradiction.
    - repeat rewrite Heq. rewrite peel_tau_elem_vis. gstep. constructor.
      intros. gfinal. left. auto.
  Qed.
 
  CoFixpoint peel_vis_elem' {A : Type} (e : E A) (a : A) (ot : itree' E R) : itree E R :=
    match ot with
    | RetF r => Ret r
    | TauF t0 => Tau (peel_vis_elem' e a (observe t0))
    | VisF e' k => test_and_apply e a e' k (ITree.spin) end.

  Definition peel_vis_elem {A : Type} (e : E A) (a : A) (t : itree E R) : itree E R :=
    peel_vis_elem' e a (observe t).

  Instance peel_vis_elem_proper {A} {e : E A} {a : A} : Proper (@eq_itree E R R eq ==> eq_itree eq) (peel_vis_elem e a).
  Proof.
    intros t1 t2 Ht12. generalize dependent t2. revert t1. pcofix CIH.
    intros.  unfold peel_vis_elem. pinversion Ht12; try inv CHECK; subst.
    - pstep. red. cbn. constructor; auto.
    - pstep. red. cbn. constructor.  eauto.
    - pstep. red. cbn. unfold observe. cbn. 

      assert (A = u \/ ~ A = u). apply classic.
      assert (JMeq e e0 \/ ~ JMeq e e0). apply classic.
      destruct H1.
      + subst. destruct H2.
        * inv H1. inj_existT. subst. repeat rewrite test_and_apply_correct_eq.
          pstep_reverse. eapply paco2_mon; try apply REL. intros; contradiction.
        * repeat rewrite test_and_apply_correct_neq; auto. pstep_reverse.
          eapply paco2_mon with (r := bot2); intros; try contradiction.
          enough (@ITree.spin E R ≅ ITree.spin). punfold H2. reflexivity.
      + inv H2.
        * inv H3. apply E_injective in H4. contradiction. 
        * repeat rewrite test_and_apply_correct_neq; auto. pstep_reverse.
          eapply paco2_mon with (r := bot2); intros; try contradiction.
          enough (@ITree.spin E R ≅ ITree.spin). punfold H2. reflexivity.
  Qed.

  Lemma peel_vis_elem_spec : forall A (e : E A) (a : A) (t : itree E R) k,
      t ≈ Vis e k -> peel_vis_elem e a t ≈ (k a).
  Proof.
    intros A e a. pcofix CIH. intros. pfold. red. cbn.
    unfold observe at 1. cbn. punfold H0. red in H0. cbn in H0.
    remember (VisF e k) as x. hinduction H0 before r; intros; try discriminate.
    - inv Heqx. inj_existT. subst. rewrite test_and_apply_correct_eq. pclearbot. pstep_reverse. 
      eapply paco2_mon; eauto. intros; contradiction.
    - constructor. auto. eapply IHeqitF; eauto.
  Qed. (* appear to have not needed coinduction in the above proof *)

  Lemma peel_vis_elem_vis_eq : forall A (e : E A) (a : A) (k : A -> itree E R),
      peel_vis_elem e a (Vis e k) ≅ k a.
  Proof.
    intros. unfold peel_vis_elem. cbn. pfold. red. cbn. unfold observe at 1. cbn.
    rewrite test_and_apply_correct_eq. pstep_reverse.
    enough (k a ≅ k a); eauto. reflexivity.
  Qed.

  Lemma peel_vis_elem_vis_type_eq : forall A (e1 e2 : E A) (a : A) (k : A -> itree E R),
      peel_vis_elem e1 a (Vis e2 k) ≅ k a.
  Proof.
    intros. unfold peel_vis_elem. cbn. pfold. red. cbn. unfold observe at 1. cbn.
    rewrite test_and_apply_correct_type_eq. pstep_reverse.
    enough (k a ≅ k a); eauto. reflexivity.
  Qed.

  Lemma peel_vis_elem_vis_type_neq : forall A B (ea : E A) (eb : E B) (a : A) (k : B -> itree E R),
      A <> B -> peel_vis_elem ea a (Vis eb k) ≅ ITree.spin.
  Proof.
    intros. unfold peel_vis_elem. cbn. pfold. red. cbn. unfold observe at 1. cbn.
    destruct (classic (JMeq ea eb)).
    - inv H0. apply E_injective in H2. apply H in H2. contradiction.
    - rewrite test_and_apply_correct_neq; auto. cbn. constructor.
      left. enough (@ITree.spin E R ≅ ITree.spin). auto. reflexivity.
  Qed.

  Lemma peel_vis_elem_ret : forall A (e : E A) (a : A) (r : R),
      peel_vis_elem e a (Ret r) ≅ Ret r.
  Proof.
    intros. unfold peel_vis_elem. cbn. pstep. red. cbn. constructor.
    auto.
  Qed.

  Lemma peel_vis_elem_tau : forall A (e : E A) (a : A) t,
      peel_vis_elem e a (Tau t) ≅ Tau (peel_vis_elem e a t).
  Proof.
    intros. pstep. red. cbn. constructor. left. 
    enough (peel_vis_elem e a t ≅ peel_vis_elem e a t). punfold H.
    reflexivity.
  Qed.

  Definition peel_vis  {A : Type} (e : E A) (a : A) (seq : sequence (itree E R) ) :=
    fun n => peel_vis_elem e a (seq n). 

  (* change peel_tau to be noop on Ret, Vis*)
  CoFixpoint itree_approx_sup (seq : sequence (itree E R) ) : itree E R :=
    match observe (seq 0) with
    | RetF r => Ret r
    | VisF e k => Vis e (fun a => itree_approx_sup (peel_vis e a seq))
    | TauF t0 => Tau (itree_approx_sup (peel_tau (advance seq) ) )
    end.

  (* may need an assumption that RR is a partial order for some properties*)
  Definition monotone_approx (RR : R -> R -> Prop) (seq : sequence (itree E R ) ) : Prop :=
    forall n m, n <= m -> strong_itree_approx RR (seq n) (seq m). 

  (* will want to show that a lot of this gets preserved *)

  Lemma advance_preserves_monotone_approx : forall (RR : R -> R -> Prop) (seq : sequence (itree E R ) ),
      monotone_approx RR seq -> monotone_approx RR (advance seq).
  Proof.
    unfold monotone_approx. intros. unfold advance. apply H. lia.
  Qed.

  Lemma peel_tau_preserves_monotone_approx : forall (RR : R -> R -> Prop) (seq : sequence (itree E R ) ),
      monotone_approx RR seq -> monotone_approx RR (peel_tau seq).
  Proof.
    unfold monotone_approx. unfold peel_tau. intros.
    apply H in H0 as Hnm. remember (seq n) as tn. remember (seq m) as tm.
    clear Heqtn Heqtm.
    generalize dependent tn. generalize dependent tm. pcofix CIH. intros.
    punfold Hnm. red in Hnm. inv Hnm; pclearbot; eauto.
    - pfold. red. unfold observe. cbn. rewrite <- H1. rewrite <- H2. constructor. auto.
    - pfold. red. unfold observe. cbn. rewrite <- H1. rewrite <- H2. constructor. right. eapply CIH; eauto.
    - eapply paco2_mon with (r := bot2); intros; try contradiction.
      pfold. red. unfold observe. cbn. rewrite <- H1. rewrite <- H2.
      punfold H3.
    - eapply paco2_mon with (r := bot2); intros; try contradiction.
      use_simpobs. rewrite H1. rewrite peel_tau_elem_tau.
      rewrite H4. apply strong_itree_approx_spin_bottom.
  Qed.

  Lemma peel_tau_elem_spin : peel_tau_elem ITree.spin ≅ ITree.spin.
  Proof.
    intros. pstep. red. cbn. constructor. left.
    enough (@ITree.spin E R ≅ ITree.spin); auto. reflexivity.
  Qed.

  Lemma peel_vis_elem_spin : forall A (e : E A) (a : A), peel_vis_elem e a ITree.spin ≅ ITree.spin.
  Proof.
    intros. ginit. gcofix CIH. gstep. red. cbn. constructor.
    gfinal. left. eapply CIH.
  Qed.

  Lemma spin_cong_tau_spin : @ITree.spin E R ≅ Tau ITree.spin.
  Proof.
    pfold. red. cbn. constructor. left.
    enough (@ITree.spin E R ≅ ITree.spin). auto. reflexivity.
  Qed.

  Lemma peel_vis_preserves_monotone_approx : forall (RR : relation R) (seq : sequence (itree E R) ) (A : Type) (e : E A) (a : A),
      monotone_approx RR seq -> monotone_approx RR (peel_vis e a seq).
  Proof.
    unfold monotone_approx. unfold peel_vis. intros.  apply H in H0. remember (seq n) as t0. remember (seq m) as t1.
    clear Heqt1 Heqt0. generalize dependent t1. revert t0. pcofix CIH. intros t0 t1 Ht. 
    pstep. red. unfold observe. cbn. pinversion Ht.
    - constructor; auto.
    - destruct (classic (A = A0) ); subst.
      + repeat rewrite test_and_apply_correct_type_eq. specialize (H2 a).
        assert (paco2 (strong_itree_approx_ RR id) r (k1 a) (k2 a)).
        eapply paco2_mon; eauto. intros; contradiction. punfold H3.
      + repeat rewrite test_and_apply_correct_neq.
        * enough (paco2 (strong_itree_approx_ RR id) r (ITree.spin) (ITree.spin) ). punfold H4.
          eapply paco2_mon with (r := bot2); intros; try contradiction. 
          apply strong_itree_approx_spin_bottom.
        * intro. inv H4. apply E_injective in H6. contradiction.
        * intro. inv H4. apply E_injective in H6. contradiction.
    - constructor. right. apply CIH; auto.
    - match goal with |- strong_itree_approxF RR (upaco2 (strong_itree_approx_ RR id) r) id (_observe ?t1) (_observe ?t2) =>
                      remember t1 as tspin; remember t2 as tr end.
      clear Heqtr. enough (strong_itree_approx RR tspin tr). punfold H4.
      eapply strong_itree_approx__mono; eauto with paco. intros. pclearbot.
      left. eapply paco2_mon; eauto. intros; contradiction.
      subst. use_simpobs.
      enough (strong_itree_approx RR (Tau (peel_vis_elem e a t2)) tr). auto.
      rewrite H3. rewrite peel_vis_elem_spin. rewrite <- spin_cong_tau_spin.
      apply strong_itree_approx_spin_bottom.
  Qed.

  Lemma peel_vis_n : forall (seq : sequence (itree E R) ) A (e : E A) a n t, t ≅ seq n -> peel_vis_elem e a t ≅ (peel_vis e a seq n).
  Proof.
    intros. unfold peel_vis. rewrite H. reflexivity.
  Qed.

  Lemma sup_spin_seq : forall (seq : sequence (itree E R) ), (forall n, seq n ≅ ITree.spin) -> itree_approx_sup seq ≅ ITree.spin.
  Proof.
    ginit. gcofix CIH. intros. gstep. red. unfold observe at 1. cbn.
    destruct (observe (seq 0) ) eqn : Hseq0.
    - symmetry in Hseq0. apply simpobs in Hseq0. exfalso. specialize (H0 0). rewrite Hseq0 in H0.
      pinversion H0; inv CHECK.
    - destruct (observe (seq 1) ) eqn : Hseq1.
      + symmetry in Hseq1. apply simpobs in Hseq1. rewrite H0 in Hseq1. pinversion Hseq1; inv CHECK.
      + constructor. gfinal. left. eapply CIH. intros. unfold peel_tau. unfold advance. specialize (H0 (S n)).
        punfold H0. red in H0. cbn in *. inv H0; try inv CHECK. pclearbot. 
        use_simpobs. rewrite H1.
        rewrite peel_tau_elem_tau. auto.
      + exfalso. symmetry in Hseq1. apply simpobs in Hseq1. rewrite H0 in Hseq1. pinversion Hseq1; inv CHECK.
    - symmetry in Hseq0. exfalso. apply simpobs in Hseq0. specialize (H0 0). rewrite Hseq0 in H0.
      pinversion H0; inv CHECK.
  Qed.

  Lemma sup_head_tau : forall (seq : sequence (itree E R) ) t1, (seq 0 ≅ Tau t1) ->
                                                          itree_approx_sup seq ≅ Tau (itree_approx_sup (peel_tau (advance seq))).
  Proof.
    ginit. intros.
    gstep. red. unfold observe at 1. cbn. punfold H0.
    inv H0; try inv CHECK. cbn. constructor. gfinal. right.
    enough (itree_approx_sup (peel_tau (advance seq)) ≅ itree_approx_sup (peel_tau (advance seq))); auto.
    reflexivity.
  Qed.

  Lemma sup_head_ret : forall  (seq : sequence (itree E R) ) r, seq 0 ≅ Ret r -> itree_approx_sup seq ≅ Ret r.
  Proof.
    ginit. intros. gstep. red. unfold observe at 1. cbn. punfold H0. inv H0; try inv CHECK. constructor; auto.
  Qed.

  Lemma sup_head_vis : forall (seq : sequence (itree E R) ) A (e : E A) k, seq 0 ≅ Vis e k -> 
                                                                      itree_approx_sup seq ≅ Vis e (fun a => itree_approx_sup (peel_vis e a seq) ).
  Proof.
    ginit. intros. gstep. red. unfold observe at 1. cbn. punfold H0. inv H0; try inv CHECK. inj_existT. subst.
    constructor. intros a. gfinal. right.
    enough (itree_approx_sup (peel_vis e a seq) ≅ itree_approx_sup (peel_vis e a seq)); auto. reflexivity.
  Qed.

  Definition fun_eq {A B} (f g : A -> (itree E B)) := respectful eq (eq_itree eq) f g.

  Instance proper_fun_seq : Proper (fun_eq ==> eq_itree eq) itree_approx_sup.
  Proof.
    ginit. gcofix CIH. intros seq1 seq2 Hseq.  repeat red in Hseq.
    destruct (observe (seq1 0)) eqn : Heq; symmetry in Heq; use_simpobs.
    - repeat rewrite sup_head_ret; eauto. 2 : erewrite <- Hseq; eauto. gstep; constructor; auto.
    - rewrite sup_head_tau; eauto. rewrite (sup_head_tau seq2); eauto. 2 : erewrite <- Hseq; eauto. 
      gstep. constructor. gfinal. left. eapply CIH. red. red. intros. subst.
      unfold advance. unfold peel_tau. rewrite Hseq; auto. reflexivity.
    - rewrite sup_head_vis; eauto. rewrite sup_head_vis; eauto. 2 : erewrite <- Hseq; eauto.
      gstep. constructor. gfinal. left. eapply CIH. red. red. intros; subst.
      unfold peel_vis. rewrite Hseq; auto. reflexivity.
  Qed.

  Instance proper_fun_seq_advance : Proper (@fun_eq nat R ==> fun_eq) (@advance (itree E R)).
  Proof.
    intros seq1 seq2 H. intros n m Hnm; subst. unfold advance. red in H. red in H. rewrite H. 
    reflexivity. auto.
  Qed.

  Instance proper_fun_seq_peel_tau : Proper (@fun_eq nat R ==> fun_eq) (peel_tau).
  Proof.
    intros seq1 seq2 H. intros n m Hnm; subst. unfold peel_tau. 
    do 2 red in H. rewrite H. reflexivity. auto.
  Qed.

  Instance proper_fun_seq_peel_vis {A} {e : E A} {a} : Proper (@fun_eq nat R ==> fun_eq) (peel_vis e a).
  Proof.
    intros seq1 seq2 H. intros n m Hnm; subst. unfold peel_vis. 
    do 2 red in H. rewrite H. reflexivity. auto.
  Qed.
  (* TODO: prove lemmas about how sup interacts with advance, and peel_tau,
     may require nested coinduction that mixes peel_tau and advance reasoning *)

  Lemma commute_peel_vis_peel_tau:
    forall (seq : sequence (itree E R)) (A : Type) (e : E A) (a : A),
      fun_eq (peel_vis e a (peel_tau seq)) (peel_tau (peel_vis e a seq)).
  Proof.
    intros seq A e a. red. intros n m eq. subst.
    unfold peel_tau. unfold peel_vis. remember (seq m) as t.
    clear Heqt. revert t. ginit. gcofix CIH. intros.
    destruct (observe t) eqn : Heq; symmetry in Heq; use_simpobs.
    - rewrite Heq. rewrite peel_tau_elem_ret. rewrite peel_vis_elem_ret. 
      rewrite peel_tau_elem_ret. gstep. constructor; auto.
    - rewrite Heq. rewrite peel_tau_elem_tau. rewrite peel_vis_elem_tau.
      rewrite peel_tau_elem_tau. 
      gfinal. right. eapply paco2_mon with (r := bot2); intros; try contradiction.
      enough (peel_vis_elem e a t0 ≅ peel_vis_elem e a t0). punfold H. reflexivity.
    - rewrite Heq. rewrite peel_tau_elem_vis.
      destruct (classic (A = X) ).
      + subst. repeat rewrite peel_vis_elem_vis_type_eq.
        gfinal. right. eapply paco2_mon with (r := bot2); intros; try contradiction.
        enough (peel_tau_elem (k a) ≅ peel_tau_elem (k a)). auto. reflexivity.
      + repeat rewrite peel_vis_elem_vis_type_neq; auto. rewrite peel_tau_elem_spin.
        gfinal. right. eapply paco2_mon with (r := bot2); intros; try contradiction.
        enough (@ITree.spin E R ≅ ITree.spin); auto. reflexivity.
   Qed.

  Lemma commute_peel_tau_advance : 
    forall (seq : sequence (itree E R) ), fun_eq ((peel_tau (advance seq))) (advance (peel_tau seq) ).
  Proof.
    intros seq n m Hnm. subst. unfold advance, peel_tau. reflexivity.
  Qed.

  Lemma commute_peel_vis_advance : 
    forall (seq : sequence (itree E R)) (A : Type) (e : E A) (a : A),
      fun_eq (peel_vis e a (advance seq)) (advance (peel_vis e a seq)).
  Proof.
    intros seq A e a n m Hnm. subst. unfold advance, peel_vis. 
    reflexivity.
  Qed.

  Lemma sup_peel_tau_advance_aux:
    forall RR : relation R,
      Equivalence RR ->
      forall r : itree E R -> itree E R -> Prop,
        (forall seq : sequence (itree E R),
            monotone_approx RR seq -> r (itree_approx_sup (peel_tau seq)) (itree_approx_sup seq)) ->
        forall seq : nat -> itree E R,
          monotone_approx RR seq ->
          gpaco2 (eqit_ RR true true id) (eqitC RR true true) r r (itree_approx_sup seq)
                 (itree_approx_sup (advance seq)).
  Proof.
    intros RR Heq r CIH. gcofix CIH'.
    intros seq Hmon.
    assert (strong_itree_approx RR (seq 0) (seq 1) ). apply Hmon. lia.
    pinversion H; use_simpobs; pclearbot.
    - rewrite sup_head_ret; eauto. rewrite sup_head_ret; eauto.
      gstep. constructor; auto.
    - rewrite sup_head_vis; eauto. rewrite sup_head_vis; eauto.
      gstep. constructor. intros a. red. rewrite commute_peel_vis_advance.
      gfinal. left. eapply CIH'. apply peel_vis_preserves_monotone_approx. auto.
    - rewrite (sup_head_tau seq); eauto.
      rewrite (sup_head_tau (advance seq) ); eauto.
      gstep. constructor. rewrite (commute_peel_tau_advance (advance seq) ) .
      gfinal. left. eapply CIH'. apply peel_tau_preserves_monotone_approx.
      apply advance_preserves_monotone_approx. auto.
    - rewrite (sup_head_tau seq); eauto. rewrite tau_euttge.
      gfinal. left. eapply CIH. apply advance_preserves_monotone_approx. auto.
  Qed.

  (*can I make this an euttge proof? *)
  Lemma sup_peel_tau_eutt : forall RR (HEq : Equivalence RR) (seq : sequence (itree E R) ),
      monotone_approx RR seq ->
      eqit RR true true ((itree_approx_sup (peel_tau seq ) ) ) (itree_approx_sup seq).
  Proof.
    intros RR Heq. ginit. gcofix CIH. intros seq Hmon.
    assert (strong_itree_approx RR (seq 0) (seq 1) ). apply Hmon. lia.
    pinversion H; use_simpobs; pclearbot.
    - rewrite (sup_head_ret seq); eauto. rewrite (sup_head_ret (peel_tau seq) ); eauto.
      2 : { unfold peel_tau. rewrite H0. rewrite peel_tau_elem_ret. reflexivity. }
      gstep. constructor. reflexivity.
    - rewrite (sup_head_vis seq); eauto.  rewrite (sup_head_vis (peel_tau seq) ); eauto.
      2 : { unfold peel_tau. rewrite H0. rewrite peel_tau_elem_vis. reflexivity. }
      gstep. constructor. intros a. red. 
      rewrite commute_peel_vis_peel_tau. gfinal. left. eapply CIH.
      apply peel_vis_preserves_monotone_approx. auto.
    - rewrite (sup_head_tau seq); eauto.
      destruct (observe t1 ) eqn :  Ht1; symmetry in Ht1; use_simpobs.
      + rewrite Ht1 in H0.  rewrite Ht1 in H2. pinversion H2; use_simpobs.
        subst. rewrite tau_euttge.
        rewrite sup_head_ret.
        2 : { unfold peel_tau. rewrite H0. rewrite peel_tau_elem_tau. reflexivity. }
        rewrite sup_head_ret.
        2 : { unfold peel_tau, advance. rewrite H1. rewrite H4. rewrite peel_tau_elem_tau.
              reflexivity. }
        gstep. constructor. auto.
      + rewrite sup_head_tau. 2 : { unfold peel_tau. pinversion H0; try inv CHECK; subst; eauto.
        rewrite <- Ht1. auto. use_simpobs. rewrite H4. rewrite REL. rewrite peel_tau_elem_tau.
        reflexivity. }
        gstep. constructor. rewrite (commute_peel_tau_advance seq). gfinal.
        left. eapply CIH. 
        apply advance_preserves_monotone_approx; apply peel_tau_preserves_monotone_approx; auto.
      + rewrite Ht1 in H0. rewrite Ht1 in H2. pinversion H2. inj_existT. subst.
        (* is there some way to take this tau and cancel out the peel_tau? *)
        (* if there was *)
        use_simpobs. rewrite tau_euttge. rewrite H7 in H1.
        rewrite sup_head_vis.
        2 : { unfold peel_tau. rewrite H0. rewrite peel_tau_elem_tau. reflexivity. }
        rewrite sup_head_vis.
        2 : { unfold peel_tau, advance. rewrite H1. rewrite peel_tau_elem_tau. reflexivity. }
        gstep. constructor. intros a. red. rewrite commute_peel_tau_advance.
        rewrite commute_peel_vis_advance. remember ((peel_vis e a (peel_tau seq))) as seq'.
        assert (monotone_approx RR seq').
        { subst. apply peel_vis_preserves_monotone_approx. apply peel_tau_preserves_monotone_approx. 
          auto. }
        eapply sup_peel_tau_advance_aux; eauto.
    - rewrite sup_head_tau. Unshelve. 3 : apply ITree.spin.
      2 : { unfold peel_tau. rewrite H0. rewrite H3. rewrite <- spin_cong_tau_spin.
            rewrite peel_tau_elem_spin. reflexivity. }
      rewrite (sup_head_tau seq); eauto. gstep. constructor.
      rewrite (commute_peel_tau_advance seq). gfinal. left. eapply CIH; eauto.
      apply advance_preserves_monotone_approx; apply peel_tau_preserves_monotone_approx; auto.
   Qed.


  Lemma monotone_approx_adjacent : forall RR (seq : sequence (itree E R) ) n, 
      monotone_approx RR seq -> strong_itree_approx RR (seq n) (seq (S n) ).
  Proof.
    intros. apply H. lia.
  Qed.

  Lemma sup_advance_euttge : forall RR (HEq : Equivalence RR) (seq : sequence (itree E R) ),
      monotone_approx RR seq ->
      eqit RR true false (itree_approx_sup seq) (itree_approx_sup (advance seq) ).
  Proof. 
    intros RR Heq. ginit. gcofix CIH. intros seq Hmon.
    assert (strong_itree_approx RR (seq 0) (seq 1) ). apply Hmon. lia.
    pinversion H; use_simpobs.
    - repeat (rewrite sup_head_ret; eauto). gstep. constructor; eauto.
    - repeat (rewrite sup_head_vis; eauto). gstep. constructor. intros a.
      assert (forall n, peel_vis e a (advance seq) n = advance (peel_vis e a seq) n ).
      { intros. cbv. auto. } red.
      rewrite commute_peel_vis_advance. gfinal. left. eapply CIH.
      apply peel_vis_preserves_monotone_approx. auto.
    - assert (advance seq 0 ≅ Tau t2). unfold advance. auto.
      rewrite sup_head_tau; eauto. rewrite (sup_head_tau (advance seq)); eauto.
      gstep. constructor. 
      rewrite (commute_peel_tau_advance (advance seq)). gfinal.
      left. eapply CIH. apply peel_tau_preserves_monotone_approx.
      apply advance_preserves_monotone_approx. auto.
    - rewrite sup_head_tau; eauto.
      rewrite tau_euttge. gfinal. right.
      eapply paco2_mon with (r := bot2); intros; try contradiction.
      enough (euttge RR (itree_approx_sup (peel_tau (advance seq)))(itree_approx_sup (advance seq)) ).
      auto.
      assert (eutt RR (itree_approx_sup (peel_tau (advance seq))) (itree_approx_sup (advance seq))).
      apply sup_peel_tau_eutt; auto. apply advance_preserves_monotone_approx. auto.
      (* am I crazy or should this be enough? *)
  Abort.

  Lemma sup_advance_eutt  : forall RR (HEq : Equivalence RR) (seq : sequence (itree E R) ),
      monotone_approx RR seq ->
      eutt RR (itree_approx_sup seq) (itree_approx_sup (advance seq) ).
  Proof.
    intros RR Heq. ginit. gcofix CIH. intros seq Hmon.
    assert (strong_itree_approx RR (seq 0) (seq 1) ). apply Hmon. lia.
    pinversion H; use_simpobs.
    - repeat (rewrite sup_head_ret; eauto). gstep. constructor; eauto.
    - repeat (rewrite sup_head_vis; eauto). gstep. constructor. intros a.
      assert (forall n, peel_vis e a (advance seq) n = advance (peel_vis e a seq) n ).
      { intros. cbv. auto. } red.
      rewrite commute_peel_vis_advance. gfinal. left. eapply CIH.
      apply peel_vis_preserves_monotone_approx. auto.
    - assert (advance seq 0 ≅ Tau t2). unfold advance. auto.
      rewrite sup_head_tau; eauto. rewrite (sup_head_tau (advance seq)); eauto.
      gstep. constructor. 
      rewrite (commute_peel_tau_advance (advance seq)). gfinal.
      left. eapply CIH. apply peel_tau_preserves_monotone_approx.
      apply advance_preserves_monotone_approx. auto.
    - rewrite sup_head_tau; eauto.
      rewrite tau_euttge. gfinal. right.
      eapply paco2_mon with (r := bot2); intros; try contradiction.
      apply sup_peel_tau_eutt; auto. apply advance_preserves_monotone_approx. auto.
  Qed.


  Lemma peel_tau_strong_itree_approx:
    forall (RR : relation R) (seq : sequence (itree E R)) (t : itree E R),
      (forall n : nat, strong_itree_approx RR (Tau t) (seq n)) ->
      forall (n : nat),
        strong_itree_approx RR t (peel_tau seq n).
  Proof.
    intros RR seq.
    intros t Ht n. specialize (Ht n). pinversion Ht; use_simpobs; subst.
    - unfold peel_tau. rewrite H0. rewrite peel_tau_elem_tau.
      auto.
    - rewrite H2. apply strong_itree_approx_spin_bottom.
  Qed.

  Lemma peel_vis_strong_itree_approx:
    forall (RR : relation R) (seq : sequence (itree E R)) 
      (A : Type) (e : E A) (k1 : A -> itree E R),
      (forall n : nat, strong_itree_approx RR (Vis e k1) (seq n)) ->
      forall (a : A) (n : nat),
        strong_itree_approx RR (k1 a) (peel_vis e a seq n).
  Proof.
    intros RR seq A e. intros k1 Hek1 a n.
    specialize (Hek1 n). pfold. red. unfold observe at 2. cbn.
    pinversion Hek1. inj_existT. subst.
    rewrite test_and_apply_correct_eq. specialize (H0 a). punfold H0.
  Qed.

  Lemma sup_is_upper_bound_0 : forall RR (HEq : Equivalence RR) (seq : sequence (itree E R) ) t, monotone_approx RR seq -> 
                                       (forall n, strong_itree_approx RR t (seq n)) ->  weak_itree_approx RR t (itree_approx_sup seq).
  Proof.
    intros RR HEq. ginit. gcofix CIH. intros seq t Hmon Ht.
    specialize (Ht 0) as H0. pinversion H0; pclearbot; use_simpobs.
    - rewrite H. rewrite sup_head_ret; eauto. gstep. constructor; auto.
    - rewrite H. rewrite sup_head_vis; eauto. gstep. constructor.
      intros a. red. gfinal. left. eapply CIH. apply peel_vis_preserves_monotone_approx. auto.
      setoid_rewrite H in Ht. apply peel_vis_strong_itree_approx. auto.
    - rewrite H. rewrite sup_head_tau; eauto. gstep. constructor. gfinal.
      left. eapply CIH.
      apply peel_tau_preserves_monotone_approx. apply advance_preserves_monotone_approx. auto.
      intros. apply peel_tau_strong_itree_approx. clear n. intros. unfold advance. 
      rewrite <- H. auto.
    - rewrite H. rewrite H3. gstep. constructor. gfinal. right.
      eapply paco2_mon with (r := bot2); intros; try contradiction. apply weak_itree_approx_spin_bottom.
  Qed.

  Lemma sup_is_upper_bound : forall RR (HEq : Equivalence RR) n (seq : sequence (itree E R) ), 
      monotone_approx RR seq -> weak_itree_approx RR (seq n) (itree_approx_sup seq).
  Proof.
    intros RR HEq n. induction n.
    - intros. eapply sup_is_upper_bound_0; auto. intros; apply H. lia.
    - intros. assert (seq (S n) = advance seq n ). auto. rewrite H0.
      assert (eutt RR (itree_approx_sup seq) (itree_approx_sup (advance seq) ) ). 
      apply sup_advance_eutt; auto. 
      eapply weak_itree_approx_eutt_RR_proper1; eauto.
      intros. rewrite <- H2. auto. intros. rewrite <- H2. auto.
      reflexivity. apply IHn. apply advance_preserves_monotone_approx.
      auto.
  Qed.


  Lemma sup_is_below_all_upper_bounds : forall RR (HEq : Equivalence RR) 
          (seq : sequence (itree E R) ) (tub : itree E R),
      monotone_approx RR seq ->
      (forall n, weak_itree_approx RR (seq n) tub ) -> weak_itree_approx RR (itree_approx_sup seq) tub.
  Proof.
    ginit. intros RR HEq. gcofix CIH. intros seq tub Hseq Htub.
    assert (strong_itree_approx RR (seq 0) (seq 1) ). apply Hseq. lia.
    pinversion H; use_simpobs.
    - rewrite sup_head_ret; eauto. specialize (Htub 0). rewrite H0 in Htub.
      gfinal. right. eapply paco2_mon; eauto. intros; contradiction.
    - rewrite sup_head_vis; eauto. specialize (Htub 0) as Htub'. rewrite H0 in Htub'.
      punfold Htub'. red in Htub'. cbn in *. remember (VisF e k1) as x.
      remember (observe tub) as y.
      hinduction Htub' before r; intros; inv Heqx; inj_existT; subst; pclearbot; eauto.
      + use_simpobs. rewrite Heqy. gstep. constructor. intros. red.
        gfinal. left. eapply CIH.
        apply peel_vis_preserves_monotone_approx. auto.
        intros. assert (strong_itree_approx RR (seq 0) (seq n) ). apply Hseq. lia.
        rewrite H1 in H4. unfold peel_vis. pinversion H4; inj_existT; subst; use_simpobs.
        rewrite H9. rewrite peel_vis_elem_vis_eq.
        specialize (Htub n). rewrite H9 in Htub. rewrite Heqy in Htub.
        pinversion Htub. inj_existT. subst. auto.
      + use_simpobs. rewrite Heqy. rewrite tau_euttge. eapply IHHtub'; eauto.
        setoid_rewrite Heqy in Htub. setoid_rewrite tau_eutt in Htub. auto.
    - rewrite sup_head_tau; eauto. gstep. constructor.
      gfinal. left. eapply CIH. 
      apply peel_tau_preserves_monotone_approx. apply advance_preserves_monotone_approx.
      auto.
      unfold peel_tau. intros. rewrite peel_tau_eutt.
      apply Htub.
    - rewrite sup_head_tau; eauto. gstep. constructor.
      gfinal. left. eapply CIH.
      apply peel_tau_preserves_monotone_approx. apply advance_preserves_monotone_approx.
      auto. intros. unfold peel_tau. rewrite peel_tau_eutt.
      apply Htub.
  Qed.


End ITreeApproxSup.
