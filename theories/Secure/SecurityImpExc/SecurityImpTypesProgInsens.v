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
     HeterogeneousRelations
     Events.MapDefault
     Events.State
     Events.StateFacts
     Events.Exception
     Events.ExceptionFacts
     Core.Divergence
     Dijkstra.TracesIT
     Dijkstra.ITrace
     Secure.SecureEqHalt
     Secure.SecurityImpExc.SecurityImp
     Secure.SecurityImpExc.SecurityImpHandler
     Secure.SecurityImpExc.RaiseException
     Secure.SecureEqProgInsens
     Secure.SecureEqProgInsensFacts
.

From ITree Require Import 
     Secure.SecurityImpExc.SecurityImpTypes.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Instance sense_preorder_in : Preorder := sense_preorder.

Notation label := sensitivity.

Definition labelled_equiv  :=
  SecurityImpTypes.labelled_equiv.

Instance labelled_equit_equiv {Γ l} : Equivalence (labelled_equiv Γ l).
Proof.
  constructor; unfold labelled_equiv.
  - red. red. intros; auto.
  - do 2 red. intros. symmetry; auto.
  - do 2 red. intros. rewrite H; auto.
Qed.

Definition label_pi_eqit_secure_impstate  (b1 b2 : bool) (Γ : privacy_map) (l : label) {R1 R2 : Type} (RR : R1 -> R2 -> Prop )
           (m1 : stateT map (itree (impExcE +' IOE)) R1) (m2 : stateT map (itree (impExcE +' IOE)) R2) : Prop :=
  forall σ1 σ2, labelled_equiv Γ l σ1 σ2 -> pi_eqit_secure sense_preorder priv_exc_io (product_rel (labelled_equiv Γ l) RR) b1 b2 l (m1 σ1) (m2 σ2).

Definition label_state_pi_sec_eutt {R1 R2} priv l (RR : R1 -> R2 -> Prop) m1 m2 :=
  label_pi_eqit_secure_impstate true true  priv l RR m1 m2.

Definition sem_stmt (s : stmt) := interp_imp (denote_stmt s).

Definition sem_throw_stmt (s : stmt) := interp_imp (throw_prefix (denote_stmt s) ).

Definition sem_expr (e : expr) := SecurityImpTypes.sem_expr e.

Definition state_equiv {E R} (m1 m2 : stateT map (itree E) R) := forall (σ : map), m1 σ ≈ m2 σ.

Locate pi_eqit_secure.

Global Instance proper_eutt_pi_secure_eutt  {E R1 R2 RR Label priv l} : Proper (@eutt E R1 R1 eq ==> @eutt E R2 R2 eq ==> Basics.flip Basics.impl)
                                                               (pi_eqit_secure Label priv RR true true l).
Proof.
Admitted.

Global Instance proper_eq_itree_secure_eutt  {E R1 R2 RR Label priv l} : Proper (@eq_itree E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> Basics.flip Basics.impl)
                                                               (pi_eqit_secure Label priv RR true true l).
Proof.
  repeat intro. assert (x ≈ y). rewrite H. reflexivity. 
  assert (x0 ≈ y0). rewrite H0. reflexivity. setoid_rewrite H3. rewrite H2. auto.
Qed.

Global Instance proper_state_equiv_label_state_sec_eutt {R1 R2 RR priv l} : Proper (@state_equiv _ R1 ==> @state_equiv _ R2 ==> iff) (@label_state_pi_sec_eutt R1 R2 priv l RR).
Proof.
  repeat intro. split.
  - intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1). eapply proper_eutt_pi_secure_eutt; eauto. symmetry. auto. symmetry. auto.
  - intros. intros. do 2 red in H1. do 2 red. intros. red in H0. specialize (H0 σ2). red in H.
    specialize (H σ1).  eapply proper_eutt_pi_secure_eutt; eauto.
Qed.

Context (Γ : privacy_map).

Variant secure_stmt_at_label (observer pc lexn : label) (s : stmt) : Prop :=
  | ssal_leq : (leq pc observer) -> label_state_pi_sec_eutt Γ observer eq (sem_stmt s) (sem_stmt s) -> secure_stmt_at_label observer pc lexn s
  | ssal_nleq : (~ leq pc observer) -> label_state_pi_sec_eutt Γ observer top2 (sem_stmt s) (ret tt) -> secure_stmt_at_label observer pc lexn s.



Variant secure_expr_at_label (observer protection: label ) (e : expr) : Prop :=
  | seal_leq : (leq protection observer) -> label_state_pi_sec_eutt Γ observer eq (sem_expr e) (sem_expr e) -> 
               secure_expr_at_label observer protection e
  | seal_nleq : (~leq protection observer) -> (exists n:value, label_state_pi_sec_eutt Γ observer top2 (sem_expr e) (ret n)) ->
                secure_expr_at_label observer protection e
.

Definition secure_expr l e := forall observer, secure_expr_at_label observer l e.

Definition secure_stmt pc lexn s := forall observer, secure_stmt_at_label observer pc lexn s.

Variant is_inl {A B : Type} : A + B -> Prop :=
  | is_inl_ev (a : A) : is_inl (inl a).


(* I need cases like rsense_termlexcr so for when public observers look at private 
   exceptions throw the sum type lense *)
Variant Rsense (observer lexn : label) : unit + label -> unit + label -> Prop :=
  | rsense_termlr : Rsense observer lexn (inl tt) (inl tt)
  | rsense_exclr l1 l2 : leq l1 lexn -> leq l2 lexn -> Rsense observer lexn (inr l1) (inr l2)
  | rsense_termlexcr lpriv : leq lpriv lexn -> ~ leq lpriv observer -> Rsense observer lexn (inl tt) (inr lpriv)
  | rsense_excltermr lpriv : leq lpriv lexn -> ~ leq lpriv observer -> Rsense observer lexn (inr lpriv) (inl tt)
.

Instance sym_rsense {observer lexn} : Symmetric (Rsense observer lexn).
Proof.
  red. intros. inv H; constructor; auto.
Qed.

Variant secure_throw_stmt_at_label (observer pc lexn : label) (s : stmt) : Prop :=
  | stsal_leq : leq pc observer -> label_state_pi_sec_eutt Γ observer (Rsense observer lexn )
                                                       (sem_throw_stmt s) (sem_throw_stmt s) -> secure_throw_stmt_at_label observer pc lexn s
  | stsal_nleq : (~ leq pc observer) -> label_state_pi_sec_eutt Γ observer (fun sum _ => is_inl sum ) 
                                                            (sem_throw_stmt s) (ret tt ) ->  secure_throw_stmt_at_label observer pc lexn s
  .
(*maybe I can simplify the first return relation, I think some of those conditions are implied by a reasonable secure_stmt def 
  really what throw_stmt is needed for is the observation of the final state before an exception
  maybe experiment with the try catch and seq cases, see what is really neededs
  Intuitively if the exception is visible the labels must be the same (that is certainly true but may be stronger than needed)
  maybe can get away with just each label is less than lexn1
  
*)
Definition secure_throw_stmt pc lexn s := forall observer, secure_throw_stmt_at_label observer pc lexn s.

Lemma pi_sem_stmt_ret_aux:
  forall (s2 : stmt) (observer : label) (σ3 σ4 : map),
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        pi_eqit_secure sense_preorder priv_exc_io (product_rel (labelled_equiv Γ observer) top2)
                       true true observer (sem_stmt s2 σ1) (Ret (σ2, tt))) ->
    labelled_equiv Γ observer σ3 σ4 ->
    pi_eqit_secure sense_preorder priv_exc_io (product_rel (labelled_equiv Γ observer) eq) true
                   true observer (interp_state handle_imp (denote_stmt s2) σ3)
                   (interp_state handle_imp (denote_stmt s2) σ4).
Proof.
  intros s2 observer σ3 σ4 Hσ Hs2.
  eapply pi_eqit_secure_RR_imp with (RR1 := rcompose  (product_rel (labelled_equiv Γ observer) (@top2 unit unit)) (Basics.flip (product_rel (labelled_equiv Γ observer) top2))).
  { intros [σ5 [] ] [σ6 [] ] Hr. inv Hr. inv REL1. inv REL2. split; auto.
    destruct r2 as [σ7 [] ]. etransitivity; eauto. symmetry. auto.
  }
  eapply pi_eqit_secure_trans_ret; eauto. 
  apply pi_eqit_secure_sym. apply Hσ. reflexivity.
Qed.

Lemma pi_sem_throw_stmt_ret_aux:
  forall (lexn : label) (s2 : stmt) (observer : label) (σ3 σ4 : map),
    (forall σ1 σ2 : map,
        labelled_equiv Γ observer σ1 σ2 ->
        pi_eqit_secure sense_preorder priv_exc_io
                       (product_rel (labelled_equiv Γ observer)
                                    (fun (sum : unit + label) (_ : unit) => is_inl sum)) true true observer
                       (sem_throw_stmt s2 σ1) (Ret (σ2, tt))) ->
    labelled_equiv Γ observer σ3 σ4 ->
    pi_eqit_secure sense_preorder priv_exc_io
                   (product_rel (labelled_equiv Γ observer) (Rsense observer lexn)) true true
                   observer (interp_state handle_imp (throw_prefix (denote_stmt s2)) σ3)
                   (interp_state handle_imp (throw_prefix (denote_stmt s2)) σ4).
Proof.
  intros lexn s2 observer σ3 σ4 Hσ H4.
  set (product_rel (labelled_equiv Γ observer) (fun (sum : unit + label) ( _ : unit) => is_inl sum ) ) as HR.
  eapply pi_eqit_secure_RR_imp with (RR1 := rcompose HR (Basics.flip HR) ).
  { unfold HR. intros [σ5 r1] [σ6 r2] Hr. inv Hr. inv REL1. inv REL2.
    inv H0. inv H2. cbn in H3. cbn in H0. subst.
    destruct r0 as [σ7 [] ]. split. etransitivity; eauto. symmetry. auto.
    cbn. destruct a. destruct a0. constructor. }
  eapply pi_eqit_secure_trans_ret; eauto. apply pi_eqit_secure_sym.
  eapply Hσ. reflexivity.
Qed.

Lemma seq_well_typed_correct pc lexn1 lexn2 s1 s2 :
  secure_stmt pc lexn1 s1 -> secure_stmt (join pc lexn1) lexn2 s2 ->
  secure_stmt pc (join lexn1 lexn2) (Seq s1 s2).
Proof.
  intros Hs1 Hs2 observer.
  specialize (Hs1 observer). inv Hs1.
  - left; auto. unfold sem_stmt, interp_imp.
    cbn. do 2 red. intros σ1 σ2 Hσ. setoid_rewrite interp_state_bind.
    eapply pi_eqit_secure_bind; eauto. intros [σ3 [] ] [σ4 [] ] [Hσ' _ ].
    specialize (Hs2 observer). inv Hs2; eauto. cbn. do 2 red in H2. cbn in H2.
    eapply pi_sem_stmt_ret_aux; eauto.
  - right; auto. cbn in H0. unfold sem_stmt, interp_imp. cbn.
    do 2 red. intros σ1 σ2 Hσ.
    setoid_rewrite <- bind_ret_r with (s := Ret (σ2, tt) ).
    setoid_rewrite interp_state_bind.
    eapply pi_eqit_secure_bind; eauto.
    intros [σ3 [] ] [σ4 [] ] [Hσ' _ ].
    specialize (Hs2 observer). inv Hs2; eauto.
    + exfalso. apply H. eapply leq_sense_trans; eauto.
      apply leq_sense_join_l.
    + cbn in H2. eauto.
Qed.

Lemma seq_well_typed_correct' pc lexn1 lexn2 s1 s2 :
  secure_throw_stmt pc lexn1 s1 -> secure_throw_stmt (join pc lexn1) lexn2 s2 ->
  secure_throw_stmt pc (join lexn1 lexn2) (Seq s1 s2).
Proof.
  intros Hs1 Hs2 observer.
  specialize (Hs1 observer). inv Hs1.
  - left; auto. unfold sem_throw_stmt, interp_imp. cbn. do 2 red.
    intros σ1 σ2 Hσ. setoid_rewrite throw_prefix_bind.
    setoid_rewrite interp_state_bind.
    eapply pi_eqit_secure_bind; eauto.
    intros [σ3 r1] [σ4 r2] [Hσ' Hr]. inv Hr.
    + specialize (Hs2 observer). inv Hs2; eauto.
      * cbn.
        eapply pi_eqit_secure_RR_imp; try eapply H4; eauto.
        intros. destruct H5. split; auto. inv H6; constructor; auto;
        try eapply leq_sense_trans; eauto; apply leq_sense_join_r.
      * cbn in H4. cbn.
        do 2 red in H4. cbn in Hσ'.
        eapply pi_sem_throw_stmt_ret_aux; eauto.
    + setoid_rewrite interp_state_ret. apply pi_eqit_secure_ret.
      split; auto; constructor; eapply leq_sense_trans; eauto.
      all : apply leq_sense_join_l.
    + specialize (Hs2 observer). inv Hs2; eauto.
      * exfalso. apply H2. eapply leq_sense_trans; eauto.
        eapply leq_sense_trans; eauto. apply leq_sense_join_r.
      * setoid_rewrite interp_state_ret. cbn.
        cbn in H6. do 2 red in H6.
        match goal with 
      |- pi_eqit_secure _ _ _ _ _ _ _ ?t => assert (t ≈ ITree.bind (Ret (σ4,tt) ) (fun '(σ',x) => Ret (σ', inr lpriv) )) end.
        rewrite bind_ret_l. reflexivity.
        rewrite H7. rewrite <- bind_ret_r.
        eapply pi_eqit_secure_bind; eauto.
        intros [σ5 r3] [σ6 r4] [Hσ'' Hr']; inv Hr'.
        cbn in H8. rewrite <- H8. destruct a. apply pi_eqit_secure_ret.
        split; auto. constructor; auto. eapply leq_sense_trans; eauto.
        apply leq_sense_join_l.
    + specialize (Hs2 observer). inv Hs2; eauto.
      * exfalso. apply H2. eapply leq_sense_trans; eauto.
        eapply leq_sense_trans; eauto. apply leq_sense_join_r.
      * setoid_rewrite interp_state_ret. cbn.
        cbn in H6.
        match goal with
        |- pi_eqit_secure _ _ _ _ _ _ ?t _ => assert (t ≈ ITree.bind (Ret (σ3,tt) ) (fun '(σ',x) => Ret (σ', inr lpriv) )) end.
        rewrite bind_ret_l. reflexivity. rewrite H7.
        setoid_rewrite <- bind_ret_r at 4.
        apply pi_eqit_secure_sym. symmetry in Hσ'. eapply pi_eqit_secure_bind; eauto.
        intros [σ5 r3] [σ6 [] ] [Hσ'' Hr']; inv Hr'.
        destruct a. cbn in H8. subst. apply pi_eqit_secure_ret.
        split; auto. symmetry. auto. constructor; auto.
        eapply leq_sense_trans; eauto. apply leq_sense_join_l.
  - right; auto. intros σ1 σ2 Hσ. unfold sem_throw_stmt, interp_imp.
    cbn. setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind.
    cbn in H0. rewrite <- bind_ret_r with (s := Ret (σ2, tt) ).
    eapply pi_eqit_secure_bind; eauto. intros [σ3 r1] [σ4 [] ] [Hσ' Hr]. inv Hr.
    destruct a. cbn. cbn in H1. subst.
    specialize (Hs2 observer). inv Hs2.
    + exfalso. apply H. eapply leq_sense_trans; eauto. apply leq_sense_join_l.
    + cbn in H2. eauto.
Qed.

Lemma try_catch_well_typed_correct pc lexn1 lexn2 s1 s2 :
  secure_stmt pc lexn1 s1 -> secure_throw_stmt pc lexn1 s1 ->
  secure_stmt (join pc lexn1) lexn2 s2 ->
  secure_stmt pc lexn2 (TryCatch s1 s2).
Proof.
  intros Hs1 Hs1t Hs2 observer.
  specialize (Hs1 observer). specialize (Hs1t observer).
  inv Hs1; inv Hs1t; try contradiction.
  - left; auto. unfold sem_stmt, interp_imp. do 2 red. intros σ1 σ2 Hσ.
    cbn. setoid_rewrite try_catch_to_throw_prefix.
    setoid_rewrite interp_state_bind. eapply pi_eqit_secure_bind; eauto.
    intros [σ3 r1 ] [σ4 r2 ] [Hσ' Hr] ; inv Hr; cbn.
    + setoid_rewrite interp_state_ret. apply pi_eqit_secure_ret. auto.
    + specialize (Hs2 observer). inv Hs2; eauto. do 2 red in H8.
      cbn in H8. eapply pi_sem_stmt_ret_aux; eauto.
    + specialize (Hs2 observer). inv Hs2. 
      * exfalso. apply H4. eapply leq_sense_trans; eauto.
        eapply leq_sense_trans. apply leq_sense_join_r. eauto.
      * apply pi_eqit_secure_sym. do 2 red in H8.
        apply pi_eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2).
        { intros [? [] ] [? [] ] ? . inv H9. split; auto. symmetry. auto. }
        cbn in H8. setoid_rewrite interp_state_ret. eapply H8. symmetry. auto.
    + specialize (Hs2 observer). inv Hs2. 
      * exfalso. apply H4. eapply leq_sense_trans; eauto.
        eapply leq_sense_trans. apply leq_sense_join_r. eauto.
      * do 2 red in H8.
        apply pi_eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2).
        { intros [? [] ] [? [] ] ? . inv H9. split; auto. }
        cbn in H8. setoid_rewrite interp_state_ret. eapply H8. auto. 
  - right; auto. unfold sem_stmt, interp_imp. do 2 red. intros σ1 σ2 Hσ.
    cbn. setoid_rewrite try_catch_to_throw_prefix.
    (* rewrite the ret into a trivial bind *)
    match goal with 
      |- pi_eqit_secure _ _ _ _ _ _ _ ?t => assert (t ≈ ITree.bind (Ret (σ2,tt) ) (fun x => Ret x)) end.
    rewrite bind_ret_r. reflexivity. rewrite H3.
    setoid_rewrite interp_state_bind. cbn in H2.
    eapply pi_eqit_secure_bind; eauto.
    intros [σ3 r1] [σ4 [] ] [Hσ' Hr]; inv Hr.
    destruct a. simpl. setoid_rewrite interp_state_ret.
    apply pi_eqit_secure_ret. split; cbv; auto.
Qed.

Lemma try_catch_well_typed_correct' pc lexn1 lexn2 s1 s2 :
  secure_stmt pc lexn1 s1 -> secure_throw_stmt pc lexn1 s1 ->
  secure_throw_stmt (join pc lexn1) lexn2 s2 ->
  secure_throw_stmt pc lexn2 (TryCatch s1 s2).
Proof.
  intros Hs1 Hs1t Hs2 observer. specialize (Hs1 observer).
  specialize (Hs1t observer). inv Hs1; inv Hs1t; try contradiction.
  - left; auto. unfold sem_throw_stmt, interp_imp. cbn. do 2 red.
    intros σ1 σ2 Hσ. rewrite throw_prefix_of_try_catch.
    setoid_rewrite try_catch_to_throw_prefix.
    setoid_rewrite throw_prefix_bind.
    repeat setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
    eapply pi_eqit_secure_bind; eauto.
    intros [σ3 r1] [σ4 r2] [Hσ' Hr]; inv Hr; cbn;
      try setoid_rewrite throw_prefix_ret; try setoid_rewrite interp_state_ret;
        try setoid_rewrite bind_ret_l; cbn.
    + setoid_rewrite interp_state_ret. apply pi_eqit_secure_ret.
      split; auto. constructor.
    + specialize (Hs2 observer). inv Hs2; eauto.
      eapply pi_sem_throw_stmt_ret_aux; eauto. 
    + specialize (Hs2 observer). inv Hs2; eauto.
      * exfalso. apply H4. eapply leq_sense_trans; eauto.
        eapply leq_sense_trans; eauto. apply leq_sense_join_r.
      * apply pi_eqit_secure_sym. cbn in H8. do 2 red in H8.
        setoid_rewrite interp_state_ret.
        match goal with
        |- pi_eqit_secure _ _ _ _ _ _ _ ?t => assert (t ≈ ITree.bind (Ret (σ3, tt) ) (fun '(σ, x) => Ret (σ, inl x) ) ) end.
        rewrite bind_ret_l. reflexivity. rewrite H9.
        rewrite <- bind_ret_r. symmetry in Hσ'. eapply pi_eqit_secure_bind; eauto.
        intros [σ5 r] [σ6 [] ] Hr. inv Hr. inv H11. destruct a. cbn in H12. subst.
        apply pi_eqit_secure_ret. split. symmetry; auto. constructor.
    + specialize (Hs2 observer). inv Hs2; eauto.
      * exfalso. apply H4. eapply leq_sense_trans; eauto.
        eapply leq_sense_trans; eauto. apply leq_sense_join_r.
      * setoid_rewrite interp_state_ret.
         match goal with
        |- pi_eqit_secure _ _ _ _ _ _ _ ?t => assert (t ≈ ITree.bind (Ret (σ4, tt) ) (fun '(σ, x) => Ret (σ, inl x) ) ) end.
        rewrite bind_ret_l. reflexivity. rewrite H9. cbn in H8.
        rewrite <- bind_ret_r. eapply pi_eqit_secure_bind; eauto.
        intros [σ5 r] [σ6 [] ] Hr. inv Hr. inv H11. destruct a. cbn in H12. subst.
        apply pi_eqit_secure_ret. split; auto. constructor.
  - right; auto. unfold sem_throw_stmt, interp_imp. cbn. do 2 red.
    intros σ1 σ2 Hσ. rewrite throw_prefix_of_try_catch.
    rewrite try_catch_to_throw_prefix.
    rewrite throw_prefix_bind. repeat rewrite interp_state_bind.
    rewrite bind_bind.
    setoid_rewrite <- bind_ret_r with (s := Ret (σ2, tt) ).
    cbn in H2.
    eapply pi_eqit_secure_bind; eauto.
    intros [σ3 r1] [σ4 r2] [Hσ' Hr]; inv Hr.
    rewrite throw_prefix_ret, interp_state_ret, bind_ret_l. cbn.
    rewrite interp_state_ret. apply pi_eqit_secure_ret. split; auto.
    constructor.
Qed.

Lemma pi_eqit_secure_while_ret_aux:
  forall (e : expr) (s : stmt) (observer : label),
    label_state_pi_sec_eutt Γ observer top2 (sem_stmt s) (ret tt) ->
    forall σ1 σ2 : map,
      labelled_equiv Γ observer σ1 σ2 ->
      pi_eqit_secure sense_preorder priv_exc_io
                     (product_rel (labelled_equiv Γ observer) top2) true true
                     observer (sem_stmt (While e s) σ1) (Ret (σ2, tt)).
Proof.
  intros e s observer H0 σ1 σ2 H3.
  unfold sem_stmt, interp_imp.
  cbn. specialize (@interp_state_iter') as Hisi. red in Hisi. setoid_rewrite Hisi.
  eapply pi_eqit_secure_iter_ret with (Rinv := product_rel (labelled_equiv Γ observer) eq ).
  2 : split; auto.
  intros [σ3 [] ] [Hσ3 _ ]. cbn.
  setoid_rewrite interp_state_bind. rewrite bind_bind.
  specialize (expr_only_ret' e σ3) as [n Hn]. setoid_rewrite Hn.
  rewrite bind_ret_l. destruct n.
  + cbn. rewrite interp_state_ret, bind_ret_l. cbn. apply pi_eqit_secure_ret.
    constructor. split; auto. cbv. auto.
  + cbn. rewrite interp_state_bind. rewrite bind_bind.
    rewrite <- bind_ret_r with (s0 := Ret (σ2, tt) ). 
    cbn in H0.
    eapply pi_eqit_secure_bind; eauto.
    intros [σ4 [] ] [σ5 [] ] [Hσ' _ ]. rewrite interp_state_ret, bind_ret_l. cbn.
    apply pi_eqit_secure_ret. constructor. split; auto.
Qed.

Lemma while_typed_correct e le pc lexn s :
  secure_expr le e -> secure_stmt (join pc le) lexn s -> secure_stmt pc lexn (While e s).
Proof.
  intros He Hs observer.
  specialize (He observer). specialize (Hs observer).
  inv Hs; inv He.
  - left. eapply leq_sense_trans; try apply H. apply leq_sense_join_l.
    do 2 red. intros σ1 σ2 Hσ. unfold sem_stmt, interp_imp. cbn.
    specialize (@interp_state_iter') as Hisi. red in Hisi. setoid_rewrite Hisi.
    apply secure_eqit_iter with (RA := product_rel (labelled_equiv Γ observer) eq );
      auto.
    clear σ1 σ2 Hσ. intros [σ1 [] ] [σ2 [] ] [Hσ _ ].
    cbn. setoid_rewrite interp_state_bind. repeat rewrite bind_bind.
    eapply pi_eqit_secure_bind; eauto.
    intros [σ3 v1] [σ4 v2] [Hσ' Hv]; cbn in Hv; subst. cbn.
    destruct v2.
    + setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l.
      cbn. apply pi_eqit_secure_ret. constructor. auto.
    + setoid_rewrite interp_state_bind. setoid_rewrite bind_bind. 
      eapply pi_eqit_secure_bind; eauto.
      intros [σ5 [] ] [σ6 [] ] [Hσ'' _ ]. setoid_rewrite interp_state_ret.
      setoid_rewrite bind_ret_l. cbn. apply pi_eqit_secure_ret.
      constructor; auto.
  - exfalso. apply H1. eapply leq_sense_trans; eauto. apply leq_sense_join_r.
  - right. intro. apply H. 
    (* come up with a lemma for this *)
    destruct pc; destruct le; destruct observer; cbv; auto.
    do 2 red. intros. cbn. eapply pi_eqit_secure_while_ret_aux; eauto.
  - case_leq pc observer.
    + left; auto. intros σ1 σ2 Hσ.
      specialize (pi_eqit_secure_while_ret_aux e s observer H0) as Hwhile.
      eapply pi_sem_stmt_ret_aux; eauto.
    + right; auto. cbn. do 2 red. intros. eapply pi_eqit_secure_while_ret_aux; eauto.
Qed.


Lemma while_typed_correct' e le pc lexn s : 
  secure_expr le e -> secure_throw_stmt (join pc le) lexn s -> secure_throw_stmt pc lexn (While e s).
Proof.
  intros He Hs observer.
  specialize (He observer). specialize (Hs observer).
  inv Hs; inv He.
  - left. eapply leq_sense_trans; try apply H. apply leq_sense_join_l.
    do 2 red. intros σ1 σ2 Hσ. unfold sem_throw_stmt, interp_imp. cbn.
    setoid_rewrite throw_prefix_iter.
    specialize (@interp_state_iter') as Hisi. red in Hisi. setoid_rewrite Hisi.
    eapply secure_eqit_iter with (RA := product_rel (labelled_equiv Γ observer) eq ); auto.
    intros [σ3 [] ] [σ4 [] ] [Hσ' _ ]. cbn. setoid_rewrite throw_prefix_bind.
    repeat setoid_rewrite interp_state_bind. repeat rewrite bind_bind.
    setoid_rewrite throw_prefix_denote_expr. setoid_rewrite interp_state_bind.
    setoid_rewrite bind_bind.
    eapply pi_eqit_secure_bind; eauto. intros [σ5 v1] [σ6 v2] [Hσ'' Hv]; cbn in Hv; subst.
    setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    destruct v2; cbn.
    + setoid_rewrite throw_prefix_ret. tau_steps.
      apply pi_eqit_secure_ret. constructor. split; auto. constructor.
    + setoid_rewrite throw_prefix_bind. setoid_rewrite interp_state_bind. 
      setoid_rewrite bind_bind.
      eapply pi_eqit_secure_bind; eauto.
      intros [σ7 r1] [σ8 r2] [Hσ''' Hr]. cbn in Hr. inv Hr.
      * setoid_rewrite throw_prefix_ret. tau_steps.
        apply pi_eqit_secure_ret. constructor. split; auto.
      * tau_steps. apply pi_eqit_secure_ret. constructor. split; auto.
        constructor; auto.
      * tau_steps. cbn in Hσ'. cbn in Hσ''. cbn in Hσ'''. admit.
      * tau_steps. admit.

  - exfalso. apply H1. eapply leq_sense_trans; eauto. apply leq_sense_join_r.
  - right. intro. apply H.
    destruct pc; destruct le; destruct observer; cbv; auto.
    (* need a lemma to relate iter to ret *) admit.
Abort. 

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


(* rework this definition to have only public exceptions*)
Inductive well_typed_stmt : sensitivity -> sensitivity -> stmt -> Prop :=
  | wts_manual pc lexn s : secure_stmt pc lexn s /\ secure_throw_stmt pc lexn s -> well_typed_stmt pc lexn s
  | wts_skip pc : well_typed_stmt pc Public Skip
  | wts_seq pc lexn1 lexn2 s1 s2 : well_typed_stmt pc lexn1 s1 -> well_typed_stmt (join pc lexn1) lexn2 s2 ->
                                   well_typed_stmt pc (join lexn1 lexn2) (Seq s1 s2)
  | wts_assign pc l x e : well_typed_expr l e -> leq (join l pc) (Γ x) ->
                          well_typed_stmt pc Public (Assign x e)
  | wts_print pc le lp e : well_typed_expr le e -> leq (join le pc) lp ->
                           well_typed_stmt pc Public (Output lp e)
  | wts_if pc le e lexn1 lexn2 s1 s2 : well_typed_expr le e -> well_typed_stmt (join pc le) lexn1 s1 -> well_typed_stmt (join pc le) lexn2 s2 ->
                                       well_typed_stmt pc (join lexn1 lexn2) (If e s1 s2)
  | wts_while e le pc lexn s : well_typed_expr le e -> well_typed_stmt (join pc le) lexn s ->
                         well_typed_stmt pc lexn (While e s)
  | wts_raise pc lexn : leq pc lexn -> well_typed_stmt pc lexn (Raise lexn)
  | wts_try pc lexn1 lexn2 s1 s2 : well_typed_stmt pc lexn1 s1 -> well_typed_stmt (join pc lexn1) lexn2 s2 ->
                                   well_typed_stmt pc lexn2 (TryCatch s1 s2)
.
