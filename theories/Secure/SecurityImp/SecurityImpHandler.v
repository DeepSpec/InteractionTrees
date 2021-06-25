From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

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
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.SecurityImp.SecurityImp
     Secure.StrongBisimProper
.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.

Definition sense_preorder : Preorder := {|
  L := sensitivity;
  leq := fun s1 s2 =>
           match (s1,s2) with
           | (Private, Public) => False
           | _ => True end |}.

Definition priv_io (A : Type) (e : IOE A) :=
  match e with
  | LabelledPrint s _ => s end.

Definition product_rel {R1 R2 S1 S2} (RR1: R1 -> S1 -> Prop) (RR2 : R2 -> S2 -> Prop)
           (p1 : R1 * R2) (p2 : S1 * S2) : Prop :=
  RR1 (fst p1) (fst p2) /\ RR2 (snd p1) (snd p2).

Definition low_map_equiv (priv : privacy_map) (s1 s2 : map) : Prop :=
  forall x, priv x = Public -> s1 x = s2 x.

Lemma low_equiv_update_public : forall (x : var) (v : value) (priv_map : privacy_map) (s1 s2 : map),
        priv_map x = Public ->  low_map_equiv priv_map s1 s2 ->
        low_map_equiv priv_map (update x v s1) (update x v s2).
Proof.
  intros. red in H0. red. intros. unfold update.
  destruct (x =? x0) eqn : Heq; auto.
Qed.

Lemma low_equiv_update_private_l : forall (x : var) (v : value) (priv_map : privacy_map) (s1 s2 : map),
    priv_map x = Private -> low_map_equiv priv_map s1 s2 ->
    low_map_equiv priv_map (update x v s1) s2.
Proof.
  intros. red in H0. red. intros. unfold update.
  destruct (x =? x0) eqn : Heq; auto.
  apply eqb_eq in Heq. subst. rewrite H in H1. discriminate.
Qed.

Lemma low_equiv_update_private_r : forall (x : var) (v : value) (priv_map : privacy_map) (s1 s2 : map),
    priv_map x = Private -> low_map_equiv priv_map s1 s2 ->
    low_map_equiv priv_map s1 (update x v s2).
Proof.
  intros. red in H0. red. intros. unfold update.
  destruct (x =? x0) eqn : Heq; auto.
  apply eqb_eq in Heq. subst. rewrite H in H1. discriminate.
Qed.


Definition low_eqit_secure_impstate  (b1 b2 : bool) (priv : var -> sensitivity) {R1 R2 : Type} (RR : R1 -> R2 -> Prop )
           (m1 : stateT map (itree IOE) R1) (m2 : stateT map (itree IOE) R2) : Prop :=
  forall s1 s2, low_map_equiv priv s1 s2 -> eqit_secure sense_preorder priv_io (product_rel (low_map_equiv priv) RR) b1 b2 Public (m1 s1) (m2 s2).

Definition handle_case {E1 E2 : Type -> Type} {M : Type -> Type} (hl : E1 ~> M) (hr : E2 ~> M) : (E1 +' E2) ~> M :=
  fun _ e => match e with
          | inl1 el => hl _ el
          | inr1 er => hr _ er end.

Definition handle_state_io : forall A, (stateE +' IOE) A -> stateT map (itree IOE) A :=
  fun _ e => match e with
          | inl1 el => handleState _ el
          | inr1 er => fun s => r <- ITree.trigger er;; Ret (s, r) end.

Definition interp_imp {R} (t : itree (stateE +' IOE) R ) : stateT map (itree IOE) R :=
  interp_state handle_state_io t.

Hint Unfold interp_imp.
Hint Unfold handle_state_io.
Hint Unfold product_rel.

Ltac use_simpobs :=
  repeat match goal with
         | H : TauF _ = observe ?t |- _ => apply simpobs in H
         | H : RetF _ = observe ?t |- _ => apply simpobs in H
         | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
  end.

Lemma interp_eqit_secure_imp : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (priv_map : privacy_map)
                                 (t1 : itree (stateE +' IOE) R1 )
                                 (t2 : itree (stateE +' IOE) R2),
    eqit_secure sense_preorder (priv_imp priv_map) RR true true Public t1 t2 ->
    low_eqit_secure_impstate true true priv_map RR (interp_imp t1 )  (interp_imp t2).
Proof.
  intros R1 R2 RR priv_map. pcofix CIH. intros t1 t2 Ht s1 s2 Hs.
  punfold Ht. red in Ht. remember (observe t1) as ot1. remember (observe t2) as ot2.
  unfold interp_imp.
  hinduction Ht before r; intros.
  - use_simpobs.
    rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_ret.
    pfold. constructor. auto.
  - use_simpobs.
    rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_tau.
    pfold. constructor. right. pclearbot. apply CIH; auto.
  - use_simpobs. rewrite Heqot1. rewrite interp_state_tau.
    pfold. constructor; auto. pstep_reverse.
  - use_simpobs. rewrite Heqot2. rewrite interp_state_tau.
    pfold. constructor; auto. pstep_reverse.
  - pclearbot. use_simpobs.
    rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    destruct e; cbn.
    + destruct s; cbn.
      * repeat rewrite bind_ret_l. pfold. constructor. right. cbn. eapply CIH; auto.
        cbv in SECCHECK. unfold get. red in Hs. destruct (priv_map x) eqn : Hx; try contradiction.
        apply Hs in Hx. rewrite Hx. apply H.
      * repeat rewrite bind_ret_l. pfold. constructor. right. cbv in SECCHECK. cbn.
        destruct (priv_map x) eqn : Hx; try contradiction.
        eapply CIH; auto. apply H. apply low_equiv_update_public; auto.
    + rewrite bind_bind. rewrite bind_bind.  repeat rewrite bind_trigger. destruct i.
      cbv in SECCHECK. destruct s; try contradiction. pfold. constructor; auto.
      left. repeat rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; auto. apply H.
  - pclearbot. use_simpobs. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_tau. rewrite interp_state_vis. destruct e; try destruct s.
    + cbn. rewrite bind_ret_l. pfold. cbn. constructor. right. apply CIH; auto. apply H.
    + cbn. rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; auto. apply H.
      apply low_equiv_update_private_l; auto. cbv in SECCHECK.
      destruct (priv_map x); auto; contradiction.
    + cbn. cbv in SECCHECK. destruct i. destruct s; try contradiction. rewrite bind_bind.
      rewrite bind_trigger. setoid_rewrite bind_ret_l. pfold. red. cbn.
      rewrite itree_eta'. unpriv_ind. cbn. constructor. right. apply CIH; auto.
      apply H.
  - pclearbot. use_simpobs. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_tau. rewrite interp_state_vis. destruct e; try destruct s.
    + cbn. rewrite bind_ret_l. pfold. cbn. constructor. right. apply CIH; auto. apply H.
    + cbn. rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; auto. apply H.
      apply low_equiv_update_private_r; auto. cbv in SECCHECK.
      destruct (priv_map x); auto; contradiction.
    + cbn. cbv in SECCHECK. destruct i. destruct s; try contradiction. rewrite bind_bind.
      rewrite bind_trigger. setoid_rewrite bind_ret_l. pfold. red. cbn.
      rewrite itree_eta' at 1. unpriv_ind. cbn. constructor. right. apply CIH; auto.
      apply H.
  - use_simpobs. rewrite Heqot1. rewrite Heqot2. pclearbot.
    rewrite interp_state_vis. destruct e1; try destruct s; destruct e2; try destruct s; try destruct i; cbn;
                                try (repeat rewrite interp_state_vis; cbn; repeat rewrite bind_ret_l; cbn).
    + pfold. constructor. right. apply CIH; auto. apply H.
    + pfold. constructor. right. apply CIH; auto. apply H.
      apply low_equiv_update_private_r; auto. cbv in SECCHECK2.
      destruct (priv_map x0); auto; contradiction.
    + rewrite bind_bind. rewrite bind_trigger.  cbv in SECCHECK2. destruct s; try contradiction.
      cbn. setoid_rewrite bind_ret_l. pfold. red. cbn. rewrite itree_eta' at 1.
      unpriv_ind. cbn. constructor. right. apply CIH; auto. apply H.
    + pfold. constructor. right. apply CIH. apply H.
      apply low_equiv_update_private_l; auto. cbv in SECCHECK1.
      destruct (priv_map x); auto; contradiction.
    + pfold. constructor. right. apply CIH. apply H.
      apply low_equiv_update_private_l; auto. cbv in SECCHECK1.
      destruct (priv_map x); auto; contradiction.
      apply low_equiv_update_private_r; auto. cbv in SECCHECK2.
      destruct (priv_map x0); auto; contradiction.
    + rewrite bind_bind. rewrite bind_trigger. cbv in SECCHECK2. destruct s; try contradiction.
      setoid_rewrite bind_ret_l.
      pfold. red. cbn. rewrite itree_eta' at 1. unpriv_ind. cbn. constructor.
      right. apply CIH; try apply H.
      apply low_equiv_update_private_l; auto. cbv in SECCHECK1.
      destruct (priv_map x); auto; contradiction.
    + rewrite bind_bind. rewrite bind_trigger. cbv in SECCHECK1. destruct s; try contradiction.
      setoid_rewrite bind_ret_l. pfold. red. cbn. rewrite itree_eta'. unpriv_ind.
      cbn. constructor. right. apply CIH; auto. apply H.
    + rewrite bind_bind. rewrite bind_trigger. setoid_rewrite bind_ret_l. pfold. red. cbn.
      rewrite itree_eta'. unpriv_ind. cbn. constructor. right. apply CIH. apply H.
      apply low_equiv_update_private_r; auto. cbv in SECCHECK2.
      destruct (priv_map x); auto; contradiction.
    + repeat rewrite bind_bind. repeat rewrite bind_trigger. repeat setoid_rewrite bind_ret_l.
      cbn. pfold. red. cbn. destruct i0. unpriv_co.
      left. pfold. constructor. right. apply CIH; auto. apply H.
  - use_simpobs. rewrite Heqot1. rewrite interp_state_vis.
    destruct e; try destruct s; cbn.
    + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse. eapply H0; eauto.
      apply low_equiv_update_private_l; auto. cbv in SECCHECK.
      destruct (priv_map x); auto; contradiction.
    + rewrite bind_bind. rewrite bind_trigger. destruct i. destruct s.
      cbv in SECCHECK; try contradiction. setoid_rewrite bind_ret_l.
      cbn. pfold. red. cbn. unpriv_ind. constructor; auto. pstep_reverse.
  - use_simpobs. rewrite Heqot2. rewrite interp_state_vis.
    destruct e; try destruct s; cbn.
    + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse.
    + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse. eapply H0; eauto.
      apply low_equiv_update_private_r; auto. cbv in SECCHECK.
      destruct (priv_map x); auto; contradiction.
    + rewrite bind_bind. rewrite bind_trigger. destruct i. destruct s.
      cbv in SECCHECK; try contradiction. setoid_rewrite bind_ret_l.
      cbn. pfold. red. cbn. unpriv_ind. constructor; auto. pstep_reverse.
  -  destruct e; try destruct s; try destruct i; exfalso; inv SIZECHECK;  apply H0; auto; apply tt.
  -  destruct e; try destruct s; try destruct i; exfalso; inv SIZECHECK;  apply H0; auto; apply tt.
  -  destruct e1; try destruct s; try destruct i; exfalso; inv SIZECHECK;  apply H0; auto; apply tt.
  -  destruct e2; try destruct s; try destruct i; exfalso; inv SIZECHECK;  apply H0; auto; apply tt.
Qed.

Section GeneralStateHandler.

Context (S : Type).
Context (RS : S -> S -> Prop).
Context (RS_PER: PER RS).

Context (E1 E2 : Type -> Type).

Context (handler : E1 ~> stateT S (itree E2) ).

Context (Label : Preorder).
Context (priv1 : forall A, E1 A -> L).
Context (priv2 : forall A, E2 A -> L).
Context (l : L).

Definition state_eqit_secure {R1 R2 : Type} (b1 b2 : bool) (RR : R1 -> R2 -> Prop)
           (m1 : stateT S (itree E2) R1) (m2 : stateT S (itree E2) R2) :=
  forall s1 s2, RS s1 s2 -> eqit_secure Label priv2 (product_rel RS RR) b1 b2 l (m1 s1) (m2 s2).

Definition top2 {R1 R2} (r1 : R1) (r2 : R2) : Prop := True.

Inductive terminates {A} (s1 : S) (P : E2 A -> Prop) : itree E2 (S * A) -> Prop :=
| terminates_ret : forall r (s2 : S), RS s1 s2 -> terminates s1 P (Ret (s2, r))
| terminates_tau : forall t, terminates s1 P t -> terminates s1 P (Tau t)
| terminates_vis : forall (e : E2 A) k, (forall v, terminates s1 P (k v)) -> P e -> terminates s1 P (Vis e k)
.

Variant handler_respects_priv (A : Type) (e : E1 A) : Prop :=
| respect_private (SECCHECK : ~ leq (priv1 _ e) l)
                  (FINCHECK : forall s, terminates s (fun e => ~ leq (priv2 _ e) l) (handler A e s))
| respect_public (SECCHECK : leq (priv1 _ e) l)
                 (RESCHECK : state_eqit_secure true true eq (handler A e) (handler A e))
.

Context (Hhandler : forall A (e : E1 A), handler_respects_priv A e).

Lemma test_r {R1 R2} (RR : R1 -> R2 -> Prop) A (e : E1 A) (e' : E2 A) t (k : A -> itree E1 R2) k' r :
  ~ leq (priv1 A e) l ->
  ~ leq (priv2 A e') l ->
  empty A ->
  paco2 (secure_eqit_ Label priv1 RR true true l id) bot2 t (Vis e k) ->
  forall s, paco2 (secure_eqit_ Label priv2 (product_rel RS RR) true true l id) r
             (interp_state handler t s)
             (Vis e' k').
Proof.
  revert t. pcofix CIH. intros t Hsec1 Hsec2 Hempty Heq s.
  pinversion Heq; subst; auto_inj_pair2; subst;
    try solve contra_size; try contradiction.
  - (* inductive tau *) use_simpobs. rewrite H. rewrite interp_state_tau.
    pfold. constructor 12; auto.
  - (* inductive private vis *)
    use_simpobs. rewrite H. rewrite interp_state_vis.
    specialize (Hhandler _ e0). inversion Hhandler; try contradiction.
    specialize (FINCHECK s). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor 12; auto. right. apply CIH; auto.
      simpl. rewrite H0 in H1. pstep. apply H1.
    + rewrite bind_tau. pstep. constructor 12; auto.
    + rewrite bind_vis. pstep. constructor 14; auto.
  - (* coinductive halting tau *) use_simpobs. rewrite H. rewrite interp_state_tau.
    pclearbot. pfold. constructor 12; auto.
  - (* coinductive halting vis *)
    use_simpobs. rewrite H. rewrite interp_state_vis.
    specialize (Hhandler _ e1). inversion Hhandler; try contradiction.
    specialize (FINCHECK s). induction FINCHECK.
    + inversion SIZECHECK. contradiction.
    + rewrite bind_tau. pstep. constructor 12; auto.
    + rewrite bind_vis. pstep. constructor 14; auto.
  - (* coinductive halting vis *)
    use_simpobs. rewrite H. rewrite interp_state_vis.
    specialize (Hhandler _ e1). inversion Hhandler; try contradiction.
    specialize (FINCHECK s). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor 12; auto.
    + rewrite bind_tau. pstep. constructor 12; auto.
    + rewrite bind_vis. pstep. constructor 14; auto.
Qed.

Lemma test_l {R1 R2} (RR : R1 -> R2 -> Prop) A (e : E1 A) (e' : E2 A) t (k : A -> itree E1 R1) k' r :
  ~ leq (priv1 A e) l ->
  ~ leq (priv2 A e') l ->
  empty A ->
  paco2 (secure_eqit_ Label priv1 RR true true l id) bot2 (Vis e k) t ->
  forall s, paco2 (secure_eqit_ Label priv2 (product_rel RS RR) true true l id) r
             (Vis e' k')
             (interp_state handler t s).
Proof.
  revert t. pcofix CIH. intros t Hsec1 Hsec2 Hempty Heq s.
  pinversion Heq; subst; auto_inj_pair2; subst;
    try solve contra_size; try contradiction.
  - (* inductive tau *) use_simpobs. rewrite H. rewrite interp_state_tau.
    pfold. constructor 11; auto.
  - (* inductive private vis *)
    use_simpobs. rewrite H0. rewrite interp_state_vis.
    specialize (Hhandler _ e0). inversion Hhandler; try contradiction.
    specialize (FINCHECK s). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor 11; auto. right. apply CIH; auto.
      simpl. rewrite H in H1. pstep. apply H1.
    + rewrite bind_tau. pstep. constructor 11; auto.
    + rewrite bind_vis. pstep. constructor 13; auto.
  - (* coinductive halting tau *) use_simpobs. rewrite H3. rewrite interp_state_tau.
    pclearbot. pfold. constructor 11; auto.
  - (* coinductive halting vis *)
    use_simpobs. rewrite H3. rewrite interp_state_vis.
    specialize (Hhandler _ e2). inversion Hhandler; try contradiction.
    specialize (FINCHECK s). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor 11; auto.
    + rewrite bind_tau. pstep. constructor 11; auto.
    + rewrite bind_vis. pstep. constructor 13; auto.
  - (* coinductive halting vis *)
    use_simpobs. rewrite H3. rewrite interp_state_vis.
    specialize (Hhandler _ e2). inversion Hhandler; try contradiction.
    specialize (FINCHECK s). induction FINCHECK.
    + inversion SIZECHECK. contradiction.
    + rewrite bind_tau. pstep. constructor 11; auto.
    + rewrite bind_vis. pstep. constructor 13; auto.
Qed.

(* I believe that this is a sound reasoning principle,
   however it looks like the proof could get a little hairy,
   if I could use gpaco and use the bind and transitivity closures, many of these cases become easy
   however, this pushes us up against *)
Lemma interp_eqit_secure_state : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E1 R2),
    eqit_secure Label priv1 RR true true l t1 t2 ->
    state_eqit_secure true true RR (interp_state handler t1) (interp_state handler t2).
Proof.
  intros R1 R2 RR. pcofix CIH. intros t1 t2 Ht s1 s2 Hs. punfold Ht.
  red in Ht. remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Ht before r; intros; use_simpobs.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_ret. pfold. constructor. auto.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_tau. pfold. constructor.
    pclearbot. right. apply CIH; auto.
  - rewrite Heqot1. rewrite interp_state_tau. pfold. constructor; auto. pstep_reverse.
  - rewrite Heqot2. rewrite interp_state_tau. pfold. constructor; auto. pstep_reverse.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    specialize (Hhandler A e). pclearbot. repeat rewrite bind_tau.
    (* could use the bind closure here, but maybe we can do manually for now*)
    repeat setoid_rewrite <- interp_state_tau. inv Hhandler; try contradiction.
    specialize (RESCHECK s1 s2 Hs).
    eapply secure_eqit_bind'; eauto. intros [] [] []. simpl in *. subst.
    repeat rewrite interp_state_tau.
    pfold. constructor. right. eapply CIH; eauto. apply H.
  - pclearbot. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_tau. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction.
    specialize (FINCHECK s1). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor. right.
      apply CIH. apply H. etransitivity; [symmetry |]; eauto.
    + rewrite bind_tau. pstep. constructor 3; auto. pstep_reverse.
    + rewrite bind_vis. pstep. constructor 9; auto. intros. pstep_reverse.
  - pclearbot. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_tau. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction.
    specialize (FINCHECK s2). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor. right.
      apply CIH. apply H. etransitivity; eauto.
    + rewrite bind_tau. pstep. constructor 4; auto. pstep_reverse.
    + rewrite bind_vis. pstep. constructor 10; auto. intros. pstep_reverse.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    specialize (Hhandler _ e1) as He1. specialize (Hhandler _ e2) as He2.
    inv He1; inv He2; try contradiction.
    eapply secure_eqit_bind' with (RR := product_rel RS (fun _ _ => True)).
    + intros [] [] ?. pstep. constructor. right.
      apply CIH. apply H. simpl. apply H0.
    + specialize (FINCHECK s1). specialize (FINCHECK0 s2).
      induction FINCHECK.
      * induction FINCHECK0.
        -- simpl. pstep. constructor. split; auto. simpl.
           transitivity s2; eauto. etransitivity; [symmetry |]; eauto.
        -- pstep. constructor; auto. pstep_reverse.
        -- pstep. constructor; auto. intros. pstep_reverse. apply H2.
      * pstep. constructor; auto. pstep_reverse.
      * pstep. constructor; auto. intros. pstep_reverse. apply H1.
  - rewrite Heqot1. rewrite interp_state_vis. specialize (Hhandler _ e).
    inv Hhandler; try contradiction.
    specialize (FINCHECK s1). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor; auto. pstep_reverse.
      eapply H0; eauto. simpl. etransitivity; [symmetry |]; eauto.
    + rewrite bind_tau. pstep. constructor 3; auto. pstep_reverse.
    + rewrite bind_vis. pstep. constructor 9; auto. intros. pstep_reverse.
  - rewrite Heqot2. rewrite interp_state_vis. specialize (Hhandler _ e).
    inv Hhandler; try contradiction.
    specialize (FINCHECK s2). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor 4; auto. pstep_reverse.
      eapply H0; eauto. simpl. etransitivity; eauto.
    + rewrite bind_tau. pstep. constructor 4; auto. pstep_reverse.
    + rewrite bind_vis. pstep. constructor 10; auto. intros. pstep_reverse.
  - pclearbot.
    rewrite Heqot1. rewrite interp_state_vis.
    rewrite Heqot2. rewrite interp_state_tau.
    pose proof Hhandler as Hhandler'.
    specialize (Hhandler' _ e). inv Hhandler'; try contradiction.
    specialize (FINCHECK s1). induction FINCHECK.
    + inversion SIZECHECK. contradiction.
    + rewrite bind_tau. pstep. constructor 3; auto. pstep_reverse.
    + eapply test_l in H; eauto.
      rewrite bind_vis. pstep. constructor 11; auto. left. apply H.
  - pclearbot.
    rewrite Heqot1. rewrite interp_state_tau.
    rewrite Heqot2. rewrite interp_state_vis.
    pose proof Hhandler as Hhandler'.
    specialize (Hhandler' _ e). inv Hhandler'; try contradiction.
    specialize (FINCHECK s2). induction FINCHECK.
    + inversion SIZECHECK. contradiction.
    + rewrite bind_tau. pstep. constructor 4; auto. pstep_reverse.
    + eapply test_r in H; eauto.
      rewrite bind_vis. pstep. constructor 12; auto. left. apply H.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    pose proof Hhandler as Hhandler'.
    specialize (Hhandler' _ e1). inv Hhandler'; try contradiction.
    specialize (FINCHECK s1). induction FINCHECK.
    + inversion SIZECHECK. contradiction.
    + rewrite bind_tau. pstep. constructor 3; auto. pstep_reverse.
    + clear H0 H1.
      rewrite bind_vis.
      pose proof Hhandler as Hhandler'.
      specialize (Hhandler' _ e2). inv Hhandler'; try contradiction.
      specialize (FINCHECK s2). induction FINCHECK.
      * rewrite bind_ret_l. simpl. pstep. constructor 4; auto. pstep_reverse.
        eapply test_l in H; eauto.
      * rewrite bind_tau. pstep. constructor 11; auto.
      * rewrite bind_vis. pstep. constructor 13; auto.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    pose proof Hhandler as Hhandler'.
    specialize (Hhandler' _ e2). inv Hhandler'; try contradiction.
    specialize (FINCHECK s2). induction FINCHECK.
    + inversion SIZECHECK. contradiction.
    + rewrite bind_tau. pstep. constructor 4; auto. pstep_reverse.
    + clear H0 H1.
      rewrite bind_vis.
      pose proof Hhandler as Hhandler'.
      specialize (Hhandler' _ e1). inv Hhandler'; try contradiction.
      specialize (FINCHECK s1). induction FINCHECK.
      * rewrite bind_ret_l. simpl. pstep. constructor 3; auto. pstep_reverse.
        eapply test_r in H; eauto.
      * rewrite bind_tau. pstep. constructor 12; auto.
      * rewrite bind_vis. pstep. constructor 14; auto.
Qed.

End GeneralStateHandler.


(*
1. Write the paper
2. Security preserving compiler correctness Imp with IO
   a. Semantics for Imp +
   b. Handler security preservation +
   c. Semantics for Asm +
   d. Handler security preservation for Asm
   e. Imp2Asm compiler +'
   f. Imp2Asm correctness (should not involve coinduction)
3. General relation of state interpreters and security
4. Security preserving compiler correctness Imp with IO and private exceptions
5. Write a type system for Imp and prove soundness
   a. "Manual" inference rule
              |- c1   |= c2
              -------------- Manual_R
                |- c1; c2
*)
