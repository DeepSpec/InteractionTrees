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
     Events.Exception
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.SecurityImpExc.SecurityImp
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


Definition priv_exc (A : Type) (e : impExcE A ) :=
  match e with
  | Throw _ s => s end.

Definition priv_exc_io := case_ priv_exc priv_io.

Definition product_rel {R1 R2 S1 S2} (RR1: R1 -> S1 -> Prop) (RR2 : R2 -> S2 -> Prop) 
           (p1 : R1 * R2) (p2 : S1 * S2) : Prop :=
  RR1 (fst p1) (fst p2) /\ RR2 (snd p1) (snd p2). 
  
Definition low_map_equiv (priv : privacy_map ) (s1 s2 : map) : Prop :=
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
           (m1 : stateT map (itree (impExcE +' IOE)) R1) (m2 : stateT map (itree (impExcE +' IOE)) R2) : Prop :=
  forall s1 s2, low_map_equiv priv s1 s2 -> eqit_secure sense_preorder priv_exc_io (product_rel (low_map_equiv priv) RR) b1 b2 Public (m1 s1) (m2 s2).





Definition handle_case {E1 E2 : Type -> Type} {M : Type -> Type} (hl : E1 ~> M) (hr : E2 ~> M) : (E1 +' E2) ~> M :=
  fun _ e => match e with
          | inl1 el => hl _ el
          | inr1 er => hr _ er end.

Definition handle_state_io : forall A, (stateE +' IOE) A -> stateT map (itree (impExcE +' IOE)) A :=
  fun _ e => match e with
          | inl1 el => handleState _ el
          | inr1 er => fun s => r <- ITree.trigger (inr1 er);; Ret (s, r) end. 

Definition handle_imp : forall A, (impExcE +' stateE +' IOE) A -> stateT map (itree (impExcE +' IOE) ) A :=
  fun _ e => match e with
          | inl1 el => fun s => r <- ITree.trigger (inl1 el);; Ret (s, r)
          | inr1 er => handle_state_io _ er end.

Definition interp_imp {R} (t : itree (impExcE +' stateE +' IOE) R ) : stateT map (itree (impExcE +' IOE)) R :=
  interp_state handle_imp t. 

Hint Unfold interp_imp.
Hint Unfold handle_state_io.
Hint Unfold handle_imp.
Hint Unfold product_rel.

Ltac use_simpobs :=
  repeat match goal with 
         | H : TauF _ = observe ?t |- _ => apply simpobs in H 
         | H : RetF _ = observe ?t |- _ => apply simpobs in H
         | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
  end.

Ltac destruct_imp_ev := repeat match goal with
                        | e : (?E1 +' ?E2) ?A |- _ => destruct e
                        | exc : impExcE ?A |- _ => destruct exc
                        | st : stateE ?A |- _ => destruct st
                        | io : IOE ?A |- _ => destruct io
                        end.

Lemma interp_eqit_secure_imp_aux_vis_r:
      forall (R2 R1 : Type) (RR : R1 -> R2 -> Prop)
             (priv_map : privacy_map)
             (r : itree (impExcE +' IOE) (map * R1) ->
                  itree (impExcE +' IOE) (map * R2) -> Prop)
             (t1 : itree (impExcE +' stateE +' IOE) R1)
             (k2 : void -> itree (impExcE +' stateE +' IOE) R2),
        paco2
          (secure_eqit_ sense_preorder (priv_imp priv_map) RR true
                        true Public id) bot2 t1
          (Vis (inl1 (Throw sensitivity Private)) k2) ->
        forall      (s1 : map)
               (k' : void -> itree (impExcE +' IOE) (map * R2)),
          paco2
            (secure_eqit_ sense_preorder priv_exc_io
                          (product_rel (low_map_equiv priv_map) RR) true true
                          Public id) r (interp_state handle_imp t1 s1)
            (Vis (inl1 (Throw sensitivity Private)) k').
Proof.
  intros R2 R1 RR priv_map r t1 k2 H s1 k'.
  assert (Hemp : empty void); try (constructor ; intros []; fail).
  generalize dependent t1. generalize dependent s1. pcofix CIH. intros.
  punfold H0. red in H0. cbn in *.
  inversion H0; ITrace.inj_existT; subst; destruct_imp_ev; try contra_size;
    try contradiction.
  - use_simpobs. rewrite H. rewrite interp_state_tau. pfold. red. cbn.
    unpriv_halt.
  - use_simpobs. rewrite H. rewrite interp_state_vis. cbn. rewrite bind_ret_l. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto. pfold. rewrite H1 in H2.
    apply H2.
  - use_simpobs. rewrite H. rewrite interp_state_vis. cbn. rewrite bind_ret_l. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto.
    pfold. rewrite H1 in H2. apply H2.
  - use_simpobs. rewrite H. rewrite interp_state_vis. cbn. rewrite bind_trigger. rewrite bind_vis.
    setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto. rewrite H1 in H2.
    pfold. constructor; auto.
  - pclearbot. use_simpobs. rewrite H. rewrite interp_state_tau. pfold. red. cbn.
    unpriv_halt.
  - use_simpobs. rewrite H. rewrite interp_state_vis. cbn. rewrite bind_trigger. rewrite bind_vis.
    pfold. red. cbn. unpriv_halt. contra_size.
  - inv SIZECHECK. exfalso; auto.
  - inv SIZECHECK. destruct (H1 tt).
  - inv SIZECHECK. destruct (H1 tt).
  - pclearbot. use_simpobs. rewrite H. rewrite interp_state_vis. cbn. 
    rewrite bind_trigger. rewrite bind_vis. pfold. red. cbn. unpriv_halt.
    contra_size.
  - use_simpobs. rewrite H. rewrite interp_state_vis. cbn. 
    rewrite bind_ret_l. pfold. red. cbn. unpriv_halt. right. pclearbot. eapply CIH; eauto.
  - pclearbot. use_simpobs. rewrite H. rewrite interp_state_vis. cbn. rewrite bind_ret_l.
    pfold. red. cbn. unpriv_halt.
  - pclearbot. use_simpobs. rewrite H. rewrite interp_state_vis. cbn. rewrite bind_trigger.
    rewrite bind_vis. setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto.
    setoid_rewrite tau_eutt. auto.
Qed.

Lemma interp_eqit_secure_imp_aux_vis_l:
  forall (R2 R1 : Type) (RR : R1 -> R2 -> Prop) (priv_map : privacy_map)
         (r : itree (impExcE +' IOE) (map * R1) -> itree (impExcE +' IOE) (map * R2) -> Prop)
         k1 k1'
         (t2 : itree (impExcE +' stateE +' IOE) R2),
    paco2 (secure_eqit_ sense_preorder (priv_imp priv_map) RR true true Public id) bot2
          (Vis (inl1 (Throw sensitivity Private)) k1) t2 ->
    forall s1 s2 : map,
      low_map_equiv priv_map s1 s2 ->
      paco2
        (secure_eqit_ sense_preorder priv_exc_io (product_rel (low_map_equiv priv_map) RR) true
                      true Public id) r
        (Vis (inl1 (Throw sensitivity Private)) k1')
        (interp_state handle_imp t2 s2).
Proof.
  intros R2 R1 RR priv_map r k1 k1' t2 H s1 s2 Hs. assert (Hemp : empty void). 
  { constructor. intros []. }
  generalize dependent t2. generalize dependent s2.
  pcofix CIH. intros. punfold H0. red in H0. cbn in *. inversion H0; ITrace.inj_existT; subst; destruct_imp_ev; try contra_size;
   try contradiction.
  - use_simpobs. rewrite H. rewrite interp_state_tau. pfold. red. cbn.
    unpriv_halt.
  - use_simpobs. rewrite H1. rewrite interp_state_vis. cbn. rewrite bind_ret_l. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto. pfold. rewrite H in H2.
    apply H2.
  - use_simpobs. rewrite H1. rewrite interp_state_vis. cbn. rewrite bind_ret_l. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto.
    + apply low_equiv_update_private_r; auto. cbn in SECCHECK. destruct (priv_map x); try contradiction; auto.
    + pfold. rewrite H in H2. apply H2.
  - use_simpobs. rewrite H1. rewrite interp_state_vis. cbn. rewrite bind_trigger. rewrite bind_vis.
    setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto. rewrite H in H2.
    pfold. constructor; auto.
  - pclearbot. use_simpobs. rewrite H4. rewrite interp_state_tau. pfold. red. cbn.
    unpriv_halt.
  - use_simpobs. rewrite H4. rewrite interp_state_vis. cbn. rewrite bind_trigger. rewrite bind_vis.
    pfold. red. cbn. unpriv_halt. contra_size.
  - pclearbot. use_simpobs. rewrite H4.  rewrite interp_state_vis. cbn. rewrite bind_ret_l.
    cbn. pfold. red. cbn. unpriv_halt.
  - pclearbot. use_simpobs. rewrite H4.  rewrite interp_state_vis. cbn. rewrite bind_ret_l. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto.
    apply low_equiv_update_private_r; auto. cbn in SECCHECK2. destruct (priv_map x); try contradiction; auto.
  - use_simpobs. rewrite H4. rewrite interp_state_vis. cbn. rewrite bind_trigger. rewrite bind_vis.
    setoid_rewrite bind_ret_l. setoid_rewrite <- interp_state_tau. cbn.
    pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto. pclearbot. pfold. constructor; auto.
    pstep_reverse.
  - use_simpobs. pclearbot. rewrite H4.  rewrite interp_state_vis. cbn. 
    rewrite bind_trigger. rewrite bind_vis. pfold. red. cbn. unpriv_halt. contra_size.
  - inv SIZECHECK. exfalso; auto.
  - inv SIZECHECK. destruct (H tt).
  - inv SIZECHECK. destruct (H tt).
Qed.
  

Lemma interp_eqit_secure_imp : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (priv_map : privacy_map) 
                                 (t1 : itree (impExcE +' stateE +' IOE) R1 ) 
                                 (t2 : itree (impExcE +' stateE +' IOE) R2),
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
    pfold. constructor; auto.  pstep_reverse.
  - pclearbot. use_simpobs.
    rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    destruct e as [ex | [s | io] ]; cbn.
    + destruct ex. cbn. repeat rewrite bind_trigger. repeat rewrite bind_vis.
      pfold. constructor; auto. intros [].
    + destruct s; cbn.
      * repeat rewrite bind_ret_l. pfold. constructor. right. cbn. eapply CIH; auto. 
        cbv in SECCHECK. unfold get. red in Hs. destruct (priv_map x) eqn : Hx; try contradiction.
        apply Hs in Hx. rewrite Hx. apply H.
      * repeat rewrite bind_ret_l. pfold. constructor. right. cbv in SECCHECK. cbn.
        destruct (priv_map x) eqn : Hx; try contradiction.
        eapply CIH; auto. apply H. apply low_equiv_update_public; auto.
   + rewrite bind_bind. rewrite bind_bind.  repeat rewrite bind_trigger. destruct io.
     cbv in SECCHECK. destruct s; try contradiction. pfold. constructor; auto.
     left. repeat rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; auto. apply H.
 - pclearbot. use_simpobs. rewrite Heqot1. rewrite Heqot2.
   rewrite interp_state_tau. rewrite interp_state_vis. destruct e as [ex | [s | io] ]; try destruct s.
   + destruct ex. inv SIZECHECK. destruct a.
   + cbn. rewrite bind_ret_l. pfold. cbn. constructor. right. apply CIH; auto. apply H.
   + cbn. rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; auto. apply H.
     apply low_equiv_update_private_l; auto. cbv in SECCHECK. 
     destruct (priv_map x); auto; contradiction.
   + cbn. cbv in SECCHECK. destruct io. destruct s; try contradiction. rewrite bind_bind.
     rewrite bind_trigger. setoid_rewrite bind_ret_l. pfold. red. cbn. 
     rewrite itree_eta'. unpriv_ind. cbn. constructor. right. apply CIH; auto.
     apply H.
 - pclearbot. use_simpobs. rewrite Heqot1. rewrite Heqot2.
   rewrite interp_state_tau. rewrite interp_state_vis. destruct e as [ex | [s | io] ]; try destruct s.
   + destruct ex. inv SIZECHECK. destruct a.
   + cbn. rewrite bind_ret_l. pfold. cbn. constructor. right. apply CIH; auto. apply H.
   + cbn. rewrite bind_ret_l. cbn. pfold. constructor. right. apply CIH; auto. apply H.
     apply low_equiv_update_private_r; auto. cbv in SECCHECK. 
     destruct (priv_map x); auto; contradiction.
   + cbn. cbv in SECCHECK. destruct io. destruct s; try contradiction. rewrite bind_bind.
     rewrite bind_trigger. setoid_rewrite bind_ret_l. pfold. red. cbn. 
     rewrite itree_eta' at 1. unpriv_ind. cbn. constructor. right. apply CIH; auto.
     apply H.
 - use_simpobs. rewrite Heqot1. rewrite Heqot2. pclearbot.
   rewrite interp_state_vis. destruct e1; try destruct s; destruct e2; try destruct s; try destruct i; cbn;
      repeat match goal with | H : nonempty void |- _ => inv H; contradiction
                          | exc : impExcE ?A |- _ => destruct exc 
                          | stio : (stateE +' IOE) ?A |- _ => destruct stio
                          | st : stateE ?A |- _ => destruct st
                          | io : IOE ?A |- _ => destruct io
end;
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
   + rewrite bind_bind. rewrite bind_trigger. cbv in SECCHECK1. destruct s0; try contradiction.
     setoid_rewrite bind_ret_l. pfold. red. cbn. rewrite itree_eta'. unpriv_ind.
     cbn. constructor. right. apply CIH; auto. apply H.
   + rewrite bind_bind. rewrite bind_trigger. setoid_rewrite bind_ret_l. pfold. red. cbn.
     rewrite itree_eta'. unpriv_ind. cbn. constructor. right. apply CIH. apply H.
     apply low_equiv_update_private_r; auto. cbv in SECCHECK2. 
     destruct (priv_map x); auto; contradiction.
   + repeat rewrite bind_bind. repeat rewrite bind_trigger. repeat setoid_rewrite bind_ret_l. 
     cbn. pfold. red. cbn. unpriv_co.
     left. pfold. constructor. right. apply CIH; auto. apply H.
 - use_simpobs. rewrite Heqot1. rewrite interp_state_vis.
   destruct e as [ex | [s | io] ]; try destruct s; cbn.
   + destruct ex. inv SIZECHECK. contradiction.
   + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse.
   + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse. eapply H0; eauto.
     apply low_equiv_update_private_l; auto. cbv in SECCHECK. 
     destruct (priv_map x); auto; contradiction.
   + rewrite bind_bind. rewrite bind_trigger. destruct io. destruct s.
     cbv in SECCHECK; try contradiction. setoid_rewrite bind_ret_l.
     cbn. pfold. red. cbn. unpriv_ind. constructor; auto. pstep_reverse.
 - use_simpobs. rewrite Heqot2. rewrite interp_state_vis.
   destruct e as [ex | [s | io] ]; try destruct s; cbn.
   + destruct ex. inv SIZECHECK. contradiction.
   + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse.
   + rewrite bind_ret_l. cbn. pfold. constructor; auto. pstep_reverse. eapply H0; eauto.
     apply low_equiv_update_private_r; auto. cbv in SECCHECK. 
     destruct (priv_map x); auto; contradiction.
   + rewrite bind_bind. rewrite bind_trigger. destruct io. destruct s.
     cbv in SECCHECK; try contradiction. setoid_rewrite bind_ret_l.
     cbn. pfold. red. cbn. unpriv_ind. constructor; auto. pstep_reverse.
 - pclearbot. destruct e as [ex | [ st | io] ];       
                repeat match goal with | H : nonempty void |- _ => inv H; contradiction
                          | exc : impExcE ?A |- _ => destruct exc 
                          | stio : (stateE +' IOE) ?A |- _ => destruct stio
                          | st : stateE ?A |- _ => destruct st
                          | io : IOE ?A |- _ => destruct io
                          | Hemp : empty value |- _ => inv Hemp; exfalso; eauto
                          | Hemp : empty unit |- _ => inv Hemp; exfalso; remember tt; eauto
                       end.
   destruct s; cbn in *; try contradiction. use_simpobs. rewrite Heqot1.
   rewrite interp_state_vis. cbn. rewrite bind_bind. rewrite bind_trigger. eapply interp_eqit_secure_imp_aux_vis_l; eauto.
   rewrite Heqot2. rewrite tau_eutt. eauto.
 - pclearbot. destruct e as [ex | [ st | io] ];       
                repeat match goal with | H : nonempty void |- _ => inv H; contradiction
                          | exc : impExcE ?A |- _ => destruct exc 
                          | stio : (stateE +' IOE) ?A |- _ => destruct stio
                          | st : stateE ?A |- _ => destruct st
                          | io : IOE ?A |- _ => destruct io
                          | Hemp : empty value |- _ => inv Hemp; exfalso; eauto
                          | Hemp : empty unit |- _ => inv Hemp; exfalso; remember tt; eauto
                       end.
   destruct s; cbn in *; try contradiction. use_simpobs. rewrite Heqot2.
   rewrite interp_state_vis. cbn. rewrite bind_bind. rewrite bind_trigger. eapply interp_eqit_secure_imp_aux_vis_r; eauto.
   rewrite Heqot1. rewrite tau_eutt. eauto.
 - pclearbot.
    destruct e1 as [ex | [ st | io] ];       
                repeat match goal with | H : nonempty void |- _ => inv H; contradiction
                          | exc : impExcE ?A |- _ => destruct exc 
                          | stio : (stateE +' IOE) ?A |- _ => destruct stio
                          | st : stateE ?A |- _ => destruct st
                          | io : IOE ?A |- _ => destruct io
                          | Hemp : empty value |- _ => inv Hemp; exfalso; eauto
                          | Hemp : empty unit |- _ => inv Hemp; exfalso; remember tt; eauto
                       end.
    destruct s; cbn in *; try contradiction. use_simpobs.
    rewrite Heqot1. rewrite interp_state_vis. cbn. rewrite bind_trigger, bind_vis.
    eapply interp_eqit_secure_imp_aux_vis_l; eauto. rewrite Heqot2. pfold. red. cbn. unpriv_halt.
  - pclearbot.
    destruct e2 as [ex | [ st | io] ];       
                repeat match goal with | H : nonempty void |- _ => inv H; contradiction
                          | exc : impExcE ?A |- _ => destruct exc 
                          | stio : (stateE +' IOE) ?A |- _ => destruct stio
                          | st : stateE ?A |- _ => destruct st
                          | io : IOE ?A |- _ => destruct io
                          | Hemp : empty value |- _ => inv Hemp; exfalso; eauto
                          | Hemp : empty unit |- _ => inv Hemp; exfalso; remember tt; eauto
                       end.
    destruct s; cbn in *; try contradiction. use_simpobs.
    rewrite Heqot2. rewrite interp_state_vis. cbn. rewrite bind_trigger. rewrite bind_vis.
    eapply interp_eqit_secure_imp_aux_vis_r; eauto. rewrite Heqot1. pfold. red.
    destruct (classic_empty A).
    + cbn. unpriv_halt. contra_size.
    + cbn. rewrite itree_eta'. unpriv_ind. pstep_reverse.
Qed.


Section GeneralStateHandler.

Context (S : Type).
Context (RS : S -> S -> Prop).

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

Variant handler_respects_priv (A : Type) (e : E1 A) : Prop :=
  | respect_private (SECCHECK : ~ leq (priv1 A e) l ) (RESCHECK : state_eqit_secure true true top2 (handler A e) (handler A e) )
  | respect_public (SECCHECK : leq (priv1 A e) l ) (RESCHECK : state_eqit_secure true true eq (handler A e) (handler A e)).

Context (Hhandler : forall A (e : E1 A), handler_respects_priv A e).

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
