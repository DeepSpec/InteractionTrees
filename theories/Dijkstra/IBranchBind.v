From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
     Logic.IndefiniteDescription
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     EuttEv
     Divergence
     Dijkstra.IBranch
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Definition peel_vis {E R S A B} (e0 : E A) (a : A) (k0 : unit -> ibranch E R)
           (e1 : E B) (k1 : B -> itree E S) 
           (peel : ibranch' E R -> itree' E S -> ibranch E S) : ibranch E S.
destruct (classicT (A = B) ).
- subst. apply (Vis (evans _ e0 a) (fun _ => peel (observe (k0 tt)) (observe (k1 a) ) ) ).
- apply ITree.spin.
Defined.

CoFixpoint peel_ {E R S} (ob : ibranch' E R) (ot : itree' E S) : ibranch E S :=
  match ob, ot with
  | TauF b, TauF t => Tau (peel_ (observe b) (observe t))
  | _, RetF s => Ret s
  | TauF b, ot => Tau (peel_ (observe b) ot )
  | ob, TauF t => Tau (peel_ ob (observe t) )
  | VisF (evempty _ Hempty e) _ , _ => Vis (evempty _ Hempty e) (fun v : void => match v with end)
  (* The type of this is problematic need some tricky dependently typed programming
     in order to have this work
  *)

  | VisF (evans _ e0 a) k0, VisF e1 k1 => peel_vis e0 a k0 e1 k1 peel_
  | _, _ => ITree.spin 
  end.

Definition peel {E R S} (b : ibranch E R) (t : itree E S) : ibranch E S :=
  peel_ (observe b) (observe t).
 
Definition peel_cont_vis {E R S A B} (e0 : E A) (a : A) (k0 : unit -> ibranch E R)
           (e1 : E B) (k1 : B -> itree E S) 
           (peel : ibranch' E R -> itree' E S -> ibranch E R) : ibranch E R.
destruct (classicT (A = B) ).
- subst. apply (Tau (peel (observe (k0 tt)) (observe (k1 a) ) ) ).
- apply ITree.spin.
Defined.


CoFixpoint peel_cont_ {E R S} (ob : ibranch' E R) (ot : itree' E S) : ibranch E R :=
  match ot with
  | RetF _ => go ob
  | TauF t => match ob with 
                   | TauF b => Tau (peel_cont_ (observe b) (observe t))
                   | ob => Tau (peel_cont_ ob (observe t)  )
                   end
  | VisF e1 k1 => match ob with 
                       | TauF b => Tau (peel_cont_ (observe b) ot)
                       | VisF (evempty _ Hempty e) _ => 
                         ITree.spin
                       | VisF (evans _ e0 a) k0 => peel_cont_vis e0 a k0 e1 k1 peel_cont_
                       | _ => ITree.spin
                       end
  end.
(*                                                   
  match ob, ot with
  | TauF b, TauF t => Tau (peel_cont_ (observe b) (observe t))
  | _ , RetF s => go ob
  | TauF b, ot => Tau (peel_cont_ (observe b) ot )
  | ob, TauF t => Tau (peel_cont_ ob (observe t) )
  | VisF (evempty _ Hempty e) _ , _ => Vis (evempty _ Hempty e) (fun v : void => match v with end)
  (* The type of this is problematic need some tricky dependently typed programming
     in order to have this work
  *)

  | VisF (evans _ e0 a) k0, VisF e1 k1 => peel_cont_vis e0 a k0 e1 k1 peel_cont_
  | _, _ => ITree.spin 
  end.
*)


Definition peel_cont {E R S} (b : ibranch E R) (t : itree E S) : S -> ibranch E R :=
  fun s => peel_cont_ (observe b) (observe t).

Inductive branch_prefix {E : Type -> Type} {R S: Type} 
          (F : ibranch E R -> ibranch E S -> Prop) : ibranch' E R -> ibranch' E S -> Prop := 
| ret_prefix (r : R) (ob : ibranch' E S) : branch_prefix F (RetF r) ob
| vis_ans_prefix {A : Type} (e : E A) (a : A) (br :ibranch E R) (bs :ibranch E S) :
    F br bs -> branch_prefix F (VisF (evans A e a) (fun _ => br) ) (VisF (evans A e a) (fun _ => bs))
| vis_empty_prefix {A : Type} (e : E A) (Hempty : A -> void) :
    branch_prefix F (VisF (evempty A Hempty e) (fun v : void => match v with end) )
                    (VisF (evempty A Hempty e) (fun v : void => match v with end) )
| tau_lr_prefix (br : ibranch E R) (bs : ibranch E S) : 
    F br bs -> branch_prefix F (TauF br) (TauF bs)
(* can add eutt style inductive tau rules *)


.


Lemma refine_ret_vis_contra : forall (E: Type -> Type) (R A: Type)
                     (r : R) (e : E A) (k : A -> itree E R),
    ~ (Ret r ⊑ Vis e k).
Proof.
  intros. intro Hcontra. pinversion Hcontra.
Qed.

(* maybe a better way of doing it is to use strong LEM to see if X = A in the vis case
   then I can remove that if statement given

 *)

Lemma peel_t_ret : forall E R S (b : ibranch E S) (t : itree E R) r, t ≅ Ret r -> (peel b t ≅ Ret r)%itree.
Proof.
  intros.  unfold peel.
  pinversion H; subst; try inv CHECK.
  destruct (observe b); cbn; auto. 
  - pfold. red. cbn. constructor. auto.
  - pfold. red. cbn. constructor; auto.
  - pfold. red. cbn. simpl. destruct e.
    + cbn. constructor. auto.
    + cbn. constructor. auto.
Qed.


(*doing these proofs, may require some techniques you don't really know*)

Lemma peel_refine_t : forall (E : Type -> Type) (R S : Type)
                  (b : ibranch E S) (t : itree E R) (f : R -> itree E S)
     (HeuttEv : b ⊑ ITree.bind t f),
    peel b t ⊑ t.
Proof.
  intros E R S b t f. generalize dependent b. generalize dependent t.
  pcofix CIH. intros.
  punfold HeuttEv. red in HeuttEv. cbn in HeuttEv. pfold. red.
  unfold peel.
  destruct (observe t) eqn : Heq.
  - destruct (observe b); cbn; try (constructor; auto).
    destruct e; cbn; constructor; auto.
  - dependent induction HeuttEv.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_tau in x. pinversion x.
      inv CHECK.
    + rewrite <- x0. cbn. constructor. right. eapply CIH.
      pclearbot. symmetry in Heq. apply simpobs in x0.
      apply simpobs in x. apply simpobs in Heq.
      apply eq_sub_eutt in x0. apply eq_sub_eutt in Heq.
      rewrite tau_eutt in Heq. rewrite tau_eutt in x0.
      rewrite <- Heq. rewrite x. rewrite tau_eutt. auto.
    + rewrite <- x. cbn. constructor. right. eapply CIH.
      clear IHHeuttEv. symmetry in Heq. apply simpobs in Heq.
      apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
      rewrite <- Heq. pfold. auto.
    + cbn. destruct (observe b) eqn : Heq'.
      * cbn. rewrite <- Heq'. constructor. right. eapply CIH. 
        symmetry in Heq'.
        apply simpobs in Heq'. rewrite Heq'.
        symmetry in Heq. apply simpobs in Heq.
        apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
        rewrite <- Heq. apply simpobs in x. rewrite x.
        rewrite tau_eutt. pfold. auto.
      * cbn. clear IHHeuttEv. 
        constructor. right. eapply CIH. 
        symmetry in Heq. apply simpobs in Heq.
        apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
        rewrite <- Heq.
        apply simpobs in x. apply eq_sub_eutt in x.
        rewrite tau_eutt in x. rewrite x.
        enough (Tau t1 ⊑ t2). 
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * destruct e; cbn.
        ++ constructor. right. rewrite <- Heq'. clear IHHeuttEv.
           eapply CIH. symmetry in Heq.
           apply simpobs in Heq. apply eq_sub_eutt in Heq. 
           rewrite tau_eutt in Heq. apply simpobs in x.
           apply eq_sub_eutt in x. rewrite tau_eutt in x.
           rewrite <- Heq. rewrite x. pfold. red.
           rewrite Heq'. auto.
        ++ constructor. right. rewrite <- Heq'. clear IHHeuttEv.
           eapply CIH. symmetry in Heq.
           apply simpobs in Heq. apply eq_sub_eutt in Heq. 
           rewrite tau_eutt in Heq. apply simpobs in x.
           apply eq_sub_eutt in x. rewrite tau_eutt in x.
           rewrite <- Heq. rewrite x. pfold. red.
           rewrite Heq'. auto.
    + exfalso. symmetry in Heq. apply simpobs in Heq.
      apply simpobs in x.
      rewrite Heq in x. rewrite bind_tau in x. pinversion x.
      inv CHECK.
  - dependent induction HeuttEv.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x; inv CHECK.
    + rewrite <- x. cbn. constructor. eapply IHHeuttEv; eauto.
    + exfalso. symmetry in Heq. apply simpobs in x. apply simpobs in Heq.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x; inv CHECK.
    + rewrite <- x0.
      symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x. pinversion x.
      subst. inj_existT; subst.
      inversion H; subst; inj_existT; subst.
      * unfold observe. cbn. unfold peel_vis.
        assert (B = B). auto.
        destruct (classicT (B = B) ); try contradiction.
        unfold eq_rect_r, eq_rect. 
        remember (eq_sym e) as He. clear HeqHe.
        dependent destruction He. cbn. constructor; eauto.
        intros. inversion H2. subst; inj_existT; subst.
        apply H0 in H2. pclearbot. unfold id. right. eapply CIH.
        enough (k2 b0 ≈ ITree.bind (k b0) f ).
        { rewrite <- H3. auto. }
        red in x1. cbn in x1. inversion x1. subst; inj_existT; subst.
        symmetry. pclearbot. specialize ( REL0 b0).
        apply eq_sub_eutt. auto.
      * cbn. constructor; eauto. intros. contradiction.
Qed.

Lemma not_spin_eutt_ret : forall E R (r : R), ~ (@ITree.spin E R ≈ Ret r). 
Proof.
  intros. intros Hcontra. specialize (@spin_diverge E R) as Hdiv.
  rewrite Hcontra in Hdiv. pinversion Hdiv.
Qed.


Lemma proper_peel_eutt_l : forall (E : Type -> Type) (R S : Type) 
                             (b b': ibranch E R) (t : itree E S),
    (b ≈ b')%itree -> (peel b t ≈ peel b' t)%itree.
Proof.
  intros E R S. pcofix CIH. intros. unfold peel.
  destruct (observe t).
  - pfold. red. destruct (observe b); destruct (observe b'); cbn;
                  try (destruct e); try (destruct e0); cbn;
                try (constructor; auto; fail).
  - pfold. punfold H0. red in H0. dependent induction H0.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor.
      right. rewrite x0. eapply CIH. reflexivity.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor. right.
      pclearbot. eapply CIH. auto.
    + rewrite <- x0. rewrite <- x. destruct e; cbn.
      * red. cbn. constructor. right. rewrite x. rewrite x0. 
        eapply CIH. pfold. red. rewrite <- x. rewrite <- x0.
        constructor. auto.
      * red. cbn. constructor. right. rewrite x0. rewrite x.
        eapply CIH. pfold. red. rewrite <- x0. rewrite <- x.
        constructor. auto.
    + destruct (observe b); destruct (observe b'); dependent destruction x.
      * red. cbn. constructor. right. remember (@go (EvAns E) _ (RetF r0)) as t1. 
        assert (RetF r0 = observe t1). 
        { rewrite Heqt1. auto. }
        rewrite H. eapply CIH. rewrite Heqt1. pfold. auto.
      * red. cbn. constructor. right. eapply CIH. 
        enough (t2 ≈ Tau t3).
        { rewrite tau_eutt in H. auto. }
         pfold. auto.
      * red. destruct e; cbn.
        ++ constructor. right.
           remember (@go (EvAns E) _ (VisF (evans A ev ans) k )  ) as t1.
           assert (VisF (evans A ev ans) k  = observe t1).
           { rewrite Heqt1. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
        ++ constructor. right.
           remember (go (VisF (evempty A Hempty ev) k )  ) as t1.
           assert (VisF (evempty A Hempty ev) k = observe t1 ).
           { subst. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
    + destruct (observe b); destruct (observe b'); dependent destruction x.
      * red. cbn. constructor. right. remember (@go (EvAns E) _ (RetF r0)) as t2. 
        assert (RetF r0 = observe t2). 
        { subst. auto. }
        rewrite H. eapply CIH. rewrite Heqt2. pfold. auto.
      * red. cbn. constructor. right. eapply CIH.
        enough (Tau t1 ≈ t3).
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * red. destruct e; cbn.
        ++ constructor. right.
           remember (@go (EvAns E) _ (VisF (evans A ev ans) k )  ) as t2.
           assert (VisF (evans A ev ans) k  = observe t2).
           { subst. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
        ++ constructor. right.
           remember (go (VisF (evempty A Hempty ev) k )  ) as t2.
           assert (VisF (evempty A Hempty ev) k = observe t2 ).
           { subst. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
  - pfold. punfold H0. red in H0. dependent induction H0.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor.
      left. eapply paco2_mon with (r := bot2); intuition.
      enough (@ITree.spin (EvAns E) S  ≈ ITree.spin); auto.
      reflexivity.
    + rewrite <- x. rewrite <- x0. red. cbn. constructor. right.
      remember (go (VisF e k) ) as t0.
      assert (VisF e k = observe t0).
      { subst. auto. }
      rewrite H. eapply CIH. pclearbot. auto.
    + rewrite <- x0. rewrite <- x. red. destruct e; cbn.
      * unfold observe. cbn. unfold peel_vis.
        destruct (classicT (A = X) ).
        ++ unfold eq_rect_r, eq_rect. remember (eq_sym e) as He.
           dependent destruction He. cbn. constructor. intros.
           right. eapply CIH. pclearbot. auto.
        ++ cbn. constructor. left. eapply paco2_mon with (r := bot2); intuition.
           enough (@ITree.spin (EvAns E) S ≈ ITree.spin ); auto.
           reflexivity.
      * constructor. left. contradiction.
   + rewrite <- x. red. destruct (observe b') eqn : Heq.
     * rewrite <- Heq. cbn. constructor; auto. eapply IHeqitF; eauto. rewrite Heq. auto.
     * cbn. constructor. right.
       remember (go (VisF e k) ) as t2.
       assert (VisF e k = observe t2).
       { subst. auto. }
       rewrite H. eapply CIH.
       enough (t1 ≈ Tau t0).
       { rewrite tau_eutt in H1. auto. }
       pfold; auto.
     * cbn. constructor; eauto. rewrite <- Heq. eapply IHeqitF; eauto.
       rewrite Heq. auto.
  + rewrite <- x. red. destruct (observe b) eqn : Heq.
     * rewrite <- Heq. cbn. constructor; auto. eapply IHeqitF; eauto. rewrite Heq. auto.
     * cbn. constructor. right.
       remember (go (VisF e k) ) as t1.
       assert (VisF e k = observe t1).
       { subst. auto. }
       rewrite H. eapply CIH.
       enough (Tau t0 ≈ t2).
       { rewrite tau_eutt in H1. auto. }
       pfold; auto.
     * cbn. constructor; eauto. rewrite <- Heq. eapply IHeqitF; eauto.
       rewrite Heq. auto.
Qed.



Lemma proper_peel_eutt_r : forall (E : Type -> Type) (R S : Type) 
                             (b: ibranch E R) (t t': itree E S),
    (t ≈ t')%itree -> (peel b t ≈ peel b t')%itree.
Proof.
  intros E R S. pcofix CIH. intros.
  pfold. red. unfold peel. destruct (observe b) eqn : Heqb.
  - punfold H0. red in H0. dependent induction H0.
    + rewrite <- x. rewrite <- x0.  cbn. constructor. auto.
    + rewrite <- x. rewrite <- x0. cbn. constructor. right. rewrite <- Heqb.
      eapply CIH. pclearbot. auto.
    + rewrite <- x0. rewrite <- x. cbn. constructor.
      left. apply paco2_eqit_refl.
    + rewrite <- x.  cbn. constructor; auto. eapply IHeqitF; eauto.
    + rewrite <- x. cbn. constructor; auto. eapply IHeqitF; eauto.
  - punfold H0. red in H0. dependent induction H0.
    + rewrite <- x. rewrite <- x0. cbn. constructor. auto.
    + rewrite <- x0. rewrite <- x. cbn. constructor. right.
      pclearbot. eapply CIH; auto.
    + rewrite <- x0. rewrite <- x. cbn. constructor. right.
      rewrite x0. rewrite x. eapply CIH.
      pfold. red. rewrite <- x0. rewrite <- x.
      constructor. auto.
    + rewrite <- x. destruct (observe t') eqn : Heqt'.
      * cbn.  constructor; auto. clear IHeqitF.
        dependent induction H0.
        ++ rewrite <- x. destruct (observe t0); cbn; try (constructor; auto; fail).
           destruct e; cbn; constructor; auto.
        ++ rewrite <- x. cbn. destruct (observe t2) eqn : Heqt2; cbn.
           ** constructor; eauto. rewrite <- Heqt2.  eapply IHeqitF; eauto.
           ** constructor; auto. eapply IHeqitF; eauto.
           ** destruct e; cbn;
              try (constructor; auto; rewrite <- Heqt2; eapply IHeqitF; eauto).
      * cbn. constructor. right. eapply CIH; eauto.
        enough (t1 ≈ Tau t2).
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * cbn. constructor. rewrite <- Heqt'. right. eapply CIH.
        pfold. red. rewrite Heqt'. auto.
    + rewrite <- x. destruct (observe t).
      * cbn. constructor; auto. clear IHeqitF.
        dependent induction H0.
        ++ rewrite <- x. destruct (observe t0); try (destruct e); cbn; constructor; auto.
        ++ rewrite <- x. destruct (observe t1) eqn : Heqt1; cbn.
           ** constructor; auto. rewrite <- Heqt1. eapply IHeqitF; eauto.
           ** constructor; auto. eapply IHeqitF; eauto.
           ** destruct e; cbn; try (constructor; auto; rewrite <- Heqt1; eapply IHeqitF; eauto).
      * cbn. constructor. right. eapply CIH; eauto.
        rewrite <- tau_eutt at 1. pfold. auto.
      * cbn. constructor. right. remember ((Vis e k) ) as t1.
        assert (VisF e k = observe t1).
        { subst. auto. }
        rewrite H. eapply CIH. subst. pfold. auto.
  - punfold H0. red in H0. dependent induction H0.
    + rewrite <- x. rewrite <- x0. destruct e; cbn; constructor; auto.
    + rewrite <- x. rewrite <- x0. destruct e; cbn; constructor; right; rewrite <- Heqb;
      eapply CIH; pclearbot; eauto.
    + rewrite <- x. rewrite <- x0. destruct e0; cbn.
      * unfold observe. cbn. unfold peel_vis.
        destruct (classicT (A = u) ).
        ++ unfold eq_rect_r, eq_rect. remember (eq_sym e0) as He.
           dependent destruction He. cbn. constructor. intros.
           right. eapply CIH. pclearbot. auto.
        ++ cbn. constructor. left. apply paco2_eqit_refl.
      * constructor. intuition.
    + rewrite <- x. destruct (observe t'); destruct e; cbn.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. cbn. constructor; auto.
        ++ rewrite <- x. cbn. constructor; eauto.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. cbn. constructor; auto.
        ++ rewrite <- x. cbn. constructor; eauto.
      * constructor. rewrite <- Heqb. right. eapply CIH.
        setoid_rewrite <- tau_eutt at 2. pfold. auto.
      * rewrite <- Heqb. constructor. right. eapply CIH.
        setoid_rewrite <- tau_eutt at 2. pfold. auto.
      * constructor; auto. clear IHeqitF. 
        dependent induction H0.
        ++ rewrite <- x. unfold observe. cbn.
           unfold peel_vis. destruct (classicT (A = X0) ).
           ** unfold eq_rect_r, eq_rect. 
              remember (eq_sym e) as He. dependent destruction He.
              cbn. constructor. intros. right. pclearbot. eapply CIH; eauto.
           ** cbn. constructor. left. apply paco2_eqit_refl.
        ++ rewrite <- x. cbn. constructor; auto; eapply IHeqitF; eauto.
      * constructor; auto. clear IHeqitF.
        dependent induction H0.
        ++ rewrite <- x. cbn. constructor. intuition.
        ++ rewrite <- x. cbn. constructor; auto; eapply IHeqitF; eauto.
   + rewrite <- x. cbn. destruct (observe t) eqn : Heqt; destruct e; cbn.
     * constructor; auto. clear IHeqitF. dependent induction H0.
       ++ rewrite <- x. cbn. constructor; auto.
       ++ rewrite <- x. cbn. constructor; eauto.
     * constructor; auto. clear IHeqitF. dependent induction H0.
       ++ rewrite <- x. cbn. constructor; auto.
       ++ rewrite <- x. cbn. constructor; eauto.
     * constructor. right. rewrite <- Heqb. eapply CIH; eauto. rewrite <- tau_eutt.
       pfold. auto.
     * constructor. rewrite <- Heqb. right. eapply CIH; eauto. rewrite <- tau_eutt.
       pfold. auto.
     * constructor; auto. clear IHeqitF. dependent induction H0.
       ++ rewrite <- x. unfold observe. cbn.
          unfold peel_vis.
          destruct (classicT (A = X0) ).
          ** unfold eq_rect_r, eq_rect.
             remember (eq_sym e) as He. dependent destruction He.
             cbn. constructor. intros. right. pclearbot. eapply CIH; apply REL.
          ** cbn. constructor. left. apply paco2_eqit_refl.
       ++ rewrite <- x. cbn. constructor; eauto.
     * constructor; auto. clear IHeqitF. dependent induction H0.
       ++ rewrite <- x. cbn. constructor. intuition.
       ++ rewrite <- x. cbn. constructor; eauto.
Qed.

Instance proper_eutt_peel {E R S} : Proper (eutt eq ==> eutt eq ==> eutt eq) (@peel E R S).
Proof.
  intros ? ? ? ? ? ?. rewrite proper_peel_eutt_l with (t := x0); eauto. 
  eapply proper_peel_eutt_r; eauto.
Qed.

Lemma not_peel_vis_ret: forall (R : Type) (E : Type -> Type) (S X : Type) (e : E X) (k : X -> itree E R) 
                          (r : R) (t1 : itree (EvAns E) S),
    ~ (peel t1 (Vis e k) ≈ Ret r)%itree.
Proof.
  intros R E S X e k r t1 Heutt.
  punfold Heutt. unfold peel in *. red in Heutt. cbn in *.
  dependent induction  Heutt.
  - destruct (observe t1); cbn in x; try discriminate.
    destruct e0; cbn in *; try discriminate.
    unfold observe in x. cbn in x. unfold peel_vis in x.
    destruct (classicT (A = X)); try discriminate.
    unfold eq_rect_r, eq_rect in x. remember (eq_sym e0) as He.
    dependent destruction He. discriminate.
  - destruct (observe t1); cbn in x; try discriminate.
    + injection x as Hspin. rewrite Hspin in Heutt. 
      eapply not_spin_eutt_ret. pfold. eauto.
    + injection x as Ht0. eapply IHHeutt; eauto. rewrite Ht0. reflexivity.
    + destruct e0; cbn in *; try discriminate.
      unfold observe in x. cbn in x. unfold peel_vis in *.
      destruct (classicT (A = X) ).
      * unfold eq_rect_r, eq_rect in x. remember (eq_sym e0) as He.
        dependent destruction He. discriminate.
      * cbn in x. injection x as Hspin. rewrite Hspin in Heutt.
        eapply not_spin_eutt_ret. pfold. eauto.
Qed.


Lemma peel_ret_inv:
        forall (R : Type) (r : R) (E : Type -> Type) (S : Type) (b : ibranch E S) (t : itree E R),
          (peel b t ≈ Ret r)%itree -> (t ≈ Ret r)%itree.
Proof.
  intros R r E S b t H. unfold peel in H.
  punfold H. red in H. cbn in H. pfold. red. cbn.
  dependent induction H.
  - unfold peel in x. destruct (observe b); destruct (observe t); cbn in *;
                        dependent destruction x; try (constructor; auto; fail).
    + destruct e; dependent destruction x; try (constructor; auto).
    + destruct e; dependent destruction x.
    + destruct e; dependent destruction x.
      unfold observe in x. cbn in x. unfold peel_vis in x.
      destruct (classicT (A = X0) ) eqn : Heq.
      * unfold eq_rect_r, eq_rect in x. subst. remember (eq_sym eq_refl) as He.
        dependent destruction He. cbn in x0. discriminate.
      * discriminate.
  - destruct (observe b); destruct (observe t); cbn in x; dependent destruction x.
    + constructor; auto. eapply IHeqitF with (b := Ret r0); eauto.
    + exfalso. eapply not_spin_eutt_ret. pfold. eauto.
    + constructor; auto. eapply IHeqitF; eauto.
    + exfalso. destruct (observe t0).  
      * cbn in H. eapply not_spin_eutt_ret. 
        inv  H. pfold. eauto.
      * cbn in H. inv H. eapply not_peel_vis_ret.
        pfold. eauto.
      * destruct e0.
        ++ clear IHeqitF. unfold observe in H. cbn in H. unfold peel_vis in H.
           destruct (classicT (A = X) ).
           ** unfold eq_rect_r, eq_rect in H. remember (eq_sym e0) as He.
              dependent destruction He. inv H.
           ** eapply not_spin_eutt_ret. pfold. eauto.
        ++ cbn in H. inv H.
    + destruct e; cbn in x; try discriminate.
    + constructor; auto. eapply IHeqitF with (b := Vis e k); eauto. cbn.
      destruct e; cbn in x; dependent destruction x; auto.
    + destruct e; cbn in x; try discriminate.
      unfold observe in x. cbn in x. unfold peel_vis in x.
      destruct (classicT (A = X0) ).
      * unfold eq_rect_r, eq_rect in x. remember (eq_sym e) as He.
        dependent destruction He. discriminate.
      * injection x as Hspin. cbn in Hspin. exfalso.
        assert (t1 ≈ Ret r).
        { pfold. auto. } 
        rewrite Hspin in H0. eapply not_spin_eutt_ret; eauto.
Qed.

Lemma eqitF_r_refl: forall (E : Type -> Type) (R: Type) r
    (ot: itree' E R),
    eqitF eq true true id (upaco2 (eqit_ eq true true id) r)
          ot ot.
Proof.
  intros E R r ot.
  destruct ot; constructor; auto.
  - left. eapply paco2_mon with (r := bot2); intuition. 
    apply Equivalence_eutt. apply eq_equivalence.
  - left. eapply paco2_mon with (r := bot2); intuition.
    apply Equivalence_eutt. apply eq_equivalence.
Qed.

Lemma eqitF_mon:
  forall (E : Type -> Type) (R : Type) (r : itree (EvAns E) R -> itree (EvAns E) R -> Prop)
    (t1 : itree' (EvAns E) R) (t0 : itree' (EvAns E) R),
    eqitF eq true true id (upaco2 (eqit_ eq true true id) bot2) t1 t0 ->
    eqitF eq true true id (upaco2 (eqit_ eq true true id) r) t1 t0.
Proof.
  intros E R r t1 t0' REL.
  induction REL; constructor; eauto.
  - pclearbot. left. eapply paco2_mon; eauto; intuition.
  - pclearbot. intros. left. eapply paco2_mon; eauto; intuition.
Qed.

Lemma eqitF_observe_peel_cont_vis:
  forall (E : Type -> Type) (R S A : Type) (ev : E A) (ans : A)
    (k1 k2 : unit -> itree (EvAns E) R),
    (forall v : unit, id (upaco2 (eqit_ eq true true id) bot2) (k1 v) (k2 v)) ->
    forall r : itree (EvAns E) R -> itree (EvAns E) R -> Prop,
      (forall (b b' : ibranch E R) (t : itree E S),
          (b ≈ b')%itree ->
          r (peel_cont_ (observe b) (observe t)) (peel_cont_ (observe b') (observe t))) ->
      forall (X : Type) (e : E X) (k : X -> itree E S),
        eqitF eq true true id (upaco2 (eqit_ eq true true id) r)
              (observe (peel_cont_ (VisF (evans A ev ans) k1) (VisF e k)))
              (observe (peel_cont_ (VisF (evans A ev ans) k2) (VisF e k))).
Proof.
  intros E R S A ev ans k1 k2 REL r CIH X e k.
  unfold observe. cbn. unfold peel_cont_vis.
  destruct (classicT (A = X) ).
  - unfold eq_rect_r, eq_rect. remember (eq_sym e0) as He.
    dependent destruction He. cbn. constructor.
    intros. right. pclearbot. eapply CIH. auto.
  - cbn. apply eqitF_r_refl.
Qed.


Lemma proper_peel_cont_eutt_l : forall (E : Type -> Type) (R S : Type) 
                             (b b': ibranch E R) (t : itree E S) (s : S),
    (b ≈ b')%itree -> (peel_cont b t s ≈ peel_cont b' t s)%itree.
Proof.
  intros E R S. unfold peel_cont. intros b b' t _.
  revert b b' t. pcofix CIH. intros. pfold. punfold H0. red in H0.
  destruct (observe t) eqn : Heqt.
  - red. destruct (observe b') eqn : Hb; destruct (observe b) eqn : Hb'; inversion H0; cbn;
    try (constructor; auto; fail);
    try (constructor; auto; eapply eqitF_mon; eauto; fail);
    try (destruct e; cbn);
    try (constructor; auto; eapply eqitF_mon; eauto; fail).
    + constructor. pclearbot. left. eapply paco2_mon; eauto; intuition.
    + subst. inj_existT. subst. cbn. constructor. intros. left. inv H0.
      inj_existT. subst. pclearbot. eapply paco2_mon; eauto; intuition.
    + inj_existT. subst. inj_existT. subst. cbn. constructor; auto. intuition.
      (*looks like I didn't actually need to induct here ... *)
  - dependent induction H0; try clear IHeqitF.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor. right.
      rewrite x. eapply CIH; eauto. pfold. red. rewrite <- x. constructor; auto.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor. right.
      eapply CIH. pclearbot. auto.
    + rewrite <- x0. rewrite <- x. red. destruct e; cbn; constructor; right.
      * rewrite x. rewrite x0. eapply CIH; eauto. pfold. red.
        rewrite <- x0. rewrite <- x. constructor. auto.
      * rewrite x. rewrite x0. eapply CIH; eauto. pfold. red.
        rewrite <- x0. rewrite <- x. constructor. auto.
    + rewrite <- x. red. cbn.
      destruct (observe b') eqn : Heqb'; cbn.
      * constructor. right. rewrite <- Heqb'. eapply CIH.
        symmetry in Heqb'. apply simpobs in Heqb'. rewrite Heqb'.
        pfold. auto.
      * constructor. right. eapply CIH. setoid_rewrite <- tau_eutt at 2.
        pfold. auto.
      * constructor. right. rewrite <- Heqb'. eapply CIH.
        symmetry in Heqb'. apply simpobs in Heqb'. rewrite Heqb'. pfold. auto.
    + rewrite <- x. red. cbn. destruct (observe b) eqn : Heqb; cbn.
      * constructor; auto. right. rewrite <- Heqb. eapply CIH.
        pfold. red. rewrite Heqb. auto.
      * constructor. right. eapply CIH. rewrite <- tau_eutt at 1. pfold. auto.
      * constructor. right. rewrite <- Heqb. eapply CIH. pfold.
        red. rewrite Heqb. auto.
  - red. dependent induction H0; cbn.
    +  rewrite <- x0. rewrite <- x. cbn. constructor. left. pfold. apply eqitF_r_refl.
    + rewrite <- x0. rewrite <- x. cbn. constructor. right. rewrite <- Heqt. eapply CIH.
      pclearbot. auto.
    + rewrite <- x. rewrite <- x0. destruct e; cbn; try (apply eqitF_observe_peel_cont_vis; auto).
      apply eqitF_r_refl.
    + rewrite <- x. cbn. constructor; eauto.
    + rewrite <- x. cbn. constructor; eauto.
Qed.

Lemma peel_cont_ret_inv : forall E R S (b : ibranch E R) (t : itree E S) (s : S),
    t ≈ Ret s -> (peel_cont_ (observe b) (observe t) ≈ b)%itree.
Proof.
  intros E R S. pcofix CIH. intros. punfold H0. red in H0. cbn in H0. dependent induction H0; subst.
  - rewrite <- x. cbn. pfold. red. cbn. apply eqitF_r_refl.
  - rewrite <- x. destruct (observe b) eqn : Hb.
    + pfold. red. cbn. constructor; auto. 
      
      specialize (IHeqitF r CIH (Ret r0) t1 s ); auto.
      assert (S = S). auto. apply IHeqitF in H; auto. rewrite Hb.
      punfold H.
    + pfold. red. rewrite Hb. cbn.   constructor. right. eapply CIH with (s := s).
      pfold. auto.
    + pfold. red. rewrite Hb. cbn. rewrite <- Hb. constructor; auto.
      specialize (IHeqitF r CIH b t1 s ); auto.
      assert (S = S). auto. apply IHeqitF in H; auto. punfold H.
Qed.

Lemma proper_peel_cont_eutt_r : forall (E : Type -> Type) (R S : Type) 
                             (b: ibranch E R) (t t': itree E S) (s : S),
    (t ≈ t')%itree -> (peel_cont b t s ≈ peel_cont b t' s)%itree.
Proof. 
  intros E R S. unfold peel_cont. intros b t t' _.
  revert b t t'. pcofix CIH. intros. pfold. punfold H0. red in H0. dependent induction H0.
  - rewrite <- x. rewrite <- x0. red. cbn. apply eqitF_r_refl.
  - rewrite <- x. rewrite <- x0. red. destruct (observe b) eqn : Heqb; cbn.
    + constructor. right. rewrite <- Heqb. eapply CIH. pclearbot. auto.
    + constructor. right. eapply CIH. pclearbot. auto.
    + constructor. right. rewrite <- Heqb. eapply CIH; pclearbot; auto.
  - rewrite <- x. rewrite <- x0. pclearbot. destruct (observe b) eqn : Heqb; red; cbn.
    + apply eqitF_r_refl.
    + constructor. rewrite x. rewrite x0. right. eapply CIH.
      pfold. red. rewrite <- x. rewrite <- x0. constructor. intros.
      left. auto.
    + destruct e0; cbn.
      * unfold observe. cbn. unfold peel_cont_vis. 
        destruct (classicT (A = u) ); try apply eqitF_r_refl.
        unfold eq_rect_r, eq_rect. remember (eq_sym e0) as He.
        dependent destruction He. cbn. constructor. intros. right.
        eapply CIH. auto.
      * apply eqitF_r_refl.
  - rewrite <- x. destruct (observe b) eqn : Heqb; red; cbn.
    + constructor; eauto. rewrite <- Heqb. eapply IHeqitF; eauto.
    + cbn. destruct (observe t') eqn : Heqt'; cbn.
      * constructor. left. eapply paco2_mon with (r := bot2); intuition.
        eapply peel_cont_ret_inv with (s := r0). pfold. auto.
      * constructor. right. eapply CIH; eauto. setoid_rewrite <- tau_eutt at 2.
        pfold. auto.
      * constructor. right. rewrite <- Heqt'. eapply CIH.
        pfold. red. rewrite Heqt'. auto.
    + rewrite <- Heqb. constructor; auto. eapply IHeqitF; eauto.
 - rewrite <- x. destruct (observe b) eqn : Heqb; red; cbn.
   + constructor; auto. rewrite <- Heqb. eapply IHeqitF; eauto.
   + destruct (observe t) eqn : Heqt; cbn.
     * constructor. left. eapply paco2_mon with (r := bot2); intuition. 
       enough (t0 ≈ peel_cont_ (observe t0) (observe t2) )%itree. auto.
       symmetry.
       eapply peel_cont_ret_inv with (s := r0). symmetry. pfold. auto.
     * constructor. right. eapply CIH. rewrite <- tau_eutt at 1. pfold. auto.
     * constructor. right. rewrite <- Heqt. eapply CIH.
       pfold. red. rewrite Heqt. auto.
   + rewrite <- Heqb. constructor; auto. eapply IHeqitF; eauto.
Qed.

Instance proper_eutt_peel_cont {E R S} : Proper (eutt eq ==> eutt eq ==> eq ==> eutt eq) (@peel_cont E R S).
Proof.
  repeat intro. subst. rewrite proper_peel_cont_eutt_l; eauto.
  rewrite proper_peel_cont_eutt_r; eauto. reflexivity.
Qed.
(*
Lemma peel_cont_bind : forall (E : Type -> Type) (R S : Type) (b : ibranch E S) (t : itree E R) (f : R -> itree E S),
    b ⊑ ITree.bind t f -> (ITree.bind (peel b t) (peel_cont b t) ≈ b)%itree.
Proof.
  intros E R S. pcofix CIH. intros. punfold H0. pfold. red. red in H0. cbn in *.
  unfold ITree.bind in H0. unfold ITree.bind. cbn in *.
  unfold observe at 1. cbn.
*)

Lemma vis_refine : forall (E : Type -> Type) (R S A : Type) (e : E A) (a : A) (f : R -> itree E S)
                   (k1: unit -> ibranch E S) (k2 : A -> itree E R) (k3 : unit -> ibranch E R),
    Vis (evans _ e a) k1 ⊑ ITree.bind (Vis e k2) f ->
        (peel (Vis (evans _ e a) k1) (Vis e k2) ≈ Vis (evans _ e a) k3)%itree -> 
        k1 tt ⊑ ITree.bind (k2 a) f.

        
Admitted.



Lemma peel_cont_refine_t : forall (E : Type -> Type) (R S : Type)
                  (b : ibranch E S) (t : itree E R) (f : R -> itree E S) (r : R)
     (HeuttEv : b ⊑ ITree.bind t f),
    can_converge r (peel b t) -> peel_cont b t r ⊑ f r.
Proof.
  intros. dependent induction H.
  - apply peel_ret_inv in H as Ht.
    rewrite Ht in HeuttEv. rewrite bind_ret in HeuttEv.
    rewrite Ht in H. 
    unfold peel_cont. cbn. rewrite peel_cont_ret_inv; eauto.
  - destruct e; try contradiction.
    

    (*  peel vis -> b vis and t vis plus some extra info
       this info should be info to tell that the cotinuations refine each other d*)
    (* break down structure of b and t*)
    (*t ≈ Vis e k0*)
    
    (* k tt ⊑  k0 ans >>= f*)
    (*b ≈ *)
    admit.
Admitted.


Lemma decompose_branch_refine_bind : forall (E : Type -> Type) (R S : Type)
                                       (b : ibranch E S) (t : itree E R) (f : R -> itree E S),
    b ⊑ t >>= f -> exists b', exists g', (ITree.bind b' g' ≈ b)%itree /\ b' ⊑ t.

Admitted.
