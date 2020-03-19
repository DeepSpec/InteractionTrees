From ExtLib Require Import
     Structures.Monad.
From ITree Require Import
     ITree
     Eq.Eq
     ITreeMonad
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Monad.

From Coq Require Import Morphisms
     Program.Equality
     Classes.RelationClasses.

Require Import Paco.paco.

(* See [PropT.v] in the Vellvm repo for the exact framework to follow with respect to typeclasses, as well as a proof of most monad laws for [PropTM (itree E)] *)

Section ITree_inversion_lemmas.

  (* To move to Eq/Eq.v eventually *)

  (************************ Missing structural inversion lemmas *************************)

  Lemma eqit_inv_ret_vis: forall {E X R1 R2 RR} b1 b2 (r: R1) (e: E X) k,
      @eqit E R1 R2 RR b1 b2 (Ret r) (Vis e k) -> False.
  Proof.
    intros.
    punfold H; inv H.
  Qed.

  Lemma eutt_inv_ret_vis: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
  Proof.
    intros; eapply eqit_inv_ret_vis; eauto.
  Qed.

  Lemma eqitree_inv_ret_vis: forall {X Y E} (x: X) (e: E Y) k, Ret x ≅ Vis e k -> False.
  Proof.
    intros; eapply eqit_inv_ret_vis; eauto.
  Qed.

  Lemma eqit_inv_tau_vis: forall {E X R1 R2 RR} b2 (e: E X) k t,
      @eqit E R1 R2 RR false b2 (Tau t) (Vis e k) -> False.
  Proof.
    intros.
    punfold H; inv H.
    inv CHECK.
  Qed.

  Lemma eqit_inv_vis_tau: forall {E X R1 R2 RR} b1 (e: E X) k t,
      @eqit E R1 R2 RR b1 false (Vis e k) (Tau t) -> False.
  Proof.
    intros.
    punfold H; inv H.
    inv CHECK.
  Qed.

  Lemma euttge_inv_tau_vis: forall {E A B} (e: E A) (k : A -> itree E B) (a : itree E B), Vis e k ≳ Tau a -> False.
  Proof.
    intros; eapply eqit_inv_vis_tau; eauto.
  Qed.

  Lemma eqitree_inv_tau_vis: forall {E A B} (e: E A) (k : A -> itree E B) (a : itree E B), Tau a ≅ Vis e k -> False.
  Proof.
    intros; eapply eqit_inv_tau_vis; eauto.
  Qed.

  Lemma eqit_inv_ret_tau: forall {E R1 R2 RR} b1 (r: R1) t,
      @eqit E R1 R2 RR b1 false (Ret r) (Tau t) -> False.
  Proof.
    intros.
    punfold H; inv H.
    inv CHECK.
  Qed.

  Lemma eqit_inv_tau_ret: forall {E R1 R2 RR} b2 (r: R2) t,
      @eqit E R1 R2 RR false b2 (Tau t) (Ret r) -> False.
  Proof.
    intros.
    punfold H; inv H.
    inv CHECK.
  Qed.

  Lemma euttge_inv_ret_tau: forall {E A} (r : A) (a : itree E A),
    Ret r ≳ Tau a -> False.
  Proof.
    intros; eapply eqit_inv_ret_tau; eauto.
  Qed.

  Lemma eqitree_inv_ret_tau: forall {E A} (r : A) (a : itree E A),
    Ret r ≅ Tau a -> False.
  Proof.
    intros; eapply eqit_inv_ret_tau; eauto.
  Qed.

  Lemma eutt_inv_ret {E R} r1 r2 :
    (Ret r1: itree E R) ≈ (Ret r2) -> r1 = r2.
  Proof.
    intros; eapply eqit_inv_ret; eauto.
  Qed.

  Lemma eqitree_inv_ret {E R} r1 r2 :
    (Ret r1: itree E R) ≅ (Ret r2) -> r1 = r2.
  Proof.
    intros; eapply eqit_inv_ret; eauto.
  Qed.

  Lemma eutt_Tau {E R} (t1 t2 : itree E R):
     Tau t1 ≈ Tau t2 <-> t1 ≈ t2.
  Proof.
    apply eqit_Tau.
  Qed.

  Lemma eqitree_Tau {E R} (t1 t2 : itree E R):
     Tau t1 ≅ Tau t2 <-> t1 ≅ t2.
  Proof.
    apply eqit_Tau.
  Qed.

  (************************ Inversion lemmas for bind *************************)

  (* Likely needless, to remove later if it's still the case *)
  Lemma eutt_bind_ret_inv':
    forall {E A B} (ma : itree E A) (kb : A -> itree E B) a b,
      ITree.bind ma kb ≈ Ret b -> ma ≈ Ret a -> kb a ≈ Ret b.
  Proof.
    intros.
    punfold H.
    unfold eqit_ in *.
    cbn in *.
    remember (observe (ITree.bind ma kb)) as tl.
    assert (ITree.bind ma kb ≈ kb a).
    rewrite H0. rewrite Eq.bind_ret_l. reflexivity.
    rewrite <- H1. rewrite itree_eta.
    remember (RetF b) as tr.
    revert Heqtl Heqtr.
    induction H; intros; subst.
    - rewrite <- Heqtl.
      reflexivity.
    - rewrite <- Heqtl.
      cbv. pstep. constructor.
      apply REL.
    - rewrite <- Heqtl.
      cbv. pstep. constructor.
      apply REL.
    - rewrite <- Heqtl.
      cbv. pstep. constructor.
      + auto.
      + apply H.
    - inversion Heqtr.
  Qed.

  Lemma eqit_inv_bind_ret:
    forall {E X R1 R2 RR} b1 b2
      (ma : itree E X) (kb : X -> itree E R1) (b: R2),
      @eqit E R1 R2 RR b1 b2 (ITree.bind ma kb) (Ret b) ->
      exists a, @eqit E X X eq b1 b2 ma (Ret a) /\
           @eqit E R1 R2 RR b1 b2 (kb a) (Ret b).
  Proof.
    intros.
    punfold H.
    unfold eqit_ in *.
    cbn in *.
    remember (ITree.bind ma kb) as tl.
    assert (tl ≅ ITree.bind ma kb) by (subst; reflexivity).
    clear Heqtl.
    genobs tl tl'.
    remember (RetF b) as tr.
    revert ma kb tl Heqtl' H0 b Heqtr.
    induction H.
    - intros; subst.
      inv Heqtr.
      destruct (observe tl) eqn: Hobtl; inv Heqtl'.
      rewrite unfold_bind in H0.
      destruct (observe ma) eqn: Hobma.
      * exists r0. split. rewrite <- Hobma. tau_steps. reflexivity.
        cbn in *. rewrite <- H0. rewrite itree_eta, Hobtl.
        apply eqit_Ret; auto.
      * cbn in H0. rewrite itree_eta in H0. rewrite Hobtl in H0.
        apply eqitree_inv_ret_tau in H0. contradiction.
      * cbn in H0. rewrite itree_eta, Hobtl in H0.
        apply eqitree_inv_ret_vis in H0. contradiction.
    - intros. inversion Heqtr.
    - intros. inversion Heqtr.
    - intros. subst.
      apply simpobs in Heqtl'. rewrite Heqtl' in H0; clear tl Heqtl'.
      rewrite unfold_bind in H0.
      destruct (observe ma) eqn: Hobma.
      + cbn in *.
        specialize (IHeqitF ma (fun _ => t1) t1 eq_refl).
        edestruct IHeqitF as (a & ? & ?);[| reflexivity |].
        * setoid_rewrite itree_eta at 4.
          rewrite Hobma, Eq.bind_ret_l.
          reflexivity.
        * exists a; split; auto.
          rewrite itree_eta, Hobma in H1.
          apply eqit_inv_ret in H1; subst.
          rewrite <- H0.
          destruct b1; [| inv CHECK].
          apply eqit_tauL; auto.
      + cbn in *. rewrite eqitree_Tau in H0.
        edestruct IHeqitF as (a & ? & ?);[reflexivity | apply H0 | reflexivity |].
        exists a; split; [| assumption].
        destruct b1; [| inv CHECK].
        rewrite itree_eta, Hobma; apply eqit_tauL; auto.
      + exfalso. cbn in H0; apply eqitree_inv_tau_vis in H0; contradiction.
    - intros. inversion Heqtr.
  Qed.

  Lemma eutt_inv_bind_ret:
    forall {E A B} (ma : itree E A) (kb : A -> itree E B) b,
      ITree.bind ma kb ≈ Ret b ->
      exists a, ma ≈ Ret a /\ kb a ≈ Ret b.
  Proof.
    intros; apply eqit_inv_bind_ret; auto.
  Qed.

  Lemma eqitree_inv_bind_ret:
    forall {E A B} (ma : itree E A) (kb : A -> itree E B) b,
      ITree.bind ma kb ≅ Ret b ->
      exists a, ma ≅ Ret a /\ kb a ≅ Ret b.
  Proof.
    intros; apply eqit_inv_bind_ret; auto.
  Qed.

  Lemma eutt_inv_bind_vis:
    forall {A B E X} (ma : itree E A) (kab : A -> itree E B) (e : E X)
      (kxb : X -> itree E B),
      ITree.bind ma kab ≈ Vis e kxb ->
      (exists (kca : X -> itree E A), (ma ≈ Vis e kca)) \/
      (exists (a : A), (ma ≈ Ret a) /\ (kab a ≈ Vis e kxb)).
  Proof.
    intros. punfold H.
  Admitted.


End ITree_inversion_lemmas.

Section MayRet.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.

  (*
    Given the usual event `Rd (x: loc): E nat`, considering the tree:
    t == Vis (Rd x) (fun n => ret n)
    Then with the def from Vellvm specialized to itrees, we have:
      forall n, MayRet t n
    While with the following generic definition, to the contrary, we cannot prove `MayRet t n` for any n.
   *)

  (*
  Inductive MayRet : forall {A}, m A -> A -> Prop :=
  | mayret_ret:  forall A (a : A),
      (* eqm (ret a) b -> *)
      MayRet (ret a) a
  | mayret_bind: forall A B (ma: m A) a (k: A -> m B) b,
      (* eqm c (bind ma k) -> *)
      MayRet ma a ->
      MayRet (k a) b ->
      MayRet (bind ma k) b.
   *)


  Class MayRet: Type :=
    {
      mayret: forall {A}, m A -> A -> Prop
    }.

  Class MayRetCorrect `{MayRet}: Prop :=
    {
      mayret_ret_refl : forall {A} (a: A), mayret (ret a) a;
      mayret_ret_inj  : forall {A} (a a': A), mayret (ret a) a' -> a = a';

      mayret_bind : forall {A B} (ma: m A) (kb: A -> m B) a b,
          mayret ma a ->
          mayret (kb a) b ->
          mayret (bind ma kb) b;

      mayret_bind' : forall {A B} (ma: m A) (kb: A -> m B) b,
          mayret (bind ma kb) b ->
          exists a, mayret ma a /\ mayret (kb a) b;

      mayret_eqm :> forall {A: Type}, Proper (eqm ==> @eq A ==> iff) mayret
    }.

End MayRet.

Section Instance_MayRet.

  Inductive Returns {E} {A: Type} : itree E A -> A -> Prop :=
  | ReturnsRet: forall a t,    t ≈ Ret a -> Returns t a
  | ReturnsTau: forall a t t', t' ≅ Tau t -> Returns t a -> Returns t' a
  | ReturnsVis: forall a {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns (k x) a -> Returns t a
  .
  Hint Constructors Returns.

  Instance ITree_mayret E: MayRet (itree E) :=
    {| mayret := @Returns E |}.


  Instance Returns_eutt {E A}: Proper (eutt eq ==> @eq A ==> iff) (@Returns E A).
  Proof.
    repeat intro; split; intros HRet; subst.
    - revert y H. induction HRet; intros.
      constructor; rewrite <- H, H0; reflexivity.
      apply IHHRet, eqit_inv_tauL; auto.
      rewrite <- H0, H; reflexivity.
      econstructor 3; [rewrite <- H0, H; reflexivity | apply IHHRet; reflexivity].
    - revert x H; induction HRet; intros ? EQ.
      constructor; rewrite EQ; eauto.
      apply IHHRet, eqit_inv_tauR; auto.
      rewrite EQ, H; reflexivity.
      econstructor 3; [rewrite EQ, H; reflexivity | apply IHHRet; reflexivity].
  Qed.

  (* ITree mayret 'Correctness' lemmas. *)

  Lemma ITree_mayret_inj:
    forall {E: Type -> Type} {A : Type} (a a' : A),
      @Returns E A (Ret a) a' -> a = a'.
  Proof.
    intros.
    remember (Ret a) as t.
    assert (Heq: t ≈ Ret a) by (rewrite Heqt; reflexivity).
    revert Heq. clear Heqt.
    induction H; subst.
    + intros Heq; rewrite H in Heq.
      apply eutt_inv_ret in Heq; auto.
    + intros.
      apply IHReturns.
      rewrite <- Heq, H, tau_eutt; reflexivity.
    + intros; exfalso.
      rewrite H in Heq; symmetry in Heq; apply eutt_inv_ret_vis in Heq; auto.
  Qed.

  Lemma ITree_mayret_bind:
    forall {E A B} (ma : itree E A) (kb : A -> itree E B) (a : A) (b : B),
    Returns ma a ->
    Returns (kb a) b ->
    Returns (ITree.bind ma kb) b.
  Proof.
    induction 1. cbn in *; intros.
    + rewrite H, Eq.bind_ret_l; auto.
    + intros.
      rewrite H, tau_eutt.
      apply IHReturns, H1.
    + intros.
      rewrite H, bind_vis.
      eapply (@ReturnsVis E B b X e x).
      * reflexivity.
      * apply IHReturns; assumption.
  Qed.

  Lemma eutt_ret_returns: forall E X (a: X) (t: itree E X),
      t ≈ ret a ->
      Returns t a.
  Proof.
    intros.
    punfold H; cbn in H.
    unfold eqit_ in *; cbn in *.
    remember (observe t) as tl.
    remember (RetF a) as tr.
    revert t Heqtl Heqtr.
    induction H; intros; subst.
    - econstructor 1.
      rewrite <- Heqtr, Heqtl.
      rewrite itree_eta; reflexivity.
    - discriminate.
    - discriminate.
    - econstructor 2; auto.
      rewrite itree_eta, Heqtl; reflexivity.
    - discriminate.
  Qed.

  Lemma ITree_mayret_bind_inv:
    forall {E} (A B : Type) (ma : itree E A) (kb : A -> itree E B) (b : B),
      Returns (bind ma kb) b ->
      exists a : A, Returns ma a /\ Returns (kb a) b.
  Proof.
    cbn. intros E A B ma kb b H.
    remember (ITree.bind ma kb) as t.
    assert (Heq: t ≈ ITree.bind ma kb) by (rewrite Heqt; reflexivity).
    revert Heq. clear Heqt.
    intros. symmetry in Heq.
    generalize dependent ma.
    generalize dependent kb.
    revert A.
    induction H; intros.
    + rewrite H in Heq.
      apply (eutt_inv_bind_ret ma kb a) in Heq.
      destruct Heq as [? [? ?]].
      exists x. split. apply eutt_ret_returns in H0.
      apply H0. apply eutt_ret_returns in H1.
      apply H1.
    + eapply IHReturns.
      rewrite H in Heq.
      rewrite tau_eutt in Heq. apply Heq.
    + rewrite H in Heq. clear H.
      generalize Heq. intros Heq'.
      apply eutt_inv_bind_vis in Heq.
      destruct Heq.
      * destruct H as (kma & Heqma). setoid_rewrite Heqma.
        edestruct (IHReturns A kb (kma x)).
        setoid_rewrite Heqma in Heq'.
        rewrite bind_vis in Heq'.
        apply eqit_inv_vis in Heq'. destruct Heq'.
        specialize (H1 x).
        rewrite H1. reflexivity.
        exists x0. split.
        econstructor 3. reflexivity. apply H. apply H.
      * destruct H as (a' & (Heqma & Heqk)).
        edestruct (IHReturns X k (Ret x)).
        rewrite Eq.bind_ret_l. reflexivity.
        exists a'. split. constructor. apply Heqma. econstructor 3.
        apply Heqk. apply H0.
  Qed.

  Instance ITree_mayret_correct E: @MayRetCorrect _ _ _ (ITree_mayret E).
  split; cbn.
  - intros. constructor. reflexivity.
  - apply (@ITree_mayret_inj E).
  - apply (@ITree_mayret_bind E).
  - apply (@ITree_mayret_bind_inv E).
  - Admitted.

End Instance_MayRet.

Arguments mayret {m _} [A].

Section Transformer.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.
  Context {ITERM : MonadIter m}.
  Context {MAYR : MayRet m}.
  Context {HEQP: @EqMProps m _ EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.

  Definition closed_eqm {A} (P: m A -> Prop) := forall a a', eqm a a' -> (P a <-> P a').

  (* Design choice 1: closed or not by construction? *)
  Definition PropTM : Type -> Type :=
    fun A => {P: m A -> Prop | closed_eqm P}.

  Notation "! P" := (proj1_sig P) (at level 5).

  Definition eqm1: forall A, PropTM A -> PropTM A -> Prop:=
    fun A PA PA' => forall a, !PA a <-> !PA' a.

  Definition eqm2: forall A, PropTM A -> PropTM A -> Prop:=
    fun A PA PA' => forall x y, eqm x y -> (!PA x <-> !PA' y).

  Definition eqm3: forall A, PropTM A -> PropTM A -> Prop :=
    fun _ P Q => (forall a, !P a -> exists a', eqm a a' /\ !Q a') /\
              (forall a, !Q a -> exists a', eqm a a' /\ !P a').

  Global Instance EqM_PropTM : EqM PropTM := eqm2.

  (* Let's assume M = id monad

mb = kb ma

fun b =>
!PA a /\ K a b

 ma: m A ~ ma: A
kb : A -> m B ~ kb: A -> B
bind ma kb ~ kb ma
MayRet ma a ~ a = ma

PA ma /\ (K a mb)
   *)

  Definition bind_f :=
    fun A B (PA : PropTM A) (K : A -> PropTM B) mb =>
      exists (ma : m A) (kb : A -> m B),
        !PA ma /\ (forall a, mayret ma a -> !(K a) (kb a)) /\
        Monad.eqm mb (bind ma kb).

  Lemma bind_f_closed:
    forall A B (PA : PropTM A) (K : A -> PropTM B),
      closed_eqm (bind_f A B PA K).
  Proof.
    split; intros;
      (destruct H1 as (ma & kb & HPA & HK & HEQa); exists ma, kb;
       rewrite H0 in *; repeat (split; try assumption)).
  Defined.


  Definition ret_f := (fun A (a : A) (ma : m A) => eqm ma (ret a)).

  Lemma ret_f_closed :
    forall A (a : A), closed_eqm (ret_f A a).
  Proof.
    split; intros; unfold ret_f in *;
      rewrite H0 in *; assumption.
  Defined.


  Global Instance Monad_PropTM : Monad (PropTM) :=
    {|
      ret:= fun A (a: A) => (exist _ (ret_f A a) (ret_f_closed A a))
      ; bind := fun A B (PA : PropTM A) (K : A -> PropTM B)=>
                  exist _ (bind_f A B PA K) (bind_f_closed A B PA K)
      |}.

 (* Global Instance MonadIter_Prop : MonadIter PropTM := *)
 (*    fun R I step i r => *)
 (*      exists (step': I -> m (I + R)%type), *)
 (*        (forall j, step j (step' j)) /\ CategoryOps.iter step' i = r. *)

  (* What is the connection (precisely) with this continuation monad? *)
  (* Definition ContM: Type -> Type := fun A => (A -> Prop) -> Prop. *)

(* ?p : "Morphisms.Proper (Morphisms.respectful eqm (Basics.flip Basics.impl)) ! (f a)" *)

End Transformer.


(* IY: [For Kento]: Monad laws for PropTM!
                    Let me know if you have any questions. :-) *)
Section Laws.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.
  Context {ITERM : MonadIter m}.
  Context {MAYR : MayRet m}.
  Context {MAYRC : MayRetCorrect m}.
  Context {HEQP: @EqMProps m _ EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.

  Notation "! P" := (proj1_sig P) (at level 5).

  Instance eqm_MonadProp_Proper {A} (P: PropTM m A) : Proper (@eqm _ _ A ==> iff) ! P.
  Proof.
    cbv. intros x y Heq.
    split; intros Heqa;
      destruct P; eapply c; eauto; rewrite Heq; reflexivity.
  Qed.

  Lemma ret_bind_l:
    forall A B (f : A -> PropTM m B) (a : A),
      eqm (bind (ret a) f) (f a).
  Proof.
    intros A B F a x y Heq. split.
    - intros comp.
      destruct comp as (ma & kb & maRet & goal & xBind).
      cbn in *. unfold ret_f in *.
      rewrite <- Heq, xBind, maRet, bind_ret_l.
      apply goal.
      rewrite maRet. eapply (mayret_ret_refl).
      auto.
    - intros fApp.
      rewrite Heq. cbn in *. unfold bind_f in *. unfold ret_f in *.
      exists (ret a). exists (fun _ => y).
      split.
      + cbn. reflexivity.
      + split.
        * intros a' mRet. eapply mayret_ret_inj in mRet.
          subst. auto. apply MAYRC.
        * rewrite bind_ret_l. reflexivity.
 Qed.

  Lemma ret_bind_r:
    forall A (ma : PropTM m A),
      eqm (bind ma (fun x => ret x)) ma.
  Proof.
    intros A PTA.
    cbn in *. unfold bind_f in *. unfold ret_f in *.
    split; rewrite H0; clear H0; cbn in *; intros comp.
    - destruct comp as (ma & kb & Hpta & Hreteq & Hbind).
      rewrite Hbind.

      assert (nonEmpty: exists a, mayret ma a).
      { admit. (* I feel like this should follow from (! PTA ma)
        that ma has to return some a. *) }
      destruct nonEmpty as (a & mRet). eapply Hreteq in mRet.
      admit.
    - exists y. exists (fun x => ret x).
      split; auto. split.
      + reflexivity.
      + rewrite bind_ret_r. reflexivity.
  Admitted.

  Lemma bind_bind:
    forall A B C (ma : PropTM m A) (mab : A -> PropTM m B)
           (mbc : B -> PropTM m C),
      eqm (bind (bind ma mab) mbc) (bind ma (fun x => bind (mab x) mbc)).
  Proof. Admitted.

  Lemma respect_bind :
  forall a b : Type, Proper (eqm ==> pointwise_relation a eqm ==> @eqm (PropTM m) _ b) bind.
  Proof.
  Admitted.

  Global Instance PropTM_Laws : @MonadLaws (PropTM m) _ _.
  split. apply ret_bind_l.
  apply ret_bind_r. apply bind_bind.
  apply respect_bind.
  Qed.

End Laws.
