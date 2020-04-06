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

From Paco Require Import paco.

From Coq Require Import Morphisms
     Program.Equality
     Classes.RelationClasses
.


Require Import Classical_Prop.
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
    unfold eqit_ in *.
    cbn in *.
    remember (ITree.bind ma kab) as tl.
    assert (tl ≅ ITree.bind ma kab) by (subst; reflexivity).
    clear Heqtl.
    genobs tl tl'.
    remember (VisF e kxb) as tr.
    revert ma kab tl Heqtl' H0 kxb Heqtr.
    revert A.
    induction H.
    - intros; subst; inv Heqtr.
    - intros; subst; inv Heqtr.
    - intros; subst.
      rewrite unfold_bind in H0.
      destruct (observe ma) eqn: Hobma.
      + cbn in *; rewrite itree_eta in H0; rewrite <- Heqtl' in H0.
        right. exists r. split. rewrite itree_eta. rewrite Hobma. reflexivity.
        rewrite <- H0. apply eqit_Vis.
        unfold id in REL.
        unfold upaco2 in REL.
        intros.
        destruct (REL u0).
        * unfold eqit. unfold eqit_. intros. apply H.
        * inversion H.
      + cbn in *; rewrite itree_eta in H0; rewrite <- Heqtl' in H0.
        symmetry in H0.
        apply eqitree_inv_tau_vis in H0. contradiction.
      + cbn in *; rewrite itree_eta in H0; rewrite <- Heqtl' in H0.
        clear Heqtl'.
        left. unfold id in REL.
        unfold upaco2 in REL.
        setoid_rewrite itree_eta at 1.
        rewrite Hobma. clear Hobma.
        inv Heqtr.
        dependent destruction H3.
        dependent destruction H2.
        apply eq_itree_inv_vis in H0.
        edestruct H0 as (? & ? & ?).
        inv H. dependent destruction H5.
        dependent destruction H4.
        exists k. reflexivity.
    - intros. inv Heqtr.
      apply simpobs in Heqtl'. rewrite Heqtl' in H0; clear tl Heqtl'.
      rewrite unfold_bind in H0.
      destruct (observe ma) eqn: Hobma.
      + cbn in *.
        specialize (IHeqitF A ma (fun _ => t1) t1 eq_refl).
        edestruct IHeqitF as [a | a];[| reflexivity | | ].
        * setoid_rewrite itree_eta at 4.
          rewrite Hobma, Eq.bind_ret_l.
          reflexivity.
        * left. apply a.
        * right.
          destruct a.
          setoid_rewrite itree_eta in H1 at 1.
          rewrite Hobma in H1. destruct H1.
          apply eutt_inv_ret in H1; subst.
          setoid_rewrite itree_eta at 1.
          rewrite Hobma.
          rewrite <- tau_eutt in H2.
          rewrite H0 in H2.
          exists x. split; try assumption; reflexivity.
      + cbn in *. rewrite eqitree_Tau in H0.
        edestruct IHeqitF as [a | ?];[reflexivity | apply H0 | reflexivity | |].
        * left. setoid_rewrite itree_eta at 1.
          rewrite Hobma. setoid_rewrite tau_eutt at 1.
          assumption.
        * right. setoid_rewrite itree_eta at 1.
          rewrite Hobma. setoid_rewrite tau_eutt at 1.
          assumption.
      + exfalso. cbn in H0; apply eqitree_inv_tau_vis in H0; contradiction.
    - intros. inversion Heqtr.
  Qed.

End ITree_inversion_lemmas.

Section MayRet.

  (* We wish to be able to capture propositionally the set of values that a monadic computation can return *)

  (* A possible generic definition could be thought to be as follows:

  Inductive MayRet : forall {A}, m A -> A -> Prop :=
  | mayret_ret:  forall A (a : A),
      (* eqm (ret a) b -> *)
      MayRet (ret a) a
  | mayret_bind: forall A B (ma: m A) a (k: A -> m B) b,
      (* eqm c (bind ma k) -> *)
      MayRet ma a ->
      MayRet (k a) b ->
      MayRet (bind ma k) b.

    This definition is however too generic as it says nothing about the effects of the computation.
    For instance consider the following itree illustration.
    Given the usual event `Rd (x: loc): E nat`, considering the tree:
    t == Vis (Rd x) (fun n => ret n)
    Then with the def from Vellvm specialized to itrees, we have:
      forall n, MayRet t n
    While with the following generic definition, to the contrary, we cannot prove `MayRet t n` for any n.
   *)


  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.

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

      mayret_eqm :> forall {A: Type}, Proper (eqm ==> @eq A ==> iff) mayret;

      mayret_proper_strong :> forall {A B} (ma ma': m A),
          ma ≈ ma' ->
          forall (kb kb': A -> m B),
            (forall a, mayret ma a -> kb a ≈ kb' a) ->
            (bind ma kb) ≈ (bind ma' kb')
    }.

End MayRet.

Section TMayRet.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.

  Variable (T: (Type -> Type) -> (Type -> Type)).
  Context `{Monad (T m)}.
  
  Definition Id (A: Type) : Type := A.
  Context `{Monad (T Id)}.

  (* maybe take in a 3rd argument R, which is a Run
     function that can be applied to the T Id A monad to 
     extract the underlying 'a' value
     The semantics of tmayret then becomes "the T m A term
     returns the value that the T Id A term computes to under
     the provided Run function *)
  (* Is there some "runnable monad" type class? *)
    
  Class TMayRet: Type :=
    {
    tmayret: forall {A},
        T m A -> (T Id A) -> (T Id A -> A) -> Prop;

    run_m: forall {X}, T Id X -> X
    }.
  

  Class TMayRetCorrect `{TMayRet}: Prop :=
    {
    tmayret_ret_refl : forall {A} (a: A),
        tmayret (ret a) (ret a) run_m;

    tmayret_ret_inj  : forall {A} (a a': A),
        tmayret (ret a) (ret a') run_m -> a = a';

    tmayret_bind : forall {A B} (tma: T m A) (ktb: A -> T m B)
                          (tia: T Id A) (a: A) (b: B),
        tmayret tma (ret a) run_m ->
        tmayret (ktb (run_m (ret a))) (ret b) run_m ->
        tmayret (bind tma ktb) (ret b) run_m;

    tmayret_bind' : forall {A B} (tma: T m A) (ktb: A -> T m B)
                           b,
        tmayret (bind tma ktb) (ret b) run_m ->
        exists a, tmayret tma (ret a) run_m /\
                  tmayret (ktb (run_m (ret a))) (ret b) run_m;

    }.

End TMayRet.

(*
Section Instance_TMayRet_id.
  Variable m : Type -> Type.
  Context {EQM : EqM m}.
  Context {HM: Monad m}.

  (* The trivial monad transformer. *)
  Definition IdT (m: Type -> Type) : Type -> Type := m.
  Context `{Monad (IdT m)}.
  Context `{HTMM: Monad (IdT m)}.
  Context `{HTIM: Monad (IdT Id)}.
  

  Instance IdT_TMayRet: (TMayRet m IdT) :=
    {|
      tmayret :=
        fun A (ima: IdT m A) (iia: IdT Id A) => True
        (* Ignore this nonsensical definition *)
    |}.

  Instance IdT_TMayRetCorrect: TMayRetCorrect m IdT.
  split.
  intros A a. unfold ret.
  (* Just wanted to unfold ret to see if the correct returns were
     being used in the tmayret_ret_refl definition *)
  Abort.
End Instance_TMayRet_id.

 *)

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

  Lemma ITree_mayret_proper :
    forall {E : Type -> Type} {A : Type}, Proper (eqm ==> eq ==> iff) (@Returns E A).
  Proof.
    repeat intro.
    split; intros; subst; generalize dependent H.
    - revert y.
      induction H1.
      + intros. rewrite H in H0. clear H.
        constructor. symmetry. apply H0.
      + intros. rewrite H in H0.
        rewrite tau_eutt in H0.
        apply IHReturns in H0. apply H0.
      + intros. rewrite H in H0.
        econstructor 3. symmetry. apply H0. apply H1.
    - revert x.
      induction H1; intros; rewrite H in H0; clear H.
      + constructor. apply H0.
      + rewrite tau_eutt in H0.
        apply IHReturns in H0. apply H0.
      + econstructor 3. apply H0. apply H1.
  Qed.

  Section ReturnsBind.
    Context {E : Type -> Type} {R : Type}.

    Import ITreeNotations.
    Local Open Scope itree.

    Inductive eqit_Returns_bind_clo b1 b2 (r : itree E R -> itree E R -> Prop) :
      itree E R -> itree E R -> Prop :=
    | pbc_intro_h U (t1 t2: itree E U) (k1 k2: U -> itree E R)
                  (EQV: eqit eq b1 b2 t1 t2)
                  (REL: forall u, Returns t1 u -> r (k1 u) (k2 u))
      : eqit_Returns_bind_clo b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
    .
    Hint Constructors eqit_Returns_bind_clo.

    Lemma eqit_Returns_clo_bind b1 b2 vclo
          (MON: monotone2 vclo)
          (CMP: compose (eqitC eq b1 b2) vclo <3= compose vclo (eqitC eq b1 b2))
          (ID: id <3= vclo):
      eqit_Returns_bind_clo b1 b2 <3= gupaco2 (eqit_ eq b1 b2 vclo) (eqitC eq b1 b2).
    Proof.
      gcofix CIH. intros. destruct PR.
      guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; try (rewrite (itree_eta (x <- _;; _ x)), unfold_bind; reflexivity).
      punfold EQV. unfold_eqit.
      genobs t1 ot1.
      genobs t2 ot2.
      hinduction EQV before CIH; intros; pclearbot.
      - guclo eqit_clo_trans.
        econstructor; auto_ctrans_eq; try (rewrite <- !itree_eta; reflexivity).
        gbase; cbn.
        apply REL0.
        rewrite itree_eta, <- Heqot1; constructor; reflexivity.
      - gstep. econstructor.
        gbase.
        apply CIH.
        constructor; auto.
        intros u HR.
        apply REL0.
        rewrite itree_eta, <- Heqot1.
        econstructor 2; eauto; reflexivity.
      - gstep. econstructor.
        intros; apply ID; unfold id.
        gbase.
        apply CIH.
        constructor; auto.
        intros ? HR; apply REL0.
        rewrite itree_eta, <- Heqot1.
        econstructor 3; eauto; reflexivity.
      - destruct b1; try discriminate.
        guclo eqit_clo_trans.
        econstructor.
        3:{ eapply IHEQV; eauto.
            intros ? HR; apply REL.
            rewrite itree_eta, <- Heqot1; econstructor 2; eauto; reflexivity.
        }
        3,4:auto_ctrans_eq.
        2: reflexivity.
        eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
      - destruct b2; try discriminate.
        guclo eqit_clo_trans.
        econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
        eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
    Qed.

    Lemma eqit_Returns_bind' {S} b1 b2
          (t1 t2: itree E S) (k1 k2: S -> itree E R) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns t1 r -> eqit eq b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ eq b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof.
      intros. ginit. guclo eqit_Returns_clo_bind. unfold eqit in *.
      econstructor; eauto with paco.
    Qed.

  End ReturnsBind.

  Lemma ITree_mayret_strong_proper:
     forall (E : Type -> Type) (A B : Type) (ma ma' : itree E A),
       ma ≈ ma' ->
       forall kb kb' : A -> itree E B,
         (forall a : A, Returns ma a -> kb a ≈ kb' a) ->
         ITree.bind ma kb ≈ ITree.bind ma' kb'.
  Proof.
    intros E A B.
    pose proof (eqit_Returns_bind' (S := A) (R := B) (E := E) true true).
    intros. apply H. apply H0. apply H1.
  Qed.

  Instance ITree_mayret_correct E: @MayRetCorrect _ _ _ (ITree_mayret E).
  split; cbn.
  - intros. constructor. reflexivity.
  - apply (@ITree_mayret_inj E).
  - apply (@ITree_mayret_bind E).
  - apply (@ITree_mayret_bind_inv E).
  - apply (@ITree_mayret_proper E).
  - apply (@ITree_mayret_strong_proper E).
  Qed.

End Instance_MayRet.

Arguments mayret {m _} [A].

From ITree Require Import
     Basics.MonadState.

Import ITree.Basics.Basics.Monads.

Section Instance_MayRet_State.
  Variable m : Type -> Type.
  Variable S : Type.
  Context {EQM : EqM m}.
  Context {HM: Monad m}.
  Context {MR: MayRet m}.
  Context {MRC: MayRetCorrect m}.

  Instance StateT_MayRet: MayRet (stateT S m) :=
    {|
      mayret :=
        fun A (sma: stateT S m A) a =>
          exists si sf, mayret (sma si) (sf,a)
    |}.

  (* We need to know that our space of states is inhabited *)
  Hypothesis s: S.


  Instance StateT_MayRetCorrect: MayRetCorrect (stateT S m).
  split.
  - repeat intro.
    exists s, s; apply (mayret_ret_refl m).
  - repeat intro.
    destruct H as (si & sf & HMR).
    apply (mayret_ret_inj m) in HMR; inv HMR; reflexivity.
  - intros A B ma kb a b (si & sj & HMRma) (sj' & sf & HMRkb).
    exists si, sf.
    eapply (mayret_bind m).
    apply HMRma.
    cbn.
    (* This cannot hold *)
  Abort.

End Instance_MayRet_State.

Section Transformer.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.
  Context {ITERM : MonadIter m}.
  Context {MAYR : MayRet m}.
  Context {HEQP: @EqMProps m _ EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.

  Definition closed_eqm {A} (P: m A -> Prop) := forall a a', eqm a a' -> (P a <-> P a').

  Arguments exist {A P}.
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

  Definition ret_f := (fun A (a : A) (ma : m A) => eqm ma (ret a)).

  Lemma ret_f_closed :
    forall A (a : A), closed_eqm (ret_f A a).
  Proof.
    split; intros; unfold ret_f in *;
      rewrite H0 in *; assumption.
  Defined.

  (* Notice that the continuation only checks membership to the set continuation over values that may be returned.
     The following example illustrates why removing this restriction is incompatible with the [bind_ret_l] monadic law.

     Consider the [PA := ret true], i.e. the singleton set (up-to ≈) containing the pure computation [ret true].
     Consider the continuation [K := fun b => if b then ret 0 else (fun _ => False)], i.e. the continuation that on true
     returns the singleton set (up-to ≈) containing the pure computation [ret 0], and on false the empty set.

     By [bind_ret_l], we _should_ have [bind PA K ≈ K true = ret 0].
     But if our definition require to provide a continuation whose member belongs to each set, then we need
     to find a value for [k true] that belongs to [K true = ∅], which is absurd.
     Hence we would have [bind PA K ≈ ∅].

     For this reason, we are trying to restrict the requirement to values that are actually returned by the computation.
   *)
  Definition bind_f :=
    fun A B (PA : PropTM A) (K : A -> PropTM B) mb =>
      exists (ma : m A) (kb : A -> m B),
        !PA ma /\ (forall a, mayret ma a -> !(K a) (kb a)) /\
        Monad.eqm mb (bind ma kb).

  (* Definition bind_f := *)
  (*   fun A B (PA : PropTM A) (K : A -> PropTM B) mb => *)
  (*     exists (ma : m A) (kb : {a: A | mayret ma a} -> m B), *)
  (*       !PA ma /\ (forall a, !(K a) (kb a)) /\ *)
  (*       Monad.eqm mb (bind ma (lift kb default)). *)

  Lemma bind_f_closed:
    forall A B (PA : PropTM A) (K : A -> PropTM B),
      closed_eqm (bind_f A B PA K).
  Proof.
    split; intros;
      (destruct H1 as (ma & kb & HPA & HK & HEQa); exists ma, kb;
       rewrite H0 in *; repeat (split; try assumption)).
  Defined.

  Global Instance Monad_PropTM : Monad (PropTM) :=
    {|
      ret:= fun A (a: A) => (exist (ret_f A a) (ret_f_closed A a))
      ; bind := fun A B (PA : PropTM A) (K : A -> PropTM B)=>
                  exist (bind_f A B PA K) (bind_f_closed A B PA K)
      |}.

  Lemma monad_iter_closed:
    forall (R I : Type) (step : I -> PropTM (I + R)) (i : I),
      closed_eqm
        (fun r : m R =>
           exists step' : I -> m (I + R),
             (forall j : I, ! (step j) (step' j)) /\
             eqm (m := m) (CategoryOps.iter step' i) r).
  Proof.
    intros R I step i.
    intros m1 m2 eqm12; split; intros (step' & ISIN & EQ);
      (exists step'; split; auto);
      [rewrite <- eqm12 | rewrite eqm12]; auto.
  Qed.

  (* Global Instance MonadIter_PropTM : MonadIter PropTM. *)
  (*  exact (fun R I step i => *)
  (*           exist (fun (r: m R) => exists (step': I -> m (I + R)%type), *)
  (*                    (forall j, !(step j) (step' j)) /\ *)
  (*                    (eqm (m := m)(CategoryOps.iter step' i) r)) *)
  (*                 (monad_iter_closed R I step i)). *)
  (* Defined. *)
  Import CatNotations.
  Local Open Scope cat_scope.

  Lemma monad_iter_closed':
    forall (R I : Type) (step : I -> PropTM (I + R)) (i : I),
      closed_eqm
        (fun r : m R =>
           exists step' : I * nat -> m (I + R),
             (forall (n : nat) (j : I), ! (step j) (step' (j, n))) /\
             eqm (m := m) (let body :=
                  fun '(x, k) =>
                    bind (step' (x, k))
                         (fun ir : I + R =>
                            match ir with
                            | inl i0 => ret (inl (i0, S k))
                            | inr r0 => ret (inr r0)
                            end) in
              CategoryOps.iter body (i, 0)) r).
  Proof.
    intros R I step i.
    intros m1 m2 eqm12; split; intros (step' & ISIN & EQ);
      (exists step'; split; auto);
      [rewrite <- eqm12 | rewrite eqm12]; auto.
  Qed.

  Global Instance MonadIter_PropTM : MonadIter PropTM.
  refine (fun (R I : Type) (step : I -> PropTM (I + R)) (i : I) =>
            exist (fun r : m R =>
           exists step' : I * nat -> m (I + R),
             (forall (n : nat) (j : I), ! (step j) (step' (j, n))) /\
             eqm (m := m) (let body :=
                  fun '(x, k) =>
                    bind (step' (x, k))
                         (fun ir : I + R =>
                            match ir with
                            | inl i0 => ret (inl (i0, S k))
                            | inr r0 => ret (inr r0)
                            end) in
                           CategoryOps.iter body (i, 0)) r)
                  (monad_iter_closed' R I step i)).
  Defined.

  Global Instance Iter_PropTM : Iter (Kleisli PropTM) sum.
  Proof.
    eapply Iter_Kleisli.
  Defined.

  Context {CM: Iterative (Kleisli m) sum}.

  Global Instance Proper_Iter_PropTM : forall a b, @Proper (Kleisli PropTM a (a + b) -> Kleisli PropTM a b) (eq2 ==> eq2) iter.
  Proof.
    destruct CM.
    repeat red in iterative_proper_iter.
    repeat red.
    intros A B x y Heq a mx my Heq0.
    split; repeat red; intros; red in H0;
        edestruct H0 as (? & ? & ?); clear H0;
        exists x0; split;
          [ | rewrite Heq0 in H2; assumption | | rewrite <- Heq0 in H2; assumption ];
          intros; repeat red in Heq; assert (Hj: x0 (j, n) ≈ x0 (j, n)) by reflexivity;
            specialize (Heq j (x0 (j, n)) (x0 (j, n)) Hj); clear Hj;
              destruct Heq; [apply H0 in H1 | apply H3 in H1] ; apply H1.
  Qed.

  Lemma indexed_iter_unfold :
    forall (A B : Type) (x y : m B)
      (step : A * nat -> m (A + B)) (a : A),
      iter (C := Kleisli m) (fun '(x, k) => bind (step (x, k)) (fun ir : A + B =>
        match ir with
        | inl i0 => ret (inl (i0, S k))
        | inr r0 => ret (inr r0)
        end)) (a, 0) ≈
      bind (m := m) (step (a, 0))
      (fun y0 : A + B =>
       bind match y0 with
          | inl i0 => ret (inl (i0, 1))
          | inr r0 => ret (inr r0)
          end
       (fun y1 : A * nat + B =>
        case_ (C := Kleisli m) (bif := sum)
          (iter (C := Kleisli m)
             (fun '(x0, k) =>
              bind (step (x0, k))
                (fun ir : A + B =>
                 match ir with
                 | inl i0 => ret (inl (i0, S k))
                 | inr r0 => ret (inr r0)
                 end))) (id_ B) y1)).
  Proof.
    intros.
    destruct CM. rewrite iterative_unfold.
    unfold cat, Cat_Kleisli. destruct HMLAWS.
    rewrite bind_bind. reflexivity.
  Qed.

  Definition g {a b : Type} (x0 : a * nat -> m (a + b)) (a1 : a)
    := (fun '(x, k) =>
            bind (x0 (x, k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, k))
                    | inr r0 => ret (inr r0)
                    end)).

  Definition f {a b : Type} : a * nat  -> m (a * nat + b) := fun '(x, k) => ret (inl ((x, S k))).

  Lemma iter_succ_dinatural:
    forall {a b : Type} (x0 : a * nat -> m (a + b)) (a1 : a),
      iter (C := Kleisli m) (bif := sum)
           (f >>> case_ (g x0 a1) inr_)
       ⩯
       f >>> case_ (iter (C := Kleisli m) (bif := sum) ((g x0 a1) >>> (case_ f inr_))) (id_ _).
  Proof.
    intros. rewrite iter_dinatural. reflexivity.
  Qed.

  Definition foo {a b : Type} (x0 : a * nat -> m (a + b))  :=
     fun '(x1, k) =>
             bind (m := m)
               (bind (m := m) (x0 (x1, k))
                   (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, S (S k)))
                    | inr r0 => ret (inr r0)
                    end))  (fun y : a * nat + b =>
                              case_ (C := Kleisli m)
                                    (fun '(x0, k) => ret (inl (x0, S k))) inr_ y) .
  
  Lemma iter_eq_start_index:
    forall (a b : Type) (x0 : a * nat -> m (a + b)) (a1 : a),
      iter (C := Kleisli m) (bif := sum)
        (fun '(x, k) =>
            bind (x0 (x, S k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, S k))
                    | inr r0 => ret (inr r0)
                    end)) (a1, 0)
        ≈ iter (C := Kleisli m) (bif := sum)
        (fun '(x', k) =>
            bind (x0 (x', k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, S k))
                    | inr r0 => ret (inr r0)
                    end)) (a1, 1).
  Proof.
    intros a b x0 a1.
    pose proof (iter_succ_dinatural x0 a1).
    specialize (H0 (a1, 0)).
    unfold f at 1, g at 1 in H0.
    unfold cat at 1, Cat_Kleisli at 1 in H0.
    match goal with
    | H : ?body1 ≈ _ |- ?body2 ≈ _ => remember body1 as s1;
                                                 remember body2 as s2
    end.
    assert (s1 ≈ s2). {
      subst.
      match goal with
      | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as k1;
                                            remember body2 as k2
      end.
      assert (iter k1 ⩯ iter k2). {
        eapply iterative_proper_iter.
        subst. do 3 red. intros.
        destruct a0; rewrite bind_ret_l; cbn.
        reflexivity.
      }
      do 3 red in H1.
      apply H1.
    }
    rewrite <- H1. subst. clear H1. rewrite H0.
    unfold f, g.
    unfold cat, Cat_Kleisli. rewrite bind_ret_l.
    cbn.
    match goal with
    | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as i1; remember body2 as i2
     end.
    assert (iter i1 ⩯ iter i2). {
      eapply iterative_proper_iter.
      subst.
      do 3 red. intros.
      destruct a0. rewrite bind_bind.
      eapply Proper_bind. reflexivity.
      do 2 red. intros. destruct a2;
      rewrite bind_ret_l; cbn; reflexivity.
    }
    do 3 red in H1.
    apply H1.
  Qed.
  
  Global Instance IterUnfold_PropTM : IterUnfold (Kleisli PropTM) sum.
  Proof with (repeat red).
    unfold IterUnfold.
    intros a b f... intros a0 x y Heq.
    unfold cat, Cat_Kleisli, iter, Iter_PropTM, Iter_Kleisli, Basics.iter, MonadIter_Prop.
    simpl proj1_sig; split; intros.
    - edestruct H0 as (? & ? & ?)... clear H0.
      rewrite Heq in H2; setoid_rewrite <- H2; clear H2.
      exists (x0 (a0, 0)).
      exists (fun y0 : a + b =>
            bind
              match y0 with
              | inl i0 => ret (inl (i0, 1))
              | inr r0 => ret (inr r0)
              end
              (fun y1 : a * nat + b =>
               case_ (C := Kleisli m) (bif := sum)
                 (iter (C := Kleisli m) (bif := sum)
                    (fun '(x', k) =>
                     bind (x0 (x', k))
                       (fun ir : a + b =>
                        match ir with
                        | inl i0 => ret (inl (i0, S k))
                        | inr r0 => ret (inr r0)
                        end))) (id_ b) y1)).
      split; [ apply H1 | split; intros ].
      + destruct a1.
        * exists (fun '(ax, nx) => x0 (ax, S nx)).
          split.
          -- intros k. apply (H1 (S k)).
          -- rewrite bind_ret_l. cbn. apply iter_eq_start_index.
        * do 10 red. rewrite bind_ret_l. cbn. reflexivity.
      + destruct CM; setoid_rewrite iterative_unfold.
        unfold cat, Cat_Kleisli; destruct HMLAWS; rewrite bind_bind.
        reflexivity.
    - intros. edestruct H0 as (mab & k & Hf & Hcat & Heqy); clear H0.
      rewrite <- Heq in Heqy; clear Heq.
      unfold MonadIter_PropTM in Hcat.
      setoid_rewrite Heqy; clear Heqy.
      (* Note: need to introduce classical reasoning here. *)
  Admitted.

  Global Instance IterNatural_PropTM : IterNatural (Kleisli PropTM) sum.
  Proof.
    destruct CM.
    clear iterative_unfold; clear iterative_dinatural; clear iterative_codiagonal;
      clear iterative_proper_iter.
    unfold IterNatural.
  Admitted.

  Global Instance IterDinatural_PropTM : IterDinatural (Kleisli PropTM) sum.
  Proof.
    destruct CM.
    clear iterative_unfold; clear iterative_natural; clear iterative_codiagonal;
      clear iterative_proper_iter.
    unfold IterDinatural.
  Admitted.

  Global Instance IterCodiagonal_PropTM : IterCodiagonal (Kleisli PropTM) sum.
  Proof. Admitted.

  Global Instance Iterative_PropTM : Iterative (Kleisli PropTM) sum.
  Proof.
    constructor; typeclasses eauto.
  Qed.

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
      cbn.
      exists (ret a), (fun _ => y).
      split.
      + cbn. reflexivity.
      + split.
        * intros a' mRet. eapply mayret_ret_inj in mRet.
          subst. auto. apply MAYRC.
        * rewrite bind_ret_l. reflexivity.
  Qed.

  (* Stronger Proper? *)
  Lemma Proper_bind_strong:
    forall {A B} (ma ma': m A),
      ma ≈ ma' ->
      forall (kb kb': A -> m B),
        (forall a, mayret ma a -> kb a ≈ kb' a) ->
        (bind ma kb) ≈ (bind ma' kb').
  Admitted.

  (* Stronger monad law? *)
  Lemma bind_mayret_ret: forall {A} ma kb,
      (forall a : A, mayret ma a -> kb a ≈ ret a) ->
      bind ma kb ≈ ma.
  Proof.
    intros.
    setoid_rewrite <- bind_ret_r at 3.
    apply Proper_bind_strong; [reflexivity | auto].
  Qed.

  Lemma ret_bind_r:
    forall A (ma : PropTM m A),
      eqm (bind ma (fun x => ret x)) ma.
  Proof.
    intros A PTA.
    cbn in *. unfold bind_f in *. unfold ret_f in *. cbn.
    split.
    - rewrite H0; clear H0; cbn in *; intros comp.
      destruct comp as (ma & kb & Hpta & Hreteq & Hbind).
      rewrite Hbind. clear Hbind.
      rewrite bind_mayret_ret; auto.
    - rewrite H0; clear x H0; cbn in *; intros comp.
      exists y, (fun a => ret a).
      repeat split; auto.
      intros; reflexivity.
      rewrite bind_ret_r; reflexivity.
  Qed.

  Require Import Logic.ClassicalChoice.

  (* YZ: The following discusses the possible use of the axiom of choice to prove the associativity of the bind operator
         Since we are considering two consecutive binds, the computation of interest is divided into three parts, of
         respective types [A], [A -> m B], [B -> m C]. We refer part i for the third i, and [i-j] for portions covering
         several thirds.

     The crux of the problem when associating to the left is as follows.
     We need to provide a computation in [m] covering computation 1-2.
     We have the part 1 [ma: m A], as well as an hypothesis of the form:
     H: ∀ a:A, mayret ma a -> ∃ (mb: m B), R a mb

     If we forget about [mayret] for a moment, our hypothesis becomes:
     H: forall a:A, ∃ (mb: m B), R a mb
     By applying to [H] the functional axiom of choice, i.e.:
     choice:  ∀ (A B : Type) (R : A->B->Prop),
              (∀ x : A, ∃ y : B, R x y) ->
              ∃ f : A->B, (∀ x : A, R x (f x)).
     H: exists (f: A -> m B), ∀ a:A, R a (f a)
     And we can hence provide the sought computation 1-2 as [bind ma f].

     Now let's plug back [mayret], can we still work around. It feels like two things may be useful:
     1) Assume the monad to be pointed, i.e. assume the existence of a family of elements [⊥: forall A, m A].
        I don't yet foresee where we'd need to know anything about it, but [spin] seems to be a natural candidate over [itree E].
     2) Assume the axiom of _strong_ excluded middle, i.e.
        classicT: forall (P : Prop), {P} + {~ P}
        so that the definition of the continuation can pattern match on the existence of a value returned by the first part of the computation
        (i.e. a generalization on pattern matching on its termination).

     However we might also be able to rather rephrase [H] by pushing [classically] the precondition under the existential by providing
     [⊥] over the complement, that is proving for instance:
     H': ∀ a: A, ∃ (mb : m B) (kb: B -> m C),
                   (~ mayret ma a /\ mb = ⊥) \/
                   (mayret ma a /\ ! (KAB a) mb /\ (forall a0 : B, mayret mb a0 -> ! (KBC a0) (kb a0)) /\ kamC a ≈ bind mb kb)

     We try this approach below:
   *)

  Lemma bind_bind:
    forall A B C (ma : PropTM m A) (mab : A -> PropTM m B)
           (mbc : B -> PropTM m C),
      eqm (bind (bind ma mab) mbc) (bind ma (fun x => bind (mab x) mbc)).
  Proof.
    intros A B C PTA KAB KBC mac mac' EQ; rewrite <- EQ; clear mac' EQ.
    split.
    - intros Hleft. cbn in *. unfold bind_f in *.
      destruct Hleft as (mb & kbmC & comp & HBmrtcont & Hbindy).
      cbn in *.
      destruct comp as (ma & kamB & Hpta & HAmrtcont & Hbindmb).
      exists ma. exists (fun a: A => bind (kamB a) kbmC).
      split; auto. split.
      + intros a mrtA. exists (kamB a). exists kbmC. split; auto.
        split; try reflexivity.
        intros b mrtB. apply HBmrtcont. rewrite Hbindmb.
        eapply mayret_bind; eauto.
      + rewrite Hbindy. rewrite Hbindmb.
        apply bind_bind.
    - intros (ma & kamC & Hpta & comp & Hbindy).
      cbn in *; unfold bind_f in *; cbn in *.

      (* Let's assume the existence of ⊥ *)
      assert (bot: forall A, m A) by admit.
      (* Let's push the precondition under the existential *)
      assert (comp': forall a: A,
                 exists (mb : m B) (kb: B -> m C),
                   (~ mayret ma a /\ mb = bot B) \/
                   (mayret ma a /\ ! (KAB a) mb /\ (forall a0 : B, mayret mb a0 -> ! (KBC a0) (kb a0)) /\ kamC a ≈ bind mb kb)
             ).
      {
        intros a.
        destruct (classic (mayret ma a)) as [MAY | MAY_NOT].
        destruct (comp a MAY) as (mb & kb & HYP).
        exists mb, kb; right; auto.
        exists (bot _), (fun _ => bot _); left; auto.
      }
      clear comp.

      (* We can now use [choice] to extract our continuation for part 2 of type [A -> m B] *)
      apply choice in comp'.
      destruct comp' as (kAmB & comp).
      (* So that we can now provide the part 1-2 of the computation *)
      exists (bind ma kAmB).
      (* We now however need to provide the part 3 of the computation, things get a bit confusing *)
      (* We _could_ apply [choice] a second time to also derive a function for this part, giving us a family
         of such continuations indexed by [A] *)
      generalize comp; intros comp'.
      apply choice in comp; destruct comp as (kBmC & comp).
      (* In all account it feels like we need to case analysis as to whether there exists a value returned by [ma] *)
      destruct (classic (exists a, mayret ma a)) as [[a aRET] | NORET].
      {
        (* Here we have such a value, we can feed it to either of our hypotheses *)
        (* The one that used choice gives us a continuation, and eliminate the left branch in the [comp]: *)
        specialize (comp a); destruct comp as [(abs & _) | (_ & comp)]; [contradiction |].
        (* The original one of course gives the same thing, I dunno what I was thinking *)
        clear kBmC comp.
        specialize (comp' a); destruct comp' as (kBmC & [(abs & _) | (_ & IN2 & CONT2 & EQ13)]); [contradiction |].
        (* Hence we can feed it *)
        exists kBmC.
        repeat split.
        - (* We are now splitting part 1-2, we should have everything we need *)
          exists ma, kAmB.
          repeat split.
          + assumption.
          + (* This is awkward. I used my case analysis earlier to fix [a: A], but need now to work with others *)
            intros a' a'RET.
            admit.
          + reflexivity.
        - intros b bRET.
          apply CONT2.
          eapply mayret_bind' in bRET; eauto.
          (* Similar to previously. I can get some [a: A] over which [kAmB a] satisfies my goal, but I fixed it *)
          admit.
        - rewrite bind_bind.
          rewrite Hbindy.
          (* And once again, EQ13 is too specialized *)
          admit.
      }
      {
        (* Here, part 1 never returns, but I'm kinda lost as to what that means at the moment... *)
        (* Right, we can prove that [forall a: A, kAmB a = ⊥]. So the always diverging continuation should be fitting *)
        exists (fun _ => bot _).
        repeat split.
        - exists ma, (fun _ => bot _).
          repeat split; auto.
          + intros a aRET; exfalso; apply NORET; eexists; eauto.
          + (* At least extentionally true, if not completely true *)
            admit.
        - intros b bRET.
          (* Not sure *)
          admit.
        - rewrite Hbindy.
          rewrite bind_bind.
          (* Some work to be done here, that's where we need to axiomatize [⊥] I think *)
  Admitted.

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
