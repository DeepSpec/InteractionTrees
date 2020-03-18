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
     Program.Equality.

(* See [PropT.v] in the Vellvm repo for the exact framework to follow with respect to typeclasses, as well as a proof of most monad laws for [PropTM (itree E)] *)

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

  Require Import Paco.paco.

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

  Lemma eutt_ret_vis_abs: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
  Proof.
    intros.
    punfold H; inv H.
  Qed.

  Lemma eutt_bind_ret_abs:
    forall {E A B} (ma : itree E A) (kb : A -> itree E B) b,
      ITree.bind ma kb ≈ Ret b -> exists a, ma ≈ Ret a /\ kb a ≈ Ret b.
  Proof.
    Admitted. 

  (*
  Inductive foo E X: itree E X -> Prop :=
  | ISRet: forall a t, observe t = RetF a -> foo E X t
  | ISTau: forall t t', observe t = TauF t' -> foo E X t' -> foo E X t.

  Lemma bar: forall E X (a: X) (t: itree E X),
      t ≈ ret a ->
      foo E X t.
  Proof.
    intros.
    punfold H.
    cbn in H.
    unfold eqit_ in *.
    cbn in *.
    remember (observe t) as tl.
    remember (RetF a) as tr.
    revert t Heqtl Heqtr.
    induction H; intros; subst.
    - econstructor 1.
      rewrite <- Heqtl.
      cbn. reflexivity.
    - discriminate.
    - discriminate.
    - econstructor 2; auto.
      rewrite Heqtl; reflexivity.
    - discriminate.
  Qed.
   *)

  Lemma eutt_ret_returns: forall E X (a: X) (t: itree E X),
      t ≈ ret a ->
      Returns t a.
  Proof.
    intros.
    punfold H.
    cbn in H.
    unfold eqit_ in *.
    cbn in *.
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

  Instance ITree_mayret_correct E: @MayRetCorrect _ _ _ (ITree_mayret E).
  split.
  - intros. constructor.
    reflexivity.
  - intros. inversion H; subst.
    + apply eqit_inv_ret in H0; assumption.
    + apply eutt_ret_vis_abs in H0; contradiction.
  - (* mayret_bind *)
    induction 1.
    + intros. rewrite H.
      cbn. rewrite Eq.bind_ret_l.
      apply H0.
    + intros. rewrite tau_eutt.
      apply IHReturns, H0.
    + rewrite H. intros.
      cbn. rewrite bind_vis.
      eapply (@ReturnsVis E B b X e x).
      * reflexivity.
      * apply IHReturns. assumption.
  - (* mayret_bind' *)
    cbn. intros A B ma kb b H.
    remember (ITree.bind ma kb) as t.
    assert (Heq: t ≈ ITree.bind ma kb) by (rewrite Heqt; reflexivity).
    revert Heq. clear Heqt.
    induction H; intros.
    + rewrite H in Heq. clear H.
      symmetry in Heq.
      eapply eutt_bind_ret_abs in Heq.
      destruct Heq as [? [? ?]].
      exists x. rewrite H, H0.
      split; constructor; reflexivity.
    + apply IHReturns. rewrite <- Heq.
      symmetry. apply tau_eutt.
    + apply IHReturns. clear IHReturns.
      rewrite <- Heq. admit. 
  - (* Proper instance *)
    intros. constructor.
    + subst. induction 1.
      * rewrite <- H. rewrite H0. constructor.
        reflexivity.
      * apply IHReturns. rewrite tau_eutt in H.
        apply H.
      * rewrite H in H0. clear H.
        rewrite H0 in *. clear H0.
        apply IHReturns.
        inversion H1; subst. rewrite H.
        -- admit.
        -- admit.
        -- rewrite H.
        eapply ReturnsVis in H1.
      Admitted.

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
  Admitted.

  Lemma ret_bind_r:
    forall A (ma : PropTM m A),
      eqm (bind ma (fun x => ret x)) ma.
  Proof.
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
