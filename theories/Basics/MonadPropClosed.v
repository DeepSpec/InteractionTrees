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

      mayret_bind: forall {A B} (ma: m A) (kb: A -> m B) a b,
          mayret ma a ->
          mayret (kb a) b ->
          mayret (bind ma kb) b;

      mayret_bind': forall {A B} (ma: m A) (kb: A -> m B) b,
          mayret (bind ma kb) b ->
          exists a, mayret ma a /\ mayret (kb a) b;

      mayret_eqm: forall {A: Type}, Proper (eqm ==> @eq A ==> iff) mayret
    }.

End MayRet.

Section Instance_MayRet.

  Inductive Returns {E} {A: Type} : itree E A -> A -> Prop :=
  | ReturnsRet: forall a t, t ≈ Ret a -> Returns t a
  | ReturnsTau: forall a t, Returns t a -> Returns (Tau t) a
  | ReturnsVis: forall a {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns (k x) a -> Returns t a
  .
  Hint Constructors Returns.

  Instance ITree_mayret E: MayRet (itree E) :=
    {| mayret := @Returns E |}.

  Require Import Paco.paco.
  Lemma eutt_ret_vis_abs: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
  Proof.
    intros.
    punfold H; inv H.
  Qed.

  Instance Returns_eutt {E A}: Proper (eutt eq ==> @eq A ==> iff) (@Returns E A).
  Proof.
    repeat intro; split; intros HRet; subst.
    - revert y H. induction HRet; intros.
      constructor; rewrite <- H, H0; reflexivity.
      apply IHHRet, eqit_inv_tauL; auto.
      econstructor 3; [rewrite <- H0, H; reflexivity | apply IHHRet; reflexivity].
    - revert x H; induction HRet; intros ? EQ.
      constructor; rewrite EQ; eauto.
      apply IHHRet, eqit_inv_tauR; auto.
      econstructor 3; [rewrite EQ, H; reflexivity | apply IHHRet; reflexivity].
  Qed.

  Instance ITree_mayret_correct E: @MayRetCorrect _ _ _ (ITree_mayret E).
  split.
  - intros. constructor.
    reflexivity.
  - intros. inversion H; subst.
    + apply eqit_inv_ret in H0; assumption.
    + apply eutt_ret_vis_abs in H0; contradiction.
  - induction 1.
    + intros. rewrite H.
      cbn. rewrite Eq.bind_ret_l.
      apply H0.
    + intros. rewrite tau_eutt.
      apply IHReturns, H0.
    + rewrite H. intros.
      cbn. rewrite bind_vis.
      eapply (@ReturnsVis _ _ _ _ _ a).
      reflexivity.




End Instance_MayRet.


  (*
    Goal MayRet t 0.
    change t with (bind (trigger (Rd x)
    apply mayret_bind.
    2: auto.
    (* MayRet (trigger (Rd x) 0) *)


   *)

  Definition ret_f := (fun A (a : A) (ma : m A) => eqm ma (ret a)).

  Lemma ret_f_closed :
    forall A (a : A), closed_eqm (ret_f A a).
  Proof.
    split; intros; unfold ret_f in *;
      rewrite H0 in *; assumption.
  Defined.

  Definition bind_f :=
    fun A B (PA : PropTM A) (K : A -> PropTM B) mb =>
      exists (ma : m A) (kb : A -> m B),
        !PA ma /\ (forall a, MayRet ma a -> !(K a) (kb a)) /\
        Monad.eqm mb (bind ma kb).



End MayRet.


Section Transformer.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.
  Context {ITERM : MonadIter m}.
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
    fun _ P Q => (forall a, !P a -> exists a', eqm a a' /\ !Q a) /\
              (forall a, !Q a -> exists a', eqm a a' /\ !P a).

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

Section BAR.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqM m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP: @EqMProps m _ EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.

  Notation "! P" := (proj1_sig P) (at level 5).

  Instance eqm_MonadProp_Proper {A} (P: PropTM m A) : Proper (@eqm _ _ A ==> iff) ! P.
  Proof.
    cbv. intros x y Heq.
    split; intros Heqa;
      destruct P; eapply c; eauto; rewrite Heq; reflexivity.
  Qed.

  Arguments MayRet [m _ A] _ _.
  Axiom return_ret_inv: forall A (a a': A), eqm (ret a) (ret a') -> a = a'.

  Lemma MayRetret_Eq: forall {A} (a b: A), MayRet (ret a) b -> a = b.
  Proof.
    intros ? ? ? ?.
    (* inversion H0; subst. *)
    dependent induction H0.
    - apply return_ret_inv.
      symmetry. rewrite x; reflexivity.

    reflexivity.
    remember (ret a) as ra.
    revert Heqra.
    induction h0.
    intros ->.
    - apply return_ret_inv. symmetry; auto.
    - intros ->.
      apply IHMayRet2.
      inversion H0_; subst.

      Set Nested Proofs Allowed.
      Lemma ret_eq_bind :
        forall A B (a: A) (ma: m A) (k : A -> m B), eqm (ret a) (bind ma k) ->






  Lemma ret_bind:
    forall A B (a : A) (f : A -> PropTM m B),
      eqm (bind (ret a) f) (f a).
  Proof.
    intros A B a f b b' HEqb. split.
    - intros Hb. cbn in *. unfold bind_f in Hb.
      cbn in *.
      destruct Hb as (ma & kb & Hma & Hk & Heqb').
      rewrite HEqb in *.
      rewrite Heqb'.
      unfold ret_f in Hma. rewrite Hma.
      rewrite bind_ret_l. apply Hk.
      apply mayret_ret. symmetry. apply Hma.
    - intros Hb.
      exists (ret a), (fun x => b'). cbn. repeat split.
      + unfold ret_f. reflexivity.
      + intros a0 Hmr.
        remember (ret a) as ra.
        revert Heqra. intros.
        apply return_ret_inv in H
        et Nested Proofs Allowed.
        Require Import Coq.Program.Equality.
          (*
  H0 : ret a0 ≈ ret a
*)
          -
        clear - Hmr.
        exfalso.
        clear -Hmr.
        dependent induction Hmr.
        admit.
        clear IHHmr1 IHHmr2.

        inversion Hmr; subst.
    unfold Monad_PropTM.
    intro mb. split.
    - intros (ma & kb & HRet & HBind & HEq).
      rewrite HEq.
End Transformer.
