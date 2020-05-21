
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Typ_Class2
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
     Basics.Monad
     Basics.HeterogeneousRelations
.

Import CatNotations.
Open Scope cat_scope.

Section MonadPropT.

  Context {M : typ -> typ}.
  Context {M_Monad : Monad typ_proper M}.
  Context {EqM: EqmR M} {EqmR : EqmR_OK M} {EqmRMonad : EqmRMonad M}.

  (* Old PropT Definition. *)
    (* {| *)
    (*   Ty := { p : M X -> Prop | Proper (equalE (M X) ==> iff) p }; *)
    (*   equal := *)
    (*     fun PA1 PA2 => *)
    (*       forall (ma : M X), ` PA1 ma <-> ` PA2 ma; *)
    (*   equal_PER := PropT_PER_equal X *)
    (* |}. *)

  Definition prop_typ : typ := Typ (iff).

  (* TODO: For later, maybe : prove exponential? *)
  Definition PropT (X : typ) : typ := (M X) ~=~> prop_typ.


  Goal forall (X : typ), equalE (PropT X) = equalE (PropT X).
    repeat intro. cbn. Abort.

  Notation "-=->!" := (exist _) (right associativity, at level 50).

  (* IY: Is there a better generalized Ltac for this? *)
  Ltac unfold_cat :=
     unfold cat, cat_typ_proper, eq2, eq2_typ_proper; cbn.

  Tactic Notation "unfold_cat" "in" hyp(H) :=
    unfold cat, cat_typ_proper, eq2, eq2_typ_proper in H; cbn in H.

  (* TODO : Automate properness proofs. *)
  Ltac find_proper :=
    match goal with
    | |- Proper (equalE ?A ==> iff) _ => apply Proper_equal_partial
    end.

  Local Obligation Tactic := program_simpl; try find_proper.

  Program Definition ret_ {A : typ} : A -> PropT A :=
    fun a => (-=->! (equal (ret @ a))) _.

  Program Definition retP {A : typ} : A -=-> PropT A :=
    -=->! ret_ _.
  Next Obligation.
  repeat red. intros x y H a1 a2 H0.
  split; intros.
  - rewrite <- H0.
    unfold ret_ in *. cbn.
    etransitivity. apply eq2_Reflexive. symmetry.
    eassumption. eassumption.
  - rewrite H0. unfold ret_ in *. cbn.
    etransitivity. apply eq2_Reflexive.
    eassumption. eassumption.
  Defined.

  (* Bind definition. *)
  Definition prop_agrees {A : typ} : relationH (A) (A ~=~> prop_typ) :=
    fun (x : A) (P : A ~=~> prop_typ) => P @ x.

  Definition agrees {A B : typ} (ma : M A) (kb : A -=-> M B) (k : A -=-> PropT B) :=
    let kb' : M A -=-> M (M B) := (monad_fmap M A (M B) kb) in
    let k'  : M A -=-> M (PropT B) := (monad_fmap M A (PropT B) k) in
    @eqmR M _ (M B) (M B ~=~> prop_typ) prop_agrees (kb' @ ma) (k' @ ma).

  Lemma agrees_ret :
    forall {A B : typ} (ma : M A) (kb :  A -=-> M B) (k : A -=-> PropT B),
    forall x, agrees ma kb k /\ ma == (ret @ x) -> (k @ x) @ (kb @ x).
  Proof. Admitted.

  Program Definition bind_ {A B : typ} (k : A -=-> PropT B) : PropT A -> PropT B :=
    fun (PA : PropT A) => fun (mb : M B) =>
                         (exists (ma : M A) (kb : A -=-> M B), ma ∈ M A /\
                             PA @ ma /\ bind kb @ ma == mb /\ agrees ma kb k).
  Next Obligation.
    epose proof @Proper_equal_partial.
    repeat red. intros x y EQ. split; intros H'.
    - edestruct H' as (ma & kb & HP & Hb & Agr).
      exists ma, kb. split ; [ | split]; try assumption.
      rewrite <- EQ. assumption.
    - edestruct H' as (ma & kb & HP & Hb & Agr).
      exists ma, kb. split ; [ | split]; try assumption.
      rewrite EQ. assumption.
  Defined.

  Ltac apply_proper A :=
    eapply (@Proper_typ_proper_app _ _ _ _ A).

  Program Definition bindP {A B : typ} (k : A -=-> PropT B) : PropT A -=-> PropT B :=
    -=->! (bind_ k) _.
  Next Obligation.
    intros Pma Pma' EQ mb mb' EQ'.
    split; intros; unfold bind_ in *.
    - edestruct H as (ma & kb & HP & Hb & Agr); clear H.
      exists ma, kb.
      rewrite <- EQ'. split; [ | split ] ; try assumption.
      apply_proper EQ. apply HP. apply Hb.
    - edestruct H as (ma & kb & Hma & HP & Hb & Agr).
      exists ma, kb.
      rewrite EQ'. split; [ | split ; [ | split ]] ; try assumption.
      apply_proper EQ; eassumption.
  Defined.

  Instance PropT_Monad : Monad typ_proper PropT :=
    {|
      ret := @retP;
      bind := @bindP
    |}.

  Ltac PER_reflexivity := etransitivity; [ | symmetry ]; eassumption.

  Lemma ret_equal :
    forall {A : typ} (x y: A), x == y -> ret @ x == ret @ x.
  Proof.
    intros.
    match goal with
    | |- ?r @ _ == _ => remember r as r'
    end.
    assert (Eq2 : r' ⩯ r') by reflexivity.
    apply_proper Eq2. PER_reflexivity.
  Qed.

  (* ==== Monad Laws for PropT ====================================================== *)
  Lemma bind_ret_l_ : forall (a b : typ) (f : a -=-> (PropT b)),
    ret >>> bind f ⩯ f.
  Proof with eauto.
  intros A B k x y EQ mb mb' EQ'.
  split; unfold bind_.

  - intros H.
    assert (Eq2 : k ⩯ k) by reflexivity.
    apply_proper Eq2. symmetry. apply EQ. symmetry. apply EQ'.
    cbn in H.
    edestruct H as (ma & kb & H'); clear H.
    edestruct H' as (Hm & Hret & Hbind & Agr); clear H'.
    rewrite <- Hbind. rewrite <- Hret. epose proof bind_ret_l as Hbr.
    unfold_cat in Hbr; rewrite Hbr.
    pose proof (agrees_ret ma kb k x) as Hagr.
    apply Hagr. split; [ | symmetry ]; eassumption. PER_reflexivity.

  - intros H.
    exists (ret @ x).
    eexists ?[kb].
    split; [ eapply ret_equal; eassumption | split; [ eapply ret_equal; eassumption | split ]].
    + pose proof (bind_ret_l (M := M) (a := A)) as Hbr.
      unfold_cat in Hbr; rewrite Hbr. 2 : apply EQ. rewrite EQ'.
      Unshelve. 2 : {
        refine (-=->! (fun x => mb') _).
        do 2 red. intros. symmetry in EQ'; PER_reflexivity.
      }
      cbn. symmetry in EQ'; PER_reflexivity.
    + unfold agrees. unfold monad_fmap.
      (* IY: Something is fishy here.. *)
      eapply eqmR_bind_ProperH...
      rewrite eqmR_equal. eapply ret_equal...
      cbn.
      intros; cbn; apply eqmR_ret...
      unfold prop_agrees.
  Admitted.

  Lemma propT_bind_ret_r : forall a : typ,
    bind ret ⩯ id_ (PropT a).
  Proof.
    cbn. red. unfold eq2_typ_proper.
    intros a x y Hx Hy Hxy ma. cbn.
    unfold bind_ty_fn. split.
    - intros.
      edestruct H as (ma' & kb & Hma & EQ & Agr).
      apply Hxy.

      (* TODO: Proper instance. *)
      assert (HP : Proper (equalE (M a) ==> iff) (` x)). admit.
      rewrite EQ. epose proof bind_ret_r as Hbr.
      unfold_cat in Hbr.

      (* Use monad reflexivity. *)
      pose proof (monad_reflexivity a ma') as Refl.
      specialize (Hbr ma' ma' Refl Refl Refl).

      (* TODO: Proper instance that depends on Agrees. *)
      (* Agr : agrees a a ma' kb ret_propT *)
      assert (H' : (equalE (M a) ((` (bind ret)) ma') ma' <-> equalE (M a) ((` (bind kb) ma')) ma')). admit.
      rewrite H' in Hbr. rewrite Hbr. apply Hma.
    - intros.
      eexists ?[ma]; eexists ?[kb].
      split ; [ | split].

      + (* TODO : Proper instance. *)
        assert (HP : Proper (equalE (PropT a) ==> iff) (fun x => (` x) ma)). admit.
        eapply HP. apply Hxy. apply H.

      + epose proof bind_ret_r as Hbr.
        unfold_cat in Hbr.

        (* Use monad reflexivity. *)
        pose proof (monad_reflexivity a ma) as Refl.
        specialize (Hbr ma ma Refl Refl Refl).
        symmetry. apply Hbr.

      + unfold agrees. intros a1 a2 Ha1 Ha2 EQ Hret.
        unfold ret_ty in Hret. cbn in Hret. unfold ret_ty_fn in Hret.
        unfold ret_propT. cbn. unfold ret_ty_fn. apply monad_reflexivity.
  Admitted.


  Lemma propT_bind_bind :
    forall (a b c : typ) (f : typ_proper a (PropT b)) (g : typ_proper b (PropT c)),
      bind f >>> bind g ⩯ bind (f >>> bind g).
  Proof.
    cbn. red. unfold eq2_typ_proper.
    intros a b c f g x y Hx Hy Hxy. cbn. intros mc.
    unfold bind_ty_fn. split.
    - intros H.
      edestruct H as (mb & kbc & Hmb & EQ & Agr); clear H.
      unfold bind_ty, bind_ty_fn in Hmb. cbn in Hmb.
      edestruct Hmb as (ma & kab & Hma & EQ' & Agr'); clear Hmb.
      exists ma. eexists ?[kac].
      split ; [ | split].

      + assert (HP : forall ma, Proper (equalE (PropT a) ==> iff) (fun x => (` x) ma)). admit.
        eapply HP. symmetry. apply Hxy. apply Hma.
      + rewrite EQ.
        epose proof bind_bind as Hbb.
        specialize (Hbb kab kbc).
        unfold_cat in Hbb.
        pose proof (monad_reflexivity a ma) as Refl.
        specialize (Hbb ma ma Refl Refl Refl). rewrite <- EQ' in Hbb.
        rewrite Hbb. apply monad_reflexivity.
      + unfold agrees. intros a1 a2 Ha1 Ha2 EQ'' Hret. cbn.
        unfold bind_ty_fn.
        unfold ret_ty in Hret. cbn in Hret. unfold ret_ty_fn in Hret.
        exists mb; eexists ?[kb].
        split; [ | split].
        * rewrite EQ'.
          rewrite <- Hret.
          epose proof bind_ret_l.
          unfold_cat in H. rewrite H. 2 : apply Ha1. 2 : apply Ha2. 2 : apply EQ''.
          unfold agrees in Agr'.

          assert (HP: Proper (equalE a ==> iff) (fun x' => (` ((` f) x')) ((`kab) a2))). {
            admit.
          }
          eapply HP. apply EQ''. eapply Agr'. apply Ha2. apply Ha1. symmetry. apply EQ''.
          eapply ret_proper. symmetry. apply EQ''. apply Hret.
        * rewrite <- EQ. clear EQ.
          epose proof bind_bind as Hbb.
          specialize (Hbb kab kbc).
          unfold_cat in Hbb.
          pose proof (monad_reflexivity a ma) as Refl.
          specialize (Hbb ma ma Refl Refl Refl). rewrite <- Hret in Hbb.
          epose proof bind_ret_l as bind_ret_l. unfold_cat in bind_ret_l.
          rewrite bind_ret_l in Hbb; clear bind_ret_l.
          2 : assumption. 2 : apply Ha2. 2 : assumption.
          rewrite <- EQ'' in Hbb. rewrite Hbb; clear Hbb.
          rewrite Hret.
          match goal with
          | |- equalE _ ((` (bind ?K)) _) _ => remember K as F
          end.

          (* TODO: Proper instance that depends on Agrees. *)
          (* Agr : agrees a a ma' kb ret_propT *)
          (* assert (H' : (equalE (M a) ((` (bind ret)) ma') ma' <-> equalE (M a) ((` (bind kb) ma')) ma')). admit. *)
  Admitted.

  Instance PropT_MonadLaws : MonadLaws PropT_Monad.
  constructor.
  - apply propT_bind_ret_l.
  - apply propT_bind_ret_r.
  - apply propT_bind_bind.
  Admitted.

End MonadPropT.

(* Outdated sketches. *)
  (* Lemma transport_refl_feq_PM: forall {X : typ}, *)
  (*     Reflexive (equalE X) -> Reflexive (feq_PM X). *)
  (* Proof. *)
  (*   intros X eqx T H. *)
  (*   repeat red. *)
  (*   tauto. *)
  (* Qed. *)

  (* Lemma transport_symm_feq_PM : forall {X : typ}, *)
  (*     Symmetric (equalE X) -> Symmetric (feq_PM X). *)
  (* Proof. *)
  (*   repeat red. intros X H x y H0 ma H1. *)
  (*   split. Admitted. *)

  (* Lemma transport_symm_feq : *)
  (*   forall {X : typ}, (Symmetric (equalE X) -> Symmetric feq). *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)

  (* Lemma transport_trans_feq : *)
  (*   forall {X : typ}, (Transitive (equalE X) -> Transitive feq). *)
  (* Proof. *)
  (*   intros. red in H. *)
  (* Admitted. *)

  (* Program Definition ret_PM {A : typ} `{Symmetric A (equalE A)} `{Transitive A (equalE A)} (a : A) : @PropT A := *)
  (*   exist _ (fun (x:M A) => feq (ret a) x) _. *)
  (* Next Obligation. *)
  (*   repeat red. *)
  (*   intros. split. intros. eapply transitivity. eassumption. eassumption. *)
  (*   intros. eapply transitivity. eassumption. *)
  (*   apply (transport_symm_feq H). assumption. *)
  (*   Unshelve. apply transport_trans_feq. assumption. *)
  (*   Unshelve. apply transport_trans_feq. assumption. *)
  (* Defined. *)


(*  
  Global Instance monad_return_PM : @MonadReturn PM A _ _ := @ret_PM.
  
  Definition bind_PM (m : PM A) (f : A -> PM B) : PM B := 
    fun (b:B) =>
      exists (a:A), eqa a a /\ m a /\ f a b.

  Global Instance monad_bind_PM : @MonadBind PM _ _ _ _ TA TB := @bind_PM.
    
  Global Instance functor_PM : Functor PM.
  unfold Functor. unfold PM.
  exact (fun A eqa P Q => forall (a b:A), eqa a b -> (P a <-> Q b)).
  Defined.

  Global Instance functorOK_PM : @FunctorOK PM functor_PM.
  unfold FunctorOK.
  intros.
  unfold transport, functor_PM.
  constructor.
  - red. intros. symmetry. apply H. symmetry. assumption.
  - red. intros x y z H H1 a b H2. 
    eapply transitivity. apply H. apply H2. apply H1. eapply transitivity. symmetry. apply H2. apply H2.
  Defined.
End MonadProp.

Section MonadPropLaws.
  Context {A B C : Type}.
  Context {eqa : rel A} {eqb : rel B} {eqc : rel C}.
  Context (TA: TYP eqa).
  Context (TB: TYP eqb).
  Context (TC: TYP eqc).

  About MonadProperties.

  Instance monad_properties_PM : @MonadProperties PM A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  split.
  - repeat reduce.
    + unfold ret, monad_return_PM, ret_PM. split.
      intros. eapply transitivity. symmetry. apply H0. eapply transitivity. apply H1. assumption.
      intros. eapply transitivity. apply H0. eapply transitivity. apply H1. symmetry. assumption.      

  - repeat reduce.
    unfold bind, monad_bind_PM, bind_PM. split.
    intros. destruct H4 as (a0 & I & J & K).
    exists a0. repeat split; try tauto. eapply H.  apply I. tauto. eapply H0.
    apply I. apply H1. apply K.
    intros. destruct H4 as (a0 & I & J & K).
    exists a0. repeat split; try tauto. eapply H; tauto. eapply H0. apply I. tauto. tauto.

  - repeat reduce.
    unfold ret, monad_return_PM, ret_PM.
    unfold bind, monad_bind_PM, bind_PM.
    split.
    + intros.
      destruct H1 as (a1 & I & J & K).
      apply (PF a1 a); eauto.
    + intros.
      exists a. tauto.

  - repeat reduce.
    unfold ret, monad_return_PM, ret_PM.
    unfold bind, monad_bind_PM, bind_PM.
    split.
    + intros.
      destruct H1 as (a1 & I & J & K).
      unfold id. unfold transport in H. unfold functor_PM in H.

*)


(* Section MonadLaws. *)


(*   Class MonadProperties : Prop := *)
(*     { *)
(*       (* mon_ret_proper  :> forall {A : typ} `{PER A (equalE A)}, *) *)
(*       (*     Proper ((equalE A) ==> feq) ret; *) *)

(*       (* mon_bind_proper :> forall {A B : typ} `{PER A (equalE A)} `{PER B (equalE B)}, *) *)
(*       (*                 Proper (feq ==> (equalE A ==> feq) ==> feq) *) *)
(*       (*                 bind; *) *)

(*       bind_ret_l : forall {A B : typ} `{PER A (equalE A)} `{PER B (equalE B)} *)
(*           (f : A -> M B) (PF:Proper (equalE A ==> feq) f), *)
(*         (equalE (equalE A ~~> feq)) (fun (a:A) => bind (ret a) f)  f; *)

(*       bind_ret_r : forall {A : typ} `{PER A (equalE A)}, *)
(*           (equalE (feq ~~> feq)) (fun x => bind x ret) (id); *)

(*       bind_bind : forall {A B C : typ} *)
(*                     `{PER A (equalE A)} `{PER B (equalE B)} `{PER C (equalE C)} *)
(*                     (f : A -> M B) (g : B -> M C) *)
(*                     (PF:Proper (equalE A ==> feq) f)  (* f \in TYP (eqa ~~> eqb) *) *)
(*                     (PG:Proper (equalE B ==> feq) g), *)
(*         (equalE (feq ~~> feq)) *)
(*           (fun (x: M A) => (@bind M _ B C (bind x f) g)) *)
(*           (fun (x: M A) => (@bind M _ A C x (fun (y : A) => (bind (f y) g)))) *)
(*     }. *)
(* End MonadLaws. *)
