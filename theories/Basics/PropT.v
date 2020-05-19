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
.

Import CatNotations.
Open Scope cat_scope.


(* Proper Instance for typ_proper. *)
Lemma typ_proper_proj :
  forall (A B : typ) (P : typ_proper A B), Proper (equalE A ==> equalE B) (` P).
Proof.
  destruct P. cbn. apply p.
Defined.

Existing Instance typ_proper_proj.


Section MonadProp.
  Program Definition PropM : typ -> typ :=
    fun (A : typ) =>
      {|
        Ty := {p : A -> Prop | Proper (equalE A ==> iff) p};
        equal :=
          fun pm1 pm2 =>
            forall (a : A), ` pm1 a <-> ` pm2 a
      |}.
  Next Obligation.
    split.
    repeat red. intros x y H a.
    split. apply H. apply H.
    repeat red. intros x y z H H0 a.  
    split. intros. apply H0, H, H1; auto. intros. apply H, H0, H1; auto.
  Qed.

  Instance PropM_Monad : Monad typ_proper PropM.
  split.
  - repeat red. intros A.
    refine (exist _ (fun (a:A) => (exist _ (fun x => equalE A a x) _)) _).
    repeat red. cbn. intros x y Heq a_term.
    rewrite Heq. auto.
    Unshelve.
    repeat red. intros.
    rewrite H.
    auto.
  - repeat red. intros A B HK.
    destruct HK as (K & KProper).
    refine (exist _ (fun PA: PropM A => (exist _ (fun b: B =>
            exists a : A, `PA a /\ (proj1_sig (K a)) b) _)) _).
    (* KS: For some reason the back-tick didn't work here *)
    repeat red. cbn. intros ma1 ma2 Heq b.
    split; intros; destruct H; exists x; specialize (Heq x).
    + rewrite <- Heq. auto.
    + rewrite Heq. auto.
    Unshelve.
    repeat red. intros b1 b2 Heq.
    split; intros; destruct H; exists x; destruct H; split; auto.
      * cbn in *. destruct K.
        (* KS: Coq can't find the necessary Proper instance to
               rewrite unless K is destructed. *)
        rewrite <- Heq. auto.
      * cbn in *; destruct K; rewrite Heq; auto.
  Qed.

End MonadProp.

Section MonadPropT.

  Context {M : typ -> typ}.
  Context {M_Monad: Monad typ_proper M}.

  Existing Instance eq2_typ_proper.
  Existing Instance cat_typ_proper.
  Existing Instance id_typ_proper.

  Context {ML : MonadLaws M_Monad}.

  Lemma PropT_PER_equal:
    forall X : typ,
      PER
        (fun PA1 PA2 : {p : M X -> Prop | Proper (equalE (M X) ==> iff) p} =>
            forall ma : M X, (` PA1) ma <-> (` PA2) ma).
  Proof.
    intros X.
    split.
    - repeat red. intros x y H6 ma.
      split; eauto. apply H6. apply H6.
    - repeat red. intros x y z H6 H7 ma.
      split; eauto. intros.  apply H7. apply H6. apply H.
      intros. apply H6. apply H7. apply H.
  Qed.

  Definition PropT : typ -> typ :=
    fun (X : typ) =>
      {|
        Ty := { p : M X -> Prop | Proper (equalE (M X) ==> iff) p };
        equal :=
          fun PA1 PA2 =>
            forall (ma : M X), ` PA1 ma <-> ` PA2 ma;
        equal_PER := PropT_PER_equal X
      |}.


  Instance ret_equalE_proper {A}:
    Proper (equalE A ==> equalE (M A) ==> impl) (fun x => equalE (M A) ((` ret) x)).
  Proof.
    destruct ret. cbn in *.
    do 2 red in p. do 3 red. intros x0 y H6 x1 y0 H7.
    rewrite <- H7.
    specialize (p _ _ H6).
    rewrite p. reflexivity.
  Qed.

  (* Ret definition. *)
  Definition ret_ty_fn {A : typ} (a : A) : M A -> Prop :=
    fun (ma : M A) => equalE (M A) (` ret a) ma.

  Lemma ret_ty_proper {A : typ} (a : A) :
    Proper (equalE (M A) ==> iff) (ret_ty_fn a).
  Proof.
    unfold ret_ty_fn.
    repeat red.
    refine (fun x y EQ => _).
    (* Introduce a proper instance for rewriting under equalE (M A). *)
    split; intros EQ'.
    + rewrite EQ in EQ'. eapply EQ'.
    + rewrite <- EQ in EQ'. apply EQ'.
  Qed.

  Definition ret_ty {A : typ} : A -> PropT A :=
    fun a => exist _ (ret_ty_fn a) (ret_ty_proper a).

  Lemma ret_prop_proper :
    forall {A : typ}, Proper (equalE (A) ==> equalE (PropT A)) ret_ty.
  Proof.
    unfold ret_ty.
    intros A a f.
    (* Properness proof of outer case. *)
    split; intros EQ''.
    + cbn. unfold ret_ty_fn. rewrite <- EQ''.
      eapply ret_equalE_proper. apply H. symmetry. eauto. eauto.
    + cbn. unfold ret_ty_fn. rewrite <- EQ''.
      eapply ret_equalE_proper. symmetry. apply H. symmetry; eauto.
      assumption.
  Qed.

  Definition ret_propT {A} : typ_proper A (PropT A) :=
    exist _ (fun a => ret_ty a) ret_prop_proper.

  (* Bind definition. *)

  Definition agrees (A B : typ) (ma : M A)
              (kb : typ_proper A (M B)) (k : typ_proper A (PropT B)) :=
      forall x y, x ∈ A -> y ∈ A -> equalE A x y ->
          ( ` (ret_ty x)) ma ->
      (` ((` k) x)) ((` kb) x).

  Definition bind_ty_fn {A B} (k : typ_proper A (PropT B)) (PA : PropT A)  :
    M B -> Prop :=
    fun (mb : M B) =>
      exists (ma : M A) (kb : typ_proper A (M B)),
        `PA ma /\
        (equalE (M B) mb ((` (bind kb)) ma)) /\
        agrees A B ma kb k.

  Lemma bind_ty_proper :
    forall {A B : typ} (k : typ_proper A (PropT B)) (PA : PropT A) ,
      Proper (equalE (M B) ==> iff) (bind_ty_fn k PA).
  Proof.
    intros A B k PA.
    unfold bind_ty_fn.
    repeat red.
    intros x y EQ.
    split; intros EQ'.
    - edestruct EQ' as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H.
      split. intros.
      rewrite <- EQ. assumption. assumption.
    - edestruct EQ' as (? & ? & ? & ? & ?).
      exists x0, x1. split. apply H.
      split. intros. rewrite EQ.
      assumption. assumption.
  Qed.

  Definition bind_ty {A B} (k : typ_proper A (PropT B)) : PropT A -> PropT B :=
    fun PA => exist _ (bind_ty_fn k PA) (bind_ty_proper k PA).

  Lemma bind_prop_proper:
    forall {A B : typ} (k : typ_proper A (PropT B)),
      Proper (equalE (PropT A) ==> equalE (PropT B)) (bind_ty k).
  Proof.
    intros A B K. cbn.
    unfold bind_ty, bind_ty_fn.
    split; intros EQ''; cbn in EQ''; cbn.
    + edestruct EQ'' as (ma0 & kb & Hx & EQ & Hagr).
      exists ma0, kb. split.
      apply H. assumption.
      split ; assumption.

    + edestruct EQ'' as (? & ? & ? & ? & ?).
      exists x0, x1. split.
      apply H. assumption.
      split; assumption.
  Qed.

  Definition bind_propT {A B} (k : typ_proper A (PropT B)) :
    typ_proper (PropT A) (PropT B):=
      exist _ (fun PA => bind_ty k PA) (bind_prop_proper k).

  Instance PropT_Monad : Monad typ_proper PropT :=
    {|
      ret := @ret_propT;
      bind := @bind_propT
    |}.

  (* ==== Monad Laws for PropT ====================================================== *)

  (* IY: Is there a better generalized Ltac for this? *)
  Ltac unfold_cat :=
     unfold cat, cat_typ_proper, eq2, eq2_typ_proper; cbn.

  Tactic Notation "unfold_cat" "in" hyp(H) :=
    unfold cat, cat_typ_proper, eq2, eq2_typ_proper in H; cbn in H.


  Lemma ret_proper :
    (forall (a : typ) (ma : M a),
        Proper (equalE a ==> iff) (fun x => (` (ret_ty x)) ma)).
  Proof.
    intros a ma. repeat red. intros. unfold ret_ty. cbn. unfold ret_ty_fn.
    split. intros. rewrite <- H. assumption.
    intros. rewrite H. assumption.
  Qed.

  Lemma typ_proper_propT :
    forall {A B : typ} (P : typ_proper A (PropT B)) (a : A), Proper (equalE (M B) ==> iff)  (` ((` P) a)).
  Proof.
    intros. destruct P. cbn.
    pose proof (proj2_sig (x a)). apply H.
  Qed.

  Existing Instance ret_proper.
  Existing Instance typ_proper_propT.
  Existing Instance ret_ty_proper.
  Existing Instance bind_ty_proper.
  Existing Instance ret_prop_proper.
  Existing Instance bind_prop_proper.

  Axiom monad_reflexivity: forall a ma, equalE (M a) ma ma.

  Definition typ_proper_app : forall {a b : typ} (f : typ_proper a b) (x : a), b.
    intros a b f x.
    destruct f.
    apply x0. apply x.
  Defined.

  Lemma proper_typ_proper_app : forall {a b : typ},
      Proper (eq2 ==> equalE a ==> equalE b) 
             (@typ_proper_app a b).
  Proof.
    repeat intro.
    destruct x, y.
    cbn in *.
    specialize (H x0 y0).
    cbn in H.
    apply H. unfold contains. etransitivity. apply H0. symmetry. apply H0.
    unfold contains. etransitivity. symmetry. apply H0. apply H0.
    assumption.
  Qed.
    
  Notation "f @ x" := (typ_proper_app f x) (at level 40).

(*
  Lemma typ_proper_app_ok : forall (a b : typ) (f : typ_proper a b) x (X:x ∈ a), (f @ x) ∈ b.
  Proof.
    intros a b f x X.
    destruct f. cbn. apply p. apply X.
  Qed.
*)
  
  (* Inductive mayRet : forall (a : typ), M a -> a -> Prop := *)
  (* | mayRet_ret : forall (A : typ) (x : A), mayRet A x *)
  (* . *)

  Lemma propT_bind_ret_l : forall (a b : typ) (f : typ_proper a (PropT b)),
    ret >>> bind f ⩯ f.
  Proof.
  intros a b k.
  unfold ret, bind, PropT_Monad, ret_propT, bind_propT.
  cbn. red. unfold eq2_typ_proper. cbn.
  intros x y Hx Hy EQ mb.
  split; unfold bind_ty_fn.
  - intros Hb.
    edestruct Hb as (ma & kb & Hret & EQ' & Ha); clear Hb.
    rewrite EQ'. rewrite <- Hret.
    epose proof bind_ret_l as Hbr.
    specialize (Hbr kb x y Hx Hy EQ). unfold_cat in Hbr.
    rewrite Hbr.
    unfold agrees in Ha.
    eapply Ha; try eassumption.
    eapply ret_proper; [symmetry | ]; eassumption.
  - intros H.
    epose proof bind_ret_l as Hbr.
    unfold_cat in Hbr.
    exists (ret @ x). eexists ?[kb].
    split; [ | split].
    + apply ret_ty_proper with (y0:=(ret @ y)).
      cbn.
      apply proper_typ_proper_app.
      { admit. }
      assumption.
      unfold ret_ty_fn. unfold typ_proper_app.
      (* TODO: replace ` proj1_sig by @ 
          -- that should lead to some cleanups ??
         TODO: ensure that eq2 is at least a preorder [doublecheck]
       *)
      admit.
      
      (* TODO: Do we introduce reflexivity for monad equality? *)
    (*      apply monad_reflexivity. unfold ret_ty_fn. apply monad_reflexivity. *)
    + (* Equality on bind_ret_l. *)
      destruct k as (k_f & k_proper). cbn in H.
      repeat red in k_proper.
      rewrite Hbr. 2 : apply Hx. 2 : apply Hy. 2 : apply EQ.

      (* TODO : We need some kind of inversion principle here (or reflexivity defined on monadic computations). *)
      (* Need to define MayRet for this monad? *)
      Unshelve. 2 : { refine (exist _ (fun a => mb) _). repeat intro.
                      apply monad_reflexivity. (* IY: reflexivity? *) }
      cbn. (* reflexivity, again. *) apply monad_reflexivity.
    + (* Agrees. *)
      unfold agrees. intros x' y' Hx' Hy' EQ' Hret. cbn.
      unfold ret_ty in Hret. cbn in Hret. unfold ret_ty_fn in Hret.

      (* TODO: Monad ret inversion. *)
      assert (ret_inv: equalE (M a) ((` ret) x') ((` ret) x) -> equalE a x' x). admit.
      specialize (ret_inv Hret).

      (* TODO: Another proper instance. *)
      assert (HP: Proper (equalE a ==> iff) (fun x' => (` ((` k) x')) mb)). {
        admit.
      }

     eapply HP. rewrite ret_inv. apply EQ. apply H.
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
