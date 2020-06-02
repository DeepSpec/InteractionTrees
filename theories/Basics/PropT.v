
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

  (* We go back to our EqmR definition, which is necessary if we want a notion
   * of "agrees" for our bind function.
   *
   * EqmRMonad is defined using typ's and fufills [CategoryMonad] monad laws.
   *)
  Context {EqM: EqmR M} {EqmR : EqmR_OK M} {EqmRMonad : EqmRMonad M}.

  (* Moreover, we need monads that have well-defined "inversion principles" *)
  Context {EqmRMonadInverses : EqmRMonadInverses M}.

  (* The typ that PropT returns that we want coincides with the typ version of typ_proper. *)
  Definition PropT (X : typ) : typ := (M X) ~=~> prop_typ.

  Lemma sanity : forall (A:typ) (P:PropT A) (ma ma' : M A) (EQ: ma == ma'), (P @ ma) == (P @ ma').
  Proof.
    intros A P ma ma' EQ.
    repeat red. split; intros.
    rewrite <- EQ. assumption. rewrite EQ. assumption.
  Qed.
  
  (* Ret Definition ************************************ *)
  (* Using Program Definition to give the properness proofs through obligations. *)
  Program Definition ret_ {A : typ} : A -> PropT A :=
    fun a => (-=->! (equal (ret @ a))) _. (* Define the data here. *)
  Next Obligation. (* Properness proof goes here. *)
    apply Proper_equal_partial.
  Defined.

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

  (* Bind definition. ********************************* *)
  Definition prop_agrees {A : typ} : relationH (A) (A ~=~> prop_typ) :=
    fun (x : A) (P : A ~=~> prop_typ) => P @ x.

  Definition agrees {A B : typ} (ma : M A) (kb : A -=-> M B) (k : A -=-> PropT B) : Prop :=
    let kb' : M A -=-> M (M B) := (monad_fmap M A (M B) kb) in
    let k'  : M A -=-> M (PropT B) := (monad_fmap M A (PropT B) k) in
    @eqmR M _ (M B) (PropT B) prop_agrees (kb' @ ma) (k' @ ma).



 (*  
  Lemma agrees_retP_eq {A : typ} :
    forall (ma : M A) (kb : A -=-> M A),
      agrees ma kb retP -> kb ⩯ ret.
  Proof with eauto.
    intros. unfold_cat. intros.
    unfold agrees, monad_fmap in H.


    

    
    exists S, eqmR S m1 m2 /\ forall s1, s2, S s1 s2 -> eqmR R (k1 s1) (k2 s2)
    
    unfold retP in H.
    eapply eqmR_Proper in H... 2 : reflexivity.
    2 : { Unshelve. 2 : { refine ( (bind kb >>> ret) @ ma). }
          2 : shelve.
          assert (bind kb >>> ret ⩯ bind (kb >>> ret)). {
            admit.
          }
  Admitted.
   *)

  
  (*
  Lemma agrees_ret_inv {A B : typ} :
    forall (x : A) (kb : A -=-> M B) (k : A -=-> PropT B),
    eqmR prop_agrees (ret @ (kb @ x)) (ret @ (k @ x)) -> prop_agrees (kb @ x) (k @ x).
  Proof.
    intros x kb k H.
  Admitted.
   *)  
  
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


  Arguments Proper_typ_proper_app {_ _ _ _}.
  Ltac apply_proper A := eapply (Proper_typ_proper_app A).

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

  (* ==== Monad Laws for PropT ====================================================== *)


  Lemma ret_equal :
    forall {A : typ} (x y: A), x == y -> ret @ x == ret @ y.
  Proof.
    intros.
    match goal with
    | |- ?r @ _ == _ => remember r as r'
    end.
    assert (Eq2 : r' ⩯ r') by reflexivity.
    apply_proper Eq2. assumption.
  Qed.

  Ltac app_proper X :=
    assert (Hz : X ⩯ X) by reflexivity; apply_proper Hz; clear Hz.

  Lemma typ_fun_in : forall (a b : typ) (f : a -=-> b), `f ∈ (a ~~> b).
  Proof.
    intros a b f.
    cbn. intros a1 a2 H.
    destruct f. cbn. apply p. assumption.
  Qed.
  
  Lemma PropT_bind_ret_l : forall (a b : typ) (f : a -=-> (PropT b)),
    ret >>> bind f ⩯ f.
  Proof with eauto.
  intros A B k x y EQ mb mb' EQ'.
  split; unfold bind_.

  (* -> *)
  - intros H. app_proper k. symmetry; apply EQ. PER_reflexivity.
    cbn in H.
    edestruct H as (ma & kb & Hm & Hret & Hbind & Agr); clear H.
    rewrite <- EQ'.
    rewrite <- Hbind. rewrite <- Hret. epose proof bind_ret_l as Hbr.
    unfold_cat in Hbr; rewrite Hbr. 2 : PER_reflexivity.

    (* Agr *)

    Typeclasses eauto := 3.
    unfold agrees, monad_fmap in Agr.

    eapply eqmR_Proper in Agr...
    2 : {
      Unshelve. 2 : {  refine ((bind (kb >>> ret)) @ (ret @ x)). }
      2 : { refine ((bind (k >>> ret)) @ (ret @ x)). }
      eapply eqmR_bind_ProperH...
      Unshelve. 3 : { refine (fun a1 a2 => a1 = x /\ a2 = x). }
      eapply eqmR_Proper...
      Unshelve. 6 : { refine (fun a1 a2 => a1 = x /\ a2 = x). }
      reflexivity. rewrite eqmR_equal. PER_reflexivity.
      rewrite eqmR_equal. symmetry; apply Hret.
      apply eqmR_ret...

      cbn. intros. apply eqmR_ret... destruct H0. rewrite H0. rewrite H1.
      app_proper kb; try PER_reflexivity.
    }

    eapply eqmR_Proper in Agr... 2 : reflexivity.
    2 : {
      Unshelve. 2 : { refine ((kb >>> ret) @ x). }
      rewrite eqmR_equal. rewrite <- eqmR_bind_ret_l.
      app_proper (bind (kb >>> ret)); try PER_reflexivity.
      unfold contains; PER_reflexivity.
      exact ((k >>> ret) @ x).
    }
    2 : {
      rewrite eqmR_equal. rewrite <- eqmR_bind_ret_l. app_proper (bind (k >>> ret)).
      PER_reflexivity. unfold contains; PER_reflexivity.
    }
    2 : { rewrite eqmR_equal. app_proper (bind (k >>> ret)). apply Hret. }
    cbn in Agr.

    change (prop_agrees (kb @ x) (k @ x)).
    apply eqmR_ret_inv in Agr; assumption...

  (* <- *)
  - intros H.
    exists (ret @ x).
    eexists ?[kb].
    split; [ eapply ret_equal; PER_reflexivity | split; [eapply ret_equal; PER_reflexivity |split ]].

    (* bind ?kb @ (ret @ x) == mb *)
    + pose proof (bind_ret_l (M := M) (a := A)) as Hbr.
      unfold_cat in Hbr; rewrite Hbr. 2 : apply EQ. rewrite EQ'.
      Unshelve. 2 : {
        refine (-=->! (fun x => mb') _).
        do 2 red. intros. symmetry in EQ'; PER_reflexivity.
      }
      cbn. symmetry in EQ'; PER_reflexivity.

    (* agrees (ret @ x) ?kb k*)
    + unfold agrees. unfold monad_fmap.
      eapply eqmR_bind_ProperH...
      Unshelve. 3 : { refine (fun a1 a2 => a1 == x /\ a2 == x). }
      apply eqmR_ret...
      split; PER_reflexivity.
      intros. cbn in H0. destruct H0.
      cbn. apply eqmR_ret...
      unfold prop_agrees.
      assert (Eq2: k ⩯ k) by reflexivity.
      apply_proper Eq2. rewrite EQ in H1.  apply H1. symmetry; eassumption.
      app_proper (k @ y)...
  Qed.

  Definition typ_proper_to_typ {a b} (X : a -=-> b) : a ~=~> b := X.
  Coercion typ_proper_to_typ : typ_proper >-> Ty.

  Lemma PropT_bind_ret_r : forall a : typ,
    bind ret ⩯ id_ (PropT a).
  Proof with eauto.
    intros a Pa Pa' EQ x y EQ'.
    split; unfold bind_.

    (* -> *)
    - intros H. cbn. app_proper Pa'. symmetry; apply EQ'.
      cbn in H. edestruct H as (ma & kb & Hma & Hret & Hbind & Agr).

      (* Rewrite with EQ. *)
      unfold equal in EQ. cbn in EQ. unfold eq2, eq2_typ_proper in EQ.
      rewrite <- EQ. 2 : PER_reflexivity.
      clear H. app_proper Pa. symmetry; apply Hbind.


      epose proof bind_ret_r as Hbr. unfold_cat in Hbr.
      assert (bind kb @ ma == ma). {
        specialize (Hbr ma ma Hma).
        rewrite <- Hbr at 2.
        rewrite <- eqmR_equal. eapply eqmR_bind_ProperH... rewrite eqmR_equal...
        intros. rewrite eqmR_equal...

        admit.
        
(*        eapply agrees_retP_eq... *)
      }
      app_proper Pa...

    (* <- *)
    - cbn. intros H.
      exists x. exists ret.
      split; [ | split ]. unfold contains. PER_reflexivity.
      apply_proper EQ...
      split.
      + epose proof bind_ret_r. unfold_cat in H0. apply H0. PER_reflexivity.
      + unfold agrees, monad_fmap. eapply eqmR_bind_ProperH...
        rewrite eqmR_equal. PER_reflexivity.
        intros. cbn. apply eqmR_ret... cbn.
        symmetry. rewrite H0. rewrite <- eqmR_equal. apply eqmR_ret... PER_reflexivity.
Admitted.

  Lemma PropT_bind_bind :
    forall (a b c : typ) (f : typ_proper a (PropT b)) (g : typ_proper b (PropT c)),
      bind f >>> bind g ⩯ bind (f >>> bind g).
  Proof with eauto.
    intros *. intros x y EQ mc mc' EQ'.
    split; intros H.
    - cbn in H. edestruct H as (mb & kbc & Hma & Hret & Hbind & Agr). clear H.
      edestruct Hret as (ma & kab & Hma' & Hret' & Hbind' & Agr'). clear Hret.
      cbn. exists ma. eexists ?[kb].
      split... split. apply_proper EQ...
      split. rewrite <- EQ'. rewrite <- Hbind. rewrite <- Hbind'.
      epose proof bind_bind. unfold eq2, eq2_typ_proper in H.
      specialize (H kab kbc ma ma Hma'). cbn in H.
      rewrite H. Unshelve. 3 : refine (kab >>> bind kbc).
      app_proper (bind (kab >>> bind kbc))...

      unfold agrees, monad_fmap. eapply eqmR_bind_ProperH...
      Unshelve. 3 : { refine ( fun a1 a2 => kab @ a1 == mb /\ kab @ a2 == mb). }
      admit.
      intros. cbn. apply eqmR_ret... cbn.
      cbn in H; destruct H.
      exists mb. exists kbc. split... split...
      app_proper (f @ a2). symmetry; apply H0.
      admit.
      split... app_proper (bind kbc). rewrite H. PER_reflexivity.
    - admit.
   Admitted.
 

  Instance PropT_MonadLaws : MonadLaws PropT_Monad.
  constructor.
  - apply PropT_bind_ret_l. 
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
