(** * Facts about [aloop] and [loop] *)

(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Function
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Core.ITreeMonad
     Core.KTree
     Eq.Shallow
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2.

Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.
(* end hide *)

Ltac unfold_ktree :=
  unfold
    Basics.iter, MonadIter_itree,
    assoc_l, AssocL_Coproduct,
    bimap, Bimap_Coproduct,
    cat, Cat_Kleisli, inl_, Inl_Kleisli, inr_, Inr_Kleisli, case_, Case_Kleisli, case_sum,
    lift_ktree_; cbn.

(** ** [ITree.aloop] *)

Lemma bind_iter {E A B C} (f : A -> itree E (A + B)) (g : B -> itree E (B + C))
  : forall x,
    (ITree.bind (ITree.iter f x) (ITree.iter g))
  ≈ ITree.iter (fun ab =>
       match ab with
       | inl a => ITree.map inl (f a)
       | inr b => ITree.map (bimap inr (id_ _)) (g b)
       end) (inl x).
Proof.
  einit. ecofix CIH. intros.
  rewrite !unfold_iter.
  rewrite bind_map, bind_bind.
  ebind; econstructor; try reflexivity.
  intros [a | b] _ [].
  - rewrite bind_tau. etau.
  - rewrite bind_ret_l, tau_euttge.
    revert b. ecofix CIH'. intros.
    rewrite !unfold_iter.
    rewrite bind_map.
    ebind; econstructor; try reflexivity.
    intros [b' | c] _ []; cbn.
    + etau.
    + reflexivity.
Qed.

Lemma eq_itree_iter' {E I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2))
      (eutt_body
       : forall j1 j2, RI j1 j2 -> eq_itree (sum_rel RI RR) (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @eq_itree E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  ginit. pcofix CIH. intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  guclo eqit_clo_bind; econstructor; eauto.
  intros ? ? []; gstep; econstructor; auto with paco.
Qed.

Lemma eutt_iter' {E I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2))
      (eutt_body
       : forall j1 j2, RI j1 j2 -> eutt (sum_rel RI RR) (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @eutt E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  einit. ecofix CIH. intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  ebind; econstructor; eauto with paco.
  intros ? ? [].
  - etau.
  - eauto with paco.
Qed.

Lemma eutt_iter'' {E I1 I2 R1 R2}
      (RI1 RI2 : I1 -> I2 -> Prop)
      (HSUB: RI2 <2= RI1)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2))
      (eutt_body
      : forall j1 j2, RI1 j1 j2 -> eutt (sum_rel RI2 RR) (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI1 i1 i2),
    @eutt E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  einit. ecofix CIH. intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  ebind; econstructor; eauto with paco.
  intros ? ? [].
  - etau.
  - eauto with paco.
Qed.

Definition eutt_iter_gen' {F A B R1 R2 S} (HS : R2 <2= R1) :
  @Proper ((A -> itree F (A + B)) -> A -> itree F B)
          ((R1 ==> eutt (sum_rel R2 S)) ==> R1 ==> (eutt S))
          (iter (C := ktree F)).
Proof.
  do 3 red;
  intros body1 body2 EQ_BODY x y Hxy. red in EQ_BODY.
  eapply eutt_iter''; eauto.
Qed.

(** ** [iter] *)

#[global] Instance eq_itree_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          ((eq ==> eq_itree eq) ==> pointwise_relation _ (eq_itree eq))
          (iter (C := ktree E)).
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  eapply (eq_itree_iter' eq); auto.
  intros; eapply eqit_mon, EQ_BODY; auto.
  intros [] _ []; auto; econstructor; subst; auto.
Qed.

#[global] Instance eutt_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          (pointwise_relation _ (eutt eq) ==> pointwise_relation _ (eutt eq))
          (iter (C := ktree E)).
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  eapply (eutt_iter' eq); auto.
  intros ? _ []; eapply eqit_mon, EQ_BODY; auto.
  intros [] _ []; auto; econstructor; auto.
Qed.

Definition eutt_iter_gen {F A B R S} :
  @Proper ((A -> itree F (A + B)) -> A -> itree F B)
          ((R ==> eutt (sum_rel R S)) ==> R ==> (eutt S))
          (iter (C := ktree F)).
Proof.
  do 3 red;
  intros body1 body2 EQ_BODY x y Hxy. red in EQ_BODY.
  eapply eutt_iter'; eauto.
Qed.

#[global] Instance eq2_ktree_iter {E A B} :
  @Proper (ktree E A (A + B) -> ktree E A B)
          (eq2 ==> eq2)
          iter.
Proof. apply eutt_iter. Qed.

Section KTreeIterative.

Lemma unfold_iter_ktree {E A B} (f : ktree E A (A + B)) (a0 : A) :
  iter f a0 ≅
    ITree.bind (f a0) (fun ab =>
    match ab with
    | inl a => Tau (iter f a)
    | inr b => Ret b
    end).
Proof.
  apply unfold_iter.
Qed.

#[global] Instance IterUnfold_ktree {E} : IterUnfold (ktree E) sum.
Proof.
  repeat intro. rewrite unfold_iter_ktree.
  eapply eutt_clo_bind; try reflexivity.
  intros [] ? []; try rewrite tau_eutt; reflexivity.
Qed.

#[global] Instance IterNatural_ktree {E} : IterNatural (ktree E) sum.
Proof.
  repeat intro.
  revert a0.
  einit. ecofix CIH. intros.
  unfold_ktree.
  rewrite 2 unfold_iter_ktree.
  repeat setoid_rewrite bind_bind.
  ebind; econstructor; try reflexivity.
  intros [] ? [].
  - setoid_rewrite bind_tau. do 2 setoid_rewrite bind_ret_l. etau.
  - setoid_rewrite bind_ret_l; repeat setoid_rewrite bind_bind. setoid_rewrite bind_ret_l. rewrite bind_ret_r.
    reflexivity.
Qed.

Lemma iter_dinatural_ktree {E A B C}
      (f : ktree E A (C + B)) (g : ktree E C (A + B)) (a0 : A)
  : iter (C := ktree E) (fun a =>
      ITree.bind (f a) (fun cb =>
      match cb with
      | inl c => Tau (g c)
      | inr b => Ret (inr b)
      end)) a0
  ≅ ITree.bind (f a0) (fun cb =>
     match cb with
     | inl c0 => Tau (iter (C := ktree E) (fun c =>
         ITree.bind (g c) (fun ab =>
         match ab with
         | inl a => Tau (f a)
         | inr b => Ret (inr b)
         end)) c0)
     | inr b => Ret b
     end).
Proof.
  revert f g a0.
  ginit. pcofix CIH. intros.
  rewrite unfold_iter_ktree.
  rewrite bind_bind.
  guclo eqit_clo_bind. econstructor. try reflexivity.
  intros [] ? [].
  { rewrite bind_tau.
    (* TODO: here we should be able to apply symmetry and be done. *)
    rewrite unfold_iter_ktree.
    gstep; econstructor.
    rewrite bind_bind.
    guclo eqit_clo_bind; econstructor; try reflexivity.
    intros [] ? [].
    * rewrite bind_tau.
      gstep; constructor.
      eauto with paco.
    * rewrite bind_ret_l. gstep; econstructor; auto.
  }
  { rewrite bind_ret_l. gstep; constructor; auto. }
Qed.

#[global] Instance IterDinatural_ktree {E} : IterDinatural (ktree E) sum.
Proof.
  repeat intro. unfold_ktree.
  transitivity (iter (C := ktree E) (fun t =>
                        ITree.bind (f t) (fun x =>
                        match x with
                        | inl a1 => Tau (g a1)
                        | inr b0 => Ret (inr b0)
                        end)) a0).
  - apply eutt_iter; intros x.
    eapply eutt_clo_bind.
    reflexivity.
    intros [] ? [].
    rewrite tau_eutt; reflexivity.
    reflexivity.
  - rewrite iter_dinatural_ktree.
    eapply eutt_clo_bind.
    reflexivity.
    intros [] ? [].
    + rewrite tau_eutt.
      apply eutt_iter; intros x.
      eapply eutt_clo_bind.
      reflexivity.
      intros [] ? [].
      rewrite tau_eutt; reflexivity.
      reflexivity.
    + reflexivity.
Qed.

Lemma iter_codiagonal_ktree {E A B} (f : ktree E A (A + (A + B))) (a0 : A)
  : iter (iter f) a0
  ≅ iter (C := ktree _) (fun a =>
       ITree.bind (f a) (fun r =>
       match r with
       | inl a' => Ret (inl a')
       | inr (inl a') => Ret (inl a')
       | inr (inr b) => Ret (inr b)
       end)) a0.
Proof.
  revert a0.
  ginit. pcofix CIH. intros.
  rewrite unfold_iter_ktree.
  rewrite (unfold_iter_ktree (fun _ => _ _ _)).
  rewrite unfold_iter_ktree, !bind_bind.
  guclo eqit_clo_bind. econstructor. reflexivity.
  intros [| []] ? [].
  - rewrite bind_ret_l, bind_tau.
    gstep. constructor.
    revert a.
    pcofix CIH'. intros.
    rewrite unfold_iter_ktree.
    rewrite (unfold_iter_ktree (fun _ => _ _ _)).
    rewrite !bind_bind.
    guclo eqit_clo_bind. econstructor. reflexivity.
    intros [| []] ? [].
    + rewrite bind_tau, bind_ret_l. gstep; constructor; auto with paco.
    + rewrite 2 bind_ret_l. gstep; constructor; auto with paco.
    + rewrite 2 bind_ret_l. gstep; constructor; auto.
  - rewrite 2 bind_ret_l.
    gstep; constructor; auto with paco.
  - rewrite 2 bind_ret_l.
    gstep; reflexivity.
Qed.

#[global] Instance IterCodiagonal_ktree {E} : IterCodiagonal (ktree E) sum.
Proof.
  repeat intro. unfold_ktree.
  rewrite iter_codiagonal_ktree.
  apply eutt_iter.
  intros a1.
  eapply eutt_clo_bind.
  reflexivity.
  intros [| []] ? []; rewrite ?tau_eutt; reflexivity.
Qed.

#[global] Instance Iterative_ktree {E} : Iterative (ktree E) sum.
Proof.
  split; typeclasses eauto.
Qed.

(* Equation merging the sequence of two [iter] into one *)
Lemma cat_iter:
  forall {E: Type -> Type} {a b c} (f: ktree E a (a + b)) (g: ktree E b (b + c)),
    ITree.iter f >>> ITree.iter g ⩯ inl_ >>> ITree.iter (case_ (f >>> inl_) (g >>> inr_ >>> assoc_l)).
Proof.
  intros *.
  unfold
    Basics.iter, MonadIter_itree,
    assoc_l, AssocL_Coproduct,
    bimap, Bimap_Coproduct,
    cat, Cat_Kleisli, inl_, Inl_Kleisli, inr_, Inr_Kleisli, case_, Case_Kleisli, case_sum,
    lift_ktree_.
  cbn.
  Unset Printing Notations.
  simpl.
  cbn.


  unfold_ktree.
  (* We move to the eworld *)
  einit.
  intros.
  revert a0.
  (* First coinductive point in the simulation: at the entry point of the iteration over f *)
  ecofix CIH.
  intros.
  cbn.
  setoid_rewrite bind_ret_l.
  (* We unfold one step on both sides *)
  match goal with
  |- euttG _ _ _ _ _ ?t _ => remember t; rewrite unfold_iter; subst
  end.
  rewrite unfold_iter; cbn.
  repeat setoid_rewrite bind_bind.
  ebind.
  (* We run f a first time on both side *)
  econstructor; [reflexivity | intros [xa | xb] ? <-].
  - (* If we loop back to f, we can conclude by coinduction *)
    repeat setoid_rewrite bind_ret_l.
    rewrite bind_tau.
    etau.
    specialize (CIHL xa). cbn in CIHL.
    match goal with
      |- euttG _ _ _ _ _ ?t _ => remember t
    end.
    clear CIHH.
    rewrite <- bind_ret_l.
    ebase.
    right. apply CIHL.
  - (* If we exit the first loop *)
    setoid_rewrite bind_ret_l.
    (* We setup a second coinductive point in the simulation.
       We just make sure to first get rid of the additional tau guard
       that we have encountered in the right of the equation to keep the second part clean.
     *)
    rewrite tau_euttge.
    generalize xb.
    ecofix CIH'.

    intros ?.
    (* We unfold a new step of computation *)
    rewrite unfold_iter; cbn.
    match goal with
      |- euttG _ _ _ _ _ ?t _ => remember t; rewrite unfold_iter; subst
    end.
    cbn.
    rewrite !bind_bind.
    (* We run g a first time on both sides *)
    ebind.
    econstructor; [reflexivity | intros [xb' | xc] ? <-].
    + (* We loop back in the second loop *)
      rewrite !bind_ret_l.
      etau.
    + rewrite !bind_ret_l.
      eret.
Qed.

End KTreeIterative.
