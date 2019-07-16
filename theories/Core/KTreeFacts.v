(** * Facts about [aloop] and [loop] *)

(* begin hide *)
From Coq Require Import
     Program
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
     Core.ITreeDefinition
     Core.ITreeMonad
     Core.KTree
     Eq.Eq
     Eq.UpToTaus.

Import ITreeNotations.
Import CatNotations.
Local Open Scope itree.
(* end hide *)

(** ** [ITree.aloop] *)

Lemma bind_iter {E A B C} (f : A -> itree E (A + B)) (g : B -> itree E (B + C))
  : forall x,
    (ITree.iter f x >>= ITree.iter g)
  ≈ ITree.iter (fun ab =>
       match ab with
       | inl a => ITree.map inl (f a)
       | inr b => ITree.map (bimap inr (id_ _)) (g b)
       end) (inl x).
Proof.
  einit. ecofix CIH. intros.
  rewrite !unfold_iter. unfold ITree._iter.
  rewrite bind_map, bind_bind.
  ebind; econstructor; try reflexivity.
  intros [a | b] _ [].
  - rewrite bind_tau. etau.
  - rewrite bind_ret, tau_eutt.
    revert b. ecofix CIH'. intros.
    rewrite !unfold_iter. unfold ITree._iter.
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
  ginit. gcofix CIH. intros.
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

(** ** [iter] *)

Lemma eqit_mon {E R1 R2} (RR RR' : R1 -> R2 -> Prop) b1 b2 :
  (RR <2= RR') ->
  (eqit RR b1 b2 <2= @eqit E _ _ RR' b1 b2).
Proof.
  intros.
  eapply paco2_mon_bot; eauto.
  intros ? ? ?. red.
  induction 1; auto.
Qed.

Instance eq_itree_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          ((eq ==> eq_itree eq) ==> pointwise_relation _ (eq_itree eq))
          iter.
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  unfold iter, Iter_Kleisli.
  eapply (eq_itree_iter' eq); auto.
  intros; eapply eqit_mon, EQ_BODY; auto.
  intros [] _ []; auto.
Qed.

Instance eutt_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          (pointwise_relation _ (eutt eq) ==> pointwise_relation _ (eutt eq))
          iter.
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  unfold iter, Iter_Kleisli.
  eapply (eutt_iter' eq); auto.
  intros ? _ []; eapply eqit_mon, EQ_BODY; auto.
  intros [] _ []; auto.
Qed.

Definition eutt_iter_gen {F A B R S} :
  @Proper ((A -> itree F (A + B)) -> A -> itree F B)
          ((R ==> eutt (sum_rel R S)) ==> R ==> (eutt S))
          KTree.iter.
Proof.
  do 3 red;
  intros body1 body2 EQ_BODY x y Hxy. red in EQ_BODY.
  eapply eutt_iter'; eauto.
Qed.

Instance eq2_ktree_iter {E A B} :
  @Proper (ktree E A (A + B) -> ktree E A B)
          (eq2 ==> eq2)
          iter.
Proof. apply eutt_iter. Qed.

Section KTreeIterative.

Lemma unfold_iter_ktree {E A B} (f : ktree E A (A + B)) (a0 : A) :
  iter f a0 ≅
    ab <- f a0 ;;
    match ab with
    | inl a => Tau (iter f a)
    | inr b => Ret b
    end.
Proof.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree, cat.
  rewrite unfold_iter; cbn.
  eapply eqit_bind; try reflexivity.
Qed.

Instance IterUnfold_ktree {E} : IterUnfold (ktree E) sum.
Proof.
  repeat intro.
  rewrite unfold_iter_ktree.
  do 2 red. unfold cat, Cat_Kleisli; cbn.
  eapply eutt_clo_bind; try reflexivity.
  intros [] ? []; try rewrite tau_eutt; reflexivity.
Qed.

Instance IterNatural_ktree {E} : IterNatural (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, CoprodCase_Kleisli, case_sum, cat, Cat_Kleisli.
  cbn.
  revert a0.
  einit. ecofix CIH. intros.
  rewrite 2 unfold_iter_ktree.
  rewrite !bind_bind.
  ebind; econstructor; try reflexivity.
  intros [] ? [].
  - rewrite bind_tau, 2 bind_ret. etau.
  - rewrite bind_ret, !bind_bind. setoid_rewrite bind_ret. rewrite bind_ret2.
    reflexivity.
Qed.

Lemma iter_dinatural_ktree {E A B C}
      (f : ktree E A (C + B)) (g : ktree E C (A + B)) (a0 : A)
  : iter (fun a =>
      cb <- f a ;;
      match cb with
      | inl c => Tau (g c)
      | inr b => Ret (inr b)
      end) a0
  ≅ cb <- f a0 ;;
     match cb with
     | inl c0 => Tau (iter (fun c =>
         ab <- g c ;;
         match ab with
         | inl a => Tau (f a)
         | inr b => Ret (inr b)
         end) c0)
     | inr b => Ret b
     end.
Proof.
  revert A B C f g a0.
  ginit. gcofix CIH. intros.
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
    * rewrite bind_ret. gstep; econstructor; auto.
  }
  { rewrite bind_ret. gstep; constructor; auto. }
Qed.

Instance IterDinatural_ktree {E} : IterDinatural (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, CoprodCase_Kleisli, case_sum, cat, Cat_Kleisli.
  cbn.
  transitivity (iter (fun t =>
                        x <- f t;;
                        match x with
                        | inl a1 => Tau (g a1)
                        | inr b0 => Ret (inr b0)
                        end) a0).
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
  ≅ iter (fun a =>
       r <- f a ;;
       match r with
       | inl a' => Ret (inl a')
       | inr (inl a') => Ret (inl a')
       | inr (inr b) => Ret (inr b)
       end) a0.
Proof.
  revert a0.
  ginit. gcofix CIH. intros.
  rewrite unfold_iter_ktree.
  rewrite (unfold_iter_ktree (fun _ => _ _ _)).
  rewrite unfold_iter_ktree, !bind_bind.
  guclo eqit_clo_bind. econstructor. reflexivity.
  intros [| []] ? [].
  - rewrite bind_ret, bind_tau.
    gstep. constructor.
    revert a.
    gcofix CIH'. intros.
    rewrite unfold_iter_ktree.
    rewrite (unfold_iter_ktree (fun _ => _ _ _)).
    rewrite !bind_bind.
    guclo eqit_clo_bind. econstructor. reflexivity.
    intros [| []] ? [].
    + rewrite bind_tau, bind_ret. gstep; constructor; auto with paco.
    + rewrite 2 bind_ret. gstep; constructor; auto with paco.
    + rewrite 2 bind_ret. gstep; constructor; auto.
  - rewrite 2 bind_ret.
    gstep; constructor; auto with paco.
  - rewrite 2 bind_ret.
    gstep; reflexivity.
Qed.

Instance IterCodiagonal_ktree {E} : IterCodiagonal (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, CoprodCase_Kleisli, case_sum, cat, Cat_Kleisli.
  cbn.
  rewrite iter_codiagonal_ktree.
  apply eutt_iter.
  intros a1.
  eapply eutt_clo_bind.
  reflexivity.
  intros [| []] ? []; rewrite ?tau_eutt; reflexivity.
Qed.

Global Instance Iterative_ktree {E} : Iterative (ktree E) sum.
Proof.
  split; typeclasses eauto.
Qed.

End KTreeIterative.
