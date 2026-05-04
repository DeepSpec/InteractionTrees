(* Rtodo: automatic to_mon for rewriting *)

(** * Facts about [aloop] and [loop] *)

(* begin hide *)
From Stdlib Require Import
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Basics.Utils 
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
     .

Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.
(* end hide *)

Ltac unfold_ktree :=
  unfold
    Monad.eq1, Eq1_ITree,
    Basics.iter, MonadIter_itree,
    assoc_l, AssocL_Coproduct,
    bimap, Bimap_Coproduct,
    cat, Cat_Kleisli, inl_, Inl_Kleisli, inr_, Inr_Kleisli, case_, Case_Kleisli, case_sum,
    lift_ktree_; cbn.

(** ** [ITree.aloop] *)


From Corelib Require Import Program.Tactics. 

Ltac under_forall' tac := 
let dummy := fresh "dummy" in   
assert (dummy : True) by constructor; 
          intros; 
          tac; 
          revert_until dummy; 
          clear dummy. 
Ltac to_mon := under_forall' to_mon_core. 

Lemma bind_iter {E A B C} (f : A -> itree E (A + B)) (g : B -> itree E (B + C))
  : forall x,
    (ITree.bind (ITree.iter f x) (ITree.iter g))
  ≈ ITree.iter (fun ab =>
       match ab with
       | inl a => ITree.map inl (f a)
       | inr b => ITree.map (bimap inr (id_ _)) (g b)
       end) (inl x).
Proof.
  coinduction. 
  (* this proof should follow from the facts about elem *)
  intros.
  (* Unset Printing Notations.  *)
  (* these rewrites must go through *)
  (* need eq_itree proper up to everything *)
  rewrite !unfold_iter.
  rewrite bind_map, bind_bind.
  ebind. 
  intros [a | b] _ [].
  - rewrite bind_tau. taus.
    eapply CIH. 
  - rewrite bind_ret_l, tau_euttge.
  (* question: why doesn't accumulate acc work? *)
    do 2 step. revert b. coinduction. intros. 
    rewrite !unfold_iter.
    rewrite bind_map.
    ebind. 
    intros [b' | c''] _ []; cbn.
    + now taus.
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
  coinduction c cih. intros. 
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  eapply eqit_bind_chain. 
  do 2 step. apply eutt_body. 
  intros ? ? []; econstructor; eauto. 
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
  coinduction c CIH. intros. 
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  ebind.
  do 2 step; eauto. 
  intros ? ? []; econstructor; eauto. 
Qed.

Lemma eutt_iter'' {E I1 I2 R1 R2}
      (RI1 RI2 : I1 -> I2 -> Prop)
      (HSUB: RI2 <= RI1)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2))
      (eutt_body
      : forall j1 j2, RI1 j1 j2 -> eutt (sum_rel RI2 RR) (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI1 i1 i2),
    @eutt E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  coinduction c CIH. intros. 
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  ebind. 
  do 2 step; eauto. 
  intros ? ? []; econstructor; eauto. now apply CIH, HSUB.
Qed.

Definition eutt_iter_gen' {F A B R1 R2 S} (HS : R2 <= R1) :
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
  unfold_ktree.
  eapply (eq_itree_iter' eq); auto.
  intros; eapply eqit_mono, EQ_BODY; auto.
  intros [] _ []; auto; econstructor; subst; auto.
Qed.

#[global] Instance eutt_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          (pointwise_relation _ (eutt eq) ==> pointwise_relation _ (eutt eq))
          (iter (C := ktree E)).
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  unfold_ktree.
  eapply (eutt_iter' eq); auto.
  intros ? _ []; eapply eqit_mono, EQ_BODY; auto.
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
  repeat intro. unfold_ktree. rewrite unfold_iter_ktree.
  eapply eutt_bind_eutt; try reflexivity.
  intros [] ? []; try rewrite tau_eutt; reflexivity.
Qed.

#[global] Instance IterNatural_ktree {E} : IterNatural (ktree E) sum.
Proof.
  repeat intro. unfold_ktree.
  revert a0.
  coinduction c' CIH. intros. 
  rewrite 2 unfold_iter_ktree.
  rewrite !bind_bind.
  ebind. 
  intros [] ? [].
  - rewrite bind_tau, 2 bind_ret_l. now taus. 
  - rewrite bind_ret_l, !bind_bind. setoid_rewrite bind_ret_l. rewrite bind_ret_r.
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
  revert A B C f g a0. 
  coinduction c CIH. intros. 
  rewrite unfold_iter_ktree.
  rewrite bind_bind.
  ebind. 
  intros [] ? [].
  (* Tour: show this *)
  (* old TODO: here we should be able to apply symmetry and be done. *)
  (* Win! *)
  - rewrite bind_tau. taus. symmetry. eapply CIH. 
  - rewrite bind_ret_l. reflexivity. 
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
    eapply eutt_bind_eutt.
    reflexivity.
    intros [] ? [].
    rewrite tau_eutt; reflexivity.
    reflexivity.
  - rewrite iter_dinatural_ktree.
    eapply eutt_bind_eutt.
    reflexivity.
    intros [] ? [].
    + rewrite tau_eutt.
      apply eutt_iter; intros x.
      eapply eutt_bind_eutt.
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
  coinduction c CIH. intros. 
  rewrite unfold_iter_ktree.
  rewrite (unfold_iter_ktree (fun _ => _ _ _)).
  rewrite unfold_iter_ktree, !bind_bind.
  ebind. 
  intros [| []] ? [].
  - rewrite bind_ret_l, bind_tau.
    taus. 
    revert a.
    accumulate acc. 
    intros.
    rewrite unfold_iter_ktree.
    rewrite (unfold_iter_ktree (fun _ => _ _ _)).
    rewrite !bind_bind.
    ebind. 
    intros [| []] ? [].
    + rewrite bind_tau, bind_ret_l. now taus. 
    + rewrite 2 bind_ret_l. now taus. 
    + rewrite 2 bind_ret_l. reflexivity. 
  - rewrite 2 bind_ret_l.
    now taus. 
  - rewrite 2 bind_ret_l.
    reflexivity. 
Qed.

#[global] Instance IterCodiagonal_ktree {E} : IterCodiagonal (ktree E) sum.
Proof.
  repeat intro. unfold_ktree.
  rewrite iter_codiagonal_ktree.
  apply eutt_iter.
  intros a1.
  eapply eutt_bind_eutt.
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
  unfold_ktree.
  (* We move to the eworld *)
  repeat red. 
  (* First coinductive point in the simulation: at the entry point of the iteration over f *)
  coinduction c' CIH. intros.   
  rewrite bind_ret_l.
  (* We unfold one step on both sides *)
  rewrite unfold_iter. 
  
  rewrite unfold_iter.
  rewrite !bind_bind.
  ebind.
  (* We run f a first time on both side *)
  intros [xa | xb] ? <-.
  - (* If we loop back to f, we can conclude by coinduction *)
    rewrite ! bind_ret_l.
    rewrite bind_tau.
    taus. 
    specialize (CIH xa).
    symmetry. 
    rewrite <- bind_ret_l. symmetry. 
    apply CIH. 
  - (* If we exit the first loop *)
    rewrite ! bind_ret_l.
    (* We setup a second coinductive point in the simulation.
       We just make sure to first get rid of the additional tau guard
       that we have encountered in the right of the equation to keep the second part clean. 
     *)
    rewrite tau_euttge.
    do 2 step. 
    generalize xb.
    coinduction c'' CIH'. intros. 
    (* We unfold a new step of computation *)
    rewrite 2 unfold_iter. 
    rewrite !bind_bind.
    (* We run g a first time on both sides *)
    ebind.
    intros [xb' | xc] ? <-.
    + (* We loop back in the second loop *)
      rewrite !bind_ret_l.
      taus.
      apply CIH'.  
    + rewrite !bind_ret_l.
      reflexivity. 
Qed.

End KTreeIterative.
