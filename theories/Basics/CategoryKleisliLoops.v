(** * Facts about [aloop] and [loop] for the Kleisli categoy *)

(* begin hide *)
From Coq Require Import
     Program
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Function.


Import CatNotations.
Import MonadNotation.
(* end hide *)

Open Scope cat_scope.
Open Scope kleisli_scope.
Open Scope monad_scope.

Section LoopFacts.

  Context {m : Type -> Type}.
  Context {EQM : EqM m}.
  Context `{Monad m}.
  Context `{@EqMProps m _ EQM}.
  Context `{@MonadLaws m EQM _}.
  Context `{@MonadProperOps m EQM _}.
  Context `{ALoop m}.
  
  (* aloop : forall M : Type -> Type, ALoop M -> forall R I : Type, (I -> M I + R) -> I -> M R *)
  Class ALoopProper :=
    {
      Proper_aloop :> forall a b,
          (@Proper ((a -> (sum (m a) b))%type -> (a -> m b%type))
                   (pointwise_relation _ (sum_rel eqm eq) ==> pointwise_relation _ eqm)
                   aloop)
    }.

  Context `{ALoopProper}.
      
  Instance Proper_iter_Kleisli
           {a b}
    : @Proper (Kleisli m a (a + b) -> Kleisli m a b)
              (eq2 ==> eq2) iter.
  Proof.
    repeat red.
    intros x y H6 a0.
    unfold iter, Iter_Kleisli.
    apply Proper_aloop.
    repeat red.
    destruct a1.
    - apply inl_morphism. apply H6.
    - apply inr_morphism. reflexivity.
  Qed.

  (* Check (fun a f g => (aloop (fun x => match x with *)
  (*                           | inl ma => y <- ma ;; bind (aloop f y) g *)
  (*                           | inr r => g r *)
  (*                           end) a)). *)
  
  Class ALoopProps :=
    {
      aloop_unfold :> forall {I R} (f : I -> m I + R) a, eqm (aloop f a)
                                                       (match f a with
                                                         | inl ma => y <- ma ;; aloop f y
                                                         | inr r => ret r
                                                         end)
    (* ; bind_aloop :> forall {I R S} (f : I -> m I + R) (a:I) (g : R -> m S), *)
    (*       eqm (bind (aloop f a) g) *)
    (*           (aloop (fun x => match x with *)
    (*                         | inl ma => y <- ma ;; bind (aloop f y) g *)
    (*                         | inr r => g r *)
    (*                         end) a) *)

    }.

  
  Context `{ALoopProps}.
  
(** ** [aloop] *)


(*
Lemma iter_bind {A B C} (f : Kleisli m A (A + B)) (g : Kleisli m B (B + C)) : 
    (iter f >>> iter g) ⩯  (iter (f >>> g)).


      aloop (fun ab =>
       match ab with
       | inl a => inl (ITree._aloop id (fun a => Ret (inl a))
                                    (bimap (id_ _) inr (f a)))
       | inr b => apply_Fun (bimap (ITree.map inr) (id_ _)) (g b)
       end) (inl x).
Proof.
  einit. ecofix CIH. intros.
  rewrite !unfold_aloop. unfold ITree._aloop.
  destruct (f x) as [t | b]; cbn.
  - unfold id. rewrite bind_tau. etau. rewrite !bind_bind.
    ebind. econstructor; try reflexivity.
    intros. subst. rewrite bind_ret. eauto with paco.
  - rewrite bind_ret, tau_eutt, bind_ret.
    revert b. ecofix CIH'. intros.
    rewrite !unfold_aloop. unfold ITree._aloop.
    destruct (g b) as [t' | c]; cbn; eauto with paco.
    rewrite bind_map. etau.
    ebind. econstructor; try reflexivity.
    intros. subst. eauto with paco.
Qed.
*)

(*
Lemma eqm_aloop' {E I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E I1 + R1)
      (body2 : I2 -> itree E I2 + R2)
      (eutt_body
       : forall j1 j2, RI j1 j2 -> sum_rel (eq_itree RI) RR (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @eq_itree E _ _ RR (ITree.aloop body1 i1) (ITree.aloop body2 i2).
Proof.
  ginit. gcofix CIH. intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_aloop.
  destruct eutt_body; cbn; eauto with paco.
  gstep. econstructor. guclo eqit_clo_bind.
  gstep. constructor; eauto.
Qed.

Lemma eutt_aloop' {E I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E I1 + R1)
      (body2 : I2 -> itree E I2 + R2)
      (eutt_body
       : forall j1 j2, RI j1 j2 -> sum_rel (eutt RI) RR (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @eutt E _ _ RR (ITree.aloop body1 i1) (ITree.aloop body2 i2).
Proof.
  einit. ecofix CIH. intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_aloop.
  destruct eutt_body; cbn; eauto with paco.
  etau. ebind. econstructor; eauto with paco.
Qed.

(** ** [iter] *)

Instance eq_itree_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          ((eq ==> eq_itree eq) ==> pointwise_relation _ (eq_itree eq))
          iter.
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  unfold iter, Iter_ktree.
  eapply (eq_itree_aloop' eq).
  intros [] ? []; constructor; auto. reflexivity.
Qed.

Instance eutt_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          (pointwise_relation _ (eutt eq) ==> pointwise_relation _ (eutt eq))
          iter.
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  unfold iter, Iter_ktree.
  eapply (eutt_aloop' eq).
  intros [] ? []; constructor; auto. reflexivity.
Qed.

Definition eutt_iter_gen {F A B R S} :
  @Proper ((A -> itree F (A + B)) -> A -> itree F B)
          ((R ==> eutt (sum_rel R S)) ==> R ==> (eutt S))
          KTree.iter.
Proof.
  do 3 red;
  intros body1 body2 EQ_BODY x y Hxy. red in EQ_BODY.
  unfold iter, Iter_ktree.
  eapply (eutt_aloop' (sum_rel R S)); intros.
  - destruct H; constructor; auto.
  - constructor; auto.
Qed.

Instance eq2_ktree_iter {E A B} :
  @Proper (ktree E A (A + B) -> ktree E A B)
          (eq2 ==> eq2)
          iter.
Proof. apply eutt_iter. Qed.
 *)




(*
Lemma unfold_iter_ktree {E A B} (f : ktree E A (A + B)) (a0 : A) :
  iter f a0 ≅ Tau (
    ab <- f a0 ;;
    match ab with
    | inl a => iter f a
    | inr b => Ret b
    end).
Proof.
  unfold iter, Iter_ktree, cat, Cat_ktree, ITree.cat.
  rewrite unfold_aloop; cbn.
  pstep; constructor; left.
  eapply eqit_bind; try reflexivity.
  intros [].
  reflexivity.
  rewrite unfold_aloop; cbn.
  reflexivity.
Qed.
*)

  Lemma unfold_iter_def {A B} (f : Kleisli m A (A + B)) (a0 : A) :
    eqm (iter f a0) (ab <- f a0 ;; match ab with
                             | inl a => iter f a
                             | inr b => ret b
                                  end).
  Proof.
    unfold iter, Iter_Kleisli.
    rewrite aloop_unfold.
    apply eqm_bind.
    - reflexivity.
    - destruct y.
      + reflexivity.
      + rewrite aloop_unfold. reflexivity.
  Qed.
    
  
Instance IterUnfold_Kleisli : IterUnfold (Kleisli m) sum.
Proof.
  unfold IterUnfold. intros a b f x.
  rewrite unfold_iter_def.
  unfold cat, Cat_Kleisli.
  apply eqm_bind.
  - reflexivity.
  - destruct y; reflexivity.
Qed.


Instance IterNatural_ktree : IterNatural (Kleisli m) sum.
Proof.
  repeat red.
  intros a b c f g a0.
  unfold iter, Iter_Kleisli.
  unfold bimap, Bimap_Coproduct, case_, CoprodCase_Kleisli, case_sum.
  unfold cat, Cat_Kleisli.
  rewrite! aloop_unfold.
  cbn.
  rewrite! bind_bind.
  apply Proper_bind.
  - reflexivity.
  - repeat red.
    destruct a1.
    + rewrite bind_bind.
      unfold id_, Id_Kleisli, pure.
      rewrite bind_ret.
      unfold inl_, CoprodInl_Kleisli, pure.
      rewrite bind_ret.
Abort.      
      
(*  
  unfold id_, Id_Kleisli.
  unfold pure.
  rewrite! unfold_iter_def.
  cbn.
  rewrite! bind_bind.
  apply Proper_bind.
  - reflexivity.
  - repeat red. destruct a1.
    + rewrite bind_bind. 
      rewrite bind_ret.
      unfold id, inl_, CoprodInl_Kleisli, pure.
      rewrite bind_ret.
      rewrite! unfold_iter_def.
      cbn. rewrite! bind_bind.
      apply Proper_bind.
      * reflexivity.
      * repeat red.
        destruct a2.
        ** rewrite bind_bind. rewrite bind_ret.
           rewrite bind_ret.
           
      
      SearchAbout aloop.
*)    
  
(*
Lemma iter_dinatural_ktree {E A B C}
      (f : ktree E A (C + B)) (g : ktree E C (A + B)) (a0 : A)
  : iter (fun a =>
      cb <- f a ;;
      match cb with
      | inl c => Tau (g c)
      | inr b => Ret (inr b)
      end) a0
  ≅ Tau (
       cb <- f a0 ;;
       match cb with
       | inl c0 => iter (fun c =>
         ab <- g c ;;
         match ab with
         | inl a => Tau (f a)
         | inr b => Ret (inr b)
         end) c0
       | inr b => Ret b
       end).
Proof.
  revert A B C f g a0.
  ginit. gcofix CIH. intros.
  rewrite unfold_iter_ktree.
  gstep; econstructor.
  rewrite bind_bind.
  guclo eqit_clo_bind. econstructor. try reflexivity.
  intros [] ? [].
  { rewrite bind_tau.
    (* TODO: here we should be able to apply symmetry and be done. *)
    rewrite unfold_iter_ktree.
    gstep; econstructor.
    rewrite bind_bind.
    guclo eqit_clo_bind. econstructor. try reflexivity.
    intros [] ? [].
    { rewrite bind_tau.
      eauto with paco.
    }
    { rewrite bind_ret. gstep; econstructor; auto.
    }
  }
  { rewrite bind_ret. gstep; constructor; auto.
  }
Qed.

Instance IterDinatural_ktree {E} : IterDinatural (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, Case_ktree, case_sum, cat, Cat_ktree, ITree.cat.
  transitivity (iter (fun t =>
                        x <- f t;;
                        match x with
                        | inl a1 => Tau (g a1)
                        | inr b0 => inr_ b0
                        end) a0).
  - apply eutt_iter; intros x.
    eapply eutt_clo_bind.
    reflexivity.
    intros [] ? [].
    rewrite tau_eutt; reflexivity.
    reflexivity.
  - rewrite iter_dinatural_ktree.
    rewrite tau_eutt.
    eapply eutt_clo_bind.
    reflexivity.
    intros [] ? [].
    + apply eutt_iter; intros x.
      eapply eutt_clo_bind.
      reflexivity.
      intros [] ? [].
      rewrite tau_eutt; reflexivity.
      reflexivity.
    + reflexivity.
Qed.

Lemma iter_codiagonal_ktree {E A B} (f : ktree E A (A + (A + B))) (a0 : A)
  : iter (iter f) a0
  ≅ Tau (iter (fun a =>
       r <- f a ;;
       match r with
       | inl a' => Ret (inl a')
       | inr (inl a') => Tau (Ret (inl a'))
       | inr (inr b) => Ret (inr b)
       end) a0).
Proof.
  revert a0.
  ginit. gcofix CIH. intros.
  rewrite unfold_iter_ktree.
  rewrite (unfold_iter_ktree (fun _ => _ _ _)).
  gstep; constructor.
  revert a0.
  gcofix CIH'. intros.
  rewrite bind_bind.
  rewrite unfold_iter_ktree.
  rewrite bind_tau, bind_bind.
  gstep; constructor.
  guclo eqit_clo_bind. econstructor. reflexivity.
  intros [| []] ? [].
  - rewrite bind_ret.
    rewrite (unfold_iter_ktree (fun _ => _ _ _)).
    auto with paco.
  - rewrite bind_tau, 2 bind_ret.
    auto with paco.
  - rewrite 2 bind_ret.
    gstep; reflexivity.
Qed.

Instance IterCodiagonal_ktree {E} : IterCodiagonal (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, Case_ktree, case_sum, cat, Cat_ktree, ITree.cat.
  rewrite iter_codiagonal_ktree.
  rewrite tau_eutt.
  apply eutt_iter.
  intros a1.
  eapply eutt_clo_bind.
  reflexivity.
  intros [| []] ? []; rewrite ?tau_eutt; reflexivity.
Qed.

Global Instance Conway_ktree {E} : Conway (ktree E) sum.
Proof.
  split; typeclasses eauto.
Qed.

End KTreeConway.
 *)

End LoopFacts.