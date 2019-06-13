(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Events.State
     Events.StateFacts.

Import ITree.Basics.Basics.Monads.
Import Monads.

Open Scope cat_scope.

Section Kleisli.
  Variable m : Type -> Type.
  Variable S : Type.
  Context {EQM : EqM m}.
  Context {HM: Monad m}.
  Context {HEQP: @EqMProps m _ EQM}.
  Context {ML: @MonadLaws m _ HM}.
  
  Global Instance EqM_stateTM : EqM (stateT S m) :=
    fun a m1 m2 => forall s, eqm (m1 s) (m2 s).

  Global Instance EqMProps_stateTM : EqMProps (stateT S m) := _.
  constructor.
  - intros a.
    destruct HEQP.
    unfold eqm, EqM_stateTM. 
    repeat split; red; intros.
    +  reflexivity.
    + symmetry. auto.
    + etransitivity; eauto.
  - repeat red. intros a b x y f g H H0 s. 
    apply eqm_bind.
    + apply H.
    + destruct y0.
      simpl. apply H0.
  Qed.

  Context {IM: Iter (Kleisli m) sum}.
  Context {CM: Conway (Kleisli m) sum}.

  (* SAZ: Why are iter, bind, and ret shadowed by itree versions here? *)  
  Global Instance Iter_stateTM : Iter (Kleisli (stateT S m)) sum := 
  (fun (a b : Type) (f : a -> S -> m (S * (a + b))) (x:a) (s:S) => 
           @iter _ (Kleisli m) _ IM _ _ (fun (sa: S * a) => 
                   @bind m HM _ _ (f (snd sa) (fst sa))
                        (fun sab =>
                           match sab with
                           | (s, inl x) => @ret m HM _ (inl (s, x))
                           | (s, inr y) => @ret m HM _ (inr (s, y))
                           end)) (s, x)).
                                                                      

  Global Instance IterUnfold_stateTM : IterUnfold (Kleisli (stateT S m)) sum := _.
  Proof.
  destruct CM.
  unfold IterUnfold.
  intros a b f.
  repeat red.
  intros a0 s.
  unfold cat, Cat_Kleisli.
  unfold iter, Iter_stateTM.
  rewrite conway_unfold.  (* SAZ: why isn't iter_unfold exposed here? *)
  unfold cat, Cat_Kleisli.
  simpl.
  rewrite bind_bind.
  apply eqm_bind.
  + reflexivity.
  + destruct y as [s' [x | y]]; simpl.
    * rewrite bind_ret.
      reflexivity.
    * rewrite bind_ret.
      reflexivity.
  Qed.

  Global Instance IterNatural_stateTM : IterNatural (Kleisli (stateT S m)) sum := _.
  Proof.
    destruct CM.
    unfold IterNatural.
    intros a b c f g.
    repeat red.
    intros a0 s.
    setoid_rewrite conway_natural.
    apply conway_proper_iter.
    repeat red.
    destruct a1. 
    unfold cat, Cat_Kleisli.
    cbn. 
    rewrite! bind_bind. 
    apply eqm_bind.
    - reflexivity.
    - destruct y as [s' [x | y]]; simpl.
      + rewrite bind_ret.
        cbn. unfold cat, Cat_Kleisli. cbn.
        rewrite bind_bind.
        rewrite bind_ret.
        rewrite bind_ret.
        cbn.
        unfold id_, Id_Kleisli. unfold pure. rewrite bind_ret. reflexivity.
      + rewrite bind_ret.
        cbn. unfold cat, Cat_Kleisli. cbn.
        rewrite bind_bind.
        apply eqm_bind.
        * reflexivity.
        * destruct y0.
          cbn.
          rewrite bind_ret. reflexivity.
  Qed.

  Global Instance Proper_Iter_stateTM : forall a b, @Proper (Kleisli (stateT S m) a (a + b) -> (Kleisli (stateT S m) a b)) (eq2 ==> eq2) iter.
  Proof.
    destruct CM.
    repeat red.
    intros a b x y H a0 s.
    apply conway_proper_iter.
    repeat red.
    destruct a1.
    cbn.
    apply eqm_bind.
    - apply H.
    - destruct y0 as [s' [x1|y1]]; reflexivity.
 Qed.

  Global Instance IterDinatural_stateTM : IterDinatural (Kleisli (stateT S m)) sum := _.
  Proof.
    destruct CM.
    unfold IterDinatural.
    intros a b c f g a0 s.
    unfold iter, Iter_stateTM. cbn.
    rewrite conway_unfold.
    unfold cat, Cat_Kleisli.
    repeat rewrite bind_bind. cbn.
    apply eqm_bind.
    - reflexivity.
    - destruct y as [s' [x | y]]; cbn.
      +
  Abort.
(*        
        Check ((fun y : S * (a + c) =>
                  
     bind (let (s0, s1) := y in match s1 with
                                | inl x0 => ret (inl (s0, x0))
                                | inr y0 => ret (inr (s0, y0))
                                end)
       (fun y0 : S * a + S * c =>
        case_
          (@iter _ (Kleisli m) sum IM _ _
             (fun sa : S * a =>
              bind (bind (f (snd sa) (fst sa)) (fun sa0 : S * (b + c) => case_ g inr_ (snd sa0) (fst sa0)))
                (fun sab : S * (a + c) =>
                 let (s0, s1) := sab in match s1 with
                                        | inl x0 => ret (inl (s0, x0))
                                        | inr y1 => ret (inr (s0, y1))
                                        end)))))).
      
  
  Global Instance IterCodiagonal_stateTM : IterCodiagonal (Kleisli (stateT S m)) sum := _.
  Proof.
    destruct CM.
    unfold IterCodiagonal.
    intros a b f a0 s.
    unfold iter, Iter_stateTM.
    cbn.
    About bind_bind.
    
    setoid_rewrite bind_bind.
    

    assert (@eq2 _ (Kleisli m) _ _ _
    (fun sa : S * a =>
     bind
       ((@iter _ (Kleisli m) sum IM _ _)
          (fun sa0 : S * a =>
           bind (f (snd sa0) (fst sa0))
             (fun sab : S * (a + (a + b)) =>
              let (s0, s1) := sab in match s1 with
                                     | inl x => ret (inl (s0, x))
                                     | inr y => ret (inr (s0, y))
                                     end)) (fst sa, snd sa))
       (fun sab : S * (a + b) =>
        let (s0, s1) := sab in match s1 with
                               | inl x => ret (inl (s0, x))
                               | inr y => ret (inr (s0, y))
                               end))


    
    Check (iter (fun sa : S * a =>
     bind
       (iter
          (fun sa0 : S * a =>
           bind (f (snd sa0) (fst sa0))
             (fun sab : S * (a + (a + b)) =>
              let (s0, s1) := sab in match s1 with
                                     | inl x => ret (inl (s0, x))
                                     | inr y => ret (inr (s0, y))
                                     end)) (fst sa, snd sa))
       (fun sab : _ =>
        let (s0, s1) := sab in match s1 with
                               | inl x => ret (inl (s0, x))
                               | inr y => ret (inr (s0, y))
                               end))).

    
    assert (pointwise_relation _ eq eq2
              (fun sa : S * a =>
                 bind
                   (iter
                      (fun sa0 : S * a =>
                         bind (f (snd sa0) (fst sa0))
                              (fun sab : S * (a + (a + b)) =>
                                 let (s0, s1) := sab in match s1 with
                                                        | inl x => ret (inl (s0, x))
                                                        | inr y => ret (inr (s0, y))
                                                        end)) (fst sa, snd sa))
                   (fun sab : S * (a + b) =>
                      let (s0, s1) := sab in match s1 with
                                             | inl x => ret (inl (s0, x))
                                             | inr y => ret (inr (s0, y))
                                             end))
                _).
                


    
    apply conway_proper_iter.
    repeat red.
    destruct a1.
    
  
  Global Instance IterDinatural_stateTM : IterDinatural (Kleisli (stateT S m)) sum := _.
  Proof.
    destruct CM.
    unfold IterDinatural.
    intros a b c f g a0 s.

    unfold iter, Iter_stateTM.
    unfold cat, Cat_Kleisli. cbn.
    remember (fun sa : S * a =>
     bind (bind (f (snd sa) (fst sa)) (fun sa0 : S * (b + c) => case_ g inr_ (snd sa0) (fst sa0)))
       (fun sab : S * (a + c) =>
        let (s0, s1) := sab in match s1 with
                               | inl x => ret (inl (s0, x))
                               | inr y => ret (inr (s0, y))
                               end)) as h.
    

    
    unfold Kleisli, stateT in f,g.
    unfold Kleisli, stateT, Cat_Kleisli, CoprodInr_Kleisli, Id_Kleisli, pure. cbn.
    setoid_rewrite conway_dinatural.
    

    

    unfold cat at 1, Cat_Kleisli.
    setoid_rewrite bind_bind.
    rewrite conway_dinatural.
    rewrite conway_unfold.
    unfold cat, Cat_Kleisli. cbn.
    repeat rewrite bind_bind.
    apply eqm_bind.
    - reflexivity.
    - destruct y as [s' [x | y]]; cbn.
      + 
    
    
  
  Global Instance Conway_stateTM : Conway (Kleisli (stateT S m)) sum := _.
  destruct CM. destruct HEQP.
  constructor.
  - 
  - unfold IterNatural.
*)    
    
  
End Kleisli.
