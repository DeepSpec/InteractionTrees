From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Section ITreeDijkstra.

  Context (E : Type -> Type).


  Inductive can_converge {A : Type} (a : A) : itree E A -> Prop :=
    | conv_ret (t : itree E A) : t ≈ Ret a -> can_converge a t
    | conv_vis (t : itree E A ) {B : Type} (e : E B) (k : B -> itree E A) (b : B) : 
        t ≈ Vis e k -> can_converge a (k b) -> can_converge a t.


  Variant must_divergeF {A : Type} (F : itree E A -> Prop) : itree' E A -> Prop :=
    | MDivTau (t : itree E A) : F t -> must_divergeF F (TauF t)
    | MDivVis (B : Type) (k : B -> itree E A) (e : E B) : 
        (forall b, F (k b)) -> must_divergeF F (VisF e k).
  Hint Constructors must_divergeF.

  Definition must_diverge_ {A} (sim : itree E A -> Prop) t := must_divergeF sim (observe t).

  Lemma must_divergeF_mono {A} (sim sim' : itree E A -> Prop) t
        (IN : must_divergeF sim t)
        (LE : sim <1= sim') : must_divergeF sim' t.
  Proof.
    induction IN; eauto. 
  Qed.

  Lemma must_divergeF_mono' {A} : monotone1 (@must_diverge_ A).
  Proof.
    unfold must_diverge_.
    red. intros. eapply must_divergeF_mono; eauto.
  Qed.
  Hint Resolve must_divergeF_mono' : paco. 

  Definition must_diverge {A : Type} := paco1 (@must_diverge_ A) bot1.

  Instance eutt_proper_must_diverge {A R} : Proper (eutt R ==> iff) (@must_diverge A).
  Proof.
    intros t1 t2 Ht. split.
    - revert t1 t2 Ht. pcofix CIH. intros t1 t2 Ht Hdiv.
      punfold Ht. unfold_eqit. pfold. red. punfold Hdiv. red in Hdiv.
      induction Ht.
      + inversion Hdiv.
      + constructor. inversion Hdiv. subst. right.
        pclearbot.
        eapply CIH; eauto.
      + constructor. inversion Hdiv. subst. apply inj_pair2 in H2.
        subst. intros. right. inversion Hdiv. subst. apply inj_pair2 in H4.
        subst. pclearbot. eapply CIH; eauto. apply H2.
      + apply IHHt. inversion Hdiv. subst. pclearbot. punfold H0.
      + constructor. left. pfold. apply IHHt. auto.
     - revert t1 t2 Ht. pcofix CIH. intros t1 t2 Ht Hdiv.
      punfold Ht. unfold_eqit. pfold. red. punfold Hdiv. red in Hdiv.
      induction Ht.
      + inversion Hdiv.
      + constructor. inversion Hdiv. subst. right.
        pclearbot.
        eapply CIH; eauto.
      + constructor. inversion Hdiv. subst. apply inj_pair2 in H2.
        subst. intros. right. inversion Hdiv. subst. apply inj_pair2 in H4.
        subst. pclearbot. eapply CIH; eauto. apply H2.
      +  constructor. left. pfold. apply IHHt. auto. 
      +  apply IHHt. inversion Hdiv. subst. pclearbot. punfold H0.
  Qed.
 
  Instance eutt_proper_con_converge {A} {a : A} : Proper (eutt eq ==> iff) (can_converge a).
  Proof.
    intros t1 t2 Ht. split; intros.
    - induction H.
      + apply conv_ret; auto. rewrite <- Ht. auto. 
      + eapply conv_vis with (e0 := e); eauto. rewrite <- H.
        symmetry. auto.
    - induction H.
      + apply conv_ret; auto. rewrite Ht. auto.
      + eapply conv_vis with (e0 := e); eauto. rewrite Ht.
        auto.
  Qed.

  Lemma not_converge_to_must_diverge : forall (A : Type) (t : itree E A), 
     (forall a, ~ can_converge a t) -> must_diverge t.
  Proof.
    intros A. pcofix CIH. intros t Hcon. pfold.
    red. destruct (observe t) eqn : Heq;
    specialize (itree_eta t) as Ht; rewrite Heq in Ht.
    - exfalso. apply (Hcon r0). rewrite Ht. constructor. reflexivity.
    - constructor. right. apply CIH.
      setoid_rewrite Ht in Hcon. setoid_rewrite tau_eutt in Hcon.
      auto.
    - constructor. right. apply CIH.
      intros a Hcontra. setoid_rewrite Ht in Hcon.
      apply (Hcon a). eapply conv_vis; try reflexivity; eauto.
  Qed.

  (*the problem is that this does not completely define their behavior like it 
    does for the Delay case*)
  Lemma classic_converge : forall (A : Type) (t : itree E A),
      (exists a, can_converge a t) \/ must_diverge t.
  Proof.
    intros. destruct (classic (exists a, can_converge a t) ); auto.
    right. apply not_converge_to_must_diverge. intros a Hcontra.
    apply H. exists a. auto.
  Qed.


  Lemma must_diverge_imp_not_conv : forall (A : Type) (t : itree E A) (a : A), 
      must_diverge t -> ~ can_converge a t.
  Proof.
    intros. intro Hcontra. induction Hcontra.
    - rewrite H0 in H. pinversion H.
    - apply IHHcontra. rewrite H0 in H. pinversion H.
      apply inj_pair2 in H3. apply inj_pair2 in H4. subst. apply H2.
  Qed.

  Definition ITDInput (A : Type) := {p : itree E A -> Prop | resp_eutt _ _ p}.

  Definition ITreeSpec (A : Type) := {w : ITDInput A -> Prop | 
                forall (p p' : ITDInput A), (forall t, t ∈ p -> t ∈ p') -> w p -> w p' }.

  Program Definition ret_itree (A : Type) (a : A) : ITreeSpec A := fun p => p (Ret a).

  
  Definition eutt_div {A B : Type} (ta : itree E A) (tb : itree E B) := 
    eutt (fun a b => False) ta tb.

  Lemma eutt_div_spin : forall (A B : Type), @eutt_div A B spin spin.
  Proof.
    intros. einit. ecofix CIH.
    setoid_rewrite unfold_spin. etau.
  Qed.


  Lemma bind_tau : forall (A B : Type) (t : itree E A) (f : A -> itree E B),
      ITree.bind (Tau t) f ≅ Tau (ITree.bind t f).
  Proof.
    intros. pfold. red. cbn. constructor. left. 
    assert ( (ITree.bind t f) ≅  (ITree.bind t f)); try reflexivity; auto.
  Qed.

  Lemma bind_vis : forall (A B C : Type) (e : E C) (k : C -> itree E A) (f : A -> itree E B),
      ITree.bind (Vis e k) f ≅ Vis e (fun a => ITree.bind (k a) f). 
  Proof.
    intros. cbn. pfold. red. cbn. constructor. intros. unfold id. left.
    assert (ITree.bind (k v) (fun x => f x) ≅ ITree.bind (k v) (fun x => f x)); try reflexivity. 
    auto.
  Qed.
 
  Lemma div_bind_nop : forall (A B : Type) (t : itree E A) (f : A -> itree E B),
      must_diverge t -> eutt_div t (t >>= f).
  Proof.
    intros. einit. generalize dependent t. ecofix CIH. intros t Hdivt. pinversion Hdivt.
    - specialize (itree_eta t) as Ht. rewrite <- H in Ht.
      cbn. rewrite Ht.
      assert (ITree.bind (Tau t0) f ≅ Tau (ITree.bind t0 f)); try apply bind_tau.
      setoid_rewrite H1. etau.
      apply euttG_base. right. apply CIH. auto.
    - specialize (itree_eta t) as Ht. rewrite <- H in Ht.
      cbn. rewrite Ht. rewrite bind_vis. evis. cbn in CIH0. intros.
      apply euttG_base. left. apply CIH0. apply H0.
  Qed. 

  Lemma eutt_subrel : forall (A B : Type) (R1 R2 : A -> B -> Prop)
                             (ta : itree E A) (tb : itree E B),
      (forall a b, R1 a b -> R2 a b) -> eutt R1 ta tb -> eutt R2 ta tb.
  Proof.
    intros.
    eapply eqit_mon; eauto.
  Qed.

  Lemma eutt_flip : forall (A B : Type) (R : A -> B -> Prop)
      (ta : itree E A) (tb : itree E B),
    eutt R ta tb -> eutt (flip R) tb ta.
  Proof.
    intros. apply eqit_flip. 
    eapply eutt_subrel with (R1 := R); eauto.
  Qed.
    
  Lemma eutt_div_subrel : forall (A B : Type) (R : A -> B -> Prop) 
                       (ta : itree E A) (tb : itree E B), 
      eutt_div ta tb -> eutt R ta tb.
  Proof.
    intros.
    eapply eutt_subrel with (R1 := fun a b => False); tauto.
  Qed.

 
  Instance proper_itree_spec {R} {p : ITDInput R}: Proper (eutt eq  ==> iff) (proj1_sig p).
  Proof.
    intros ? ? ?. destruct p as [p Hp]. simpl. split; intros; eapply Hp; eauto.
    symmetry. auto.
  Qed.


   Lemma eutt_imp_div : forall (A B : Type) (R : A -> B -> Prop) 
                               (ta : itree E A) (tb : itree E B),
      must_diverge ta -> eutt R ta tb -> eutt_div ta tb.
   Proof.
     (* oddly had trouble doing this with euttG, maybe I should reread the gpaco paper*)
     intros A B R. pcofix CIH. pstep. intros ta tb Hdiv Heutt.
     punfold Heutt. unfold_eqit. dependent induction Heutt; pclearbot.
     - exfalso. clear CIH. specialize (itree_eta ta) as Hta.
       rewrite <- x0 in Hta. rewrite Hta in Hdiv. pinversion Hdiv.
     - rewrite <- x0. rewrite <- x. constructor. right.
       assert (m1 ≈ ta).
       { specialize (itree_eta ta) as Hta. rewrite <- x0 in Hta.
         rewrite Hta. rewrite tau_eutt. reflexivity. }
       assert (m2 ≈ tb).
       { specialize (itree_eta tb) as Htb. rewrite <- x in Htb.
         rewrite Htb. rewrite tau_eutt. reflexivity. }
       apply CIH; auto.
       rewrite H. auto.
     - rewrite <- x0. rewrite <- x. constructor.
       intros. right. apply CIH; auto.
       specialize (itree_eta ta) as Hta. rewrite <- x0 in Hta.
       rewrite Hta in Hdiv. pinversion Hdiv.
       apply inj_pair2 in H2. subst. apply H0.
     - rewrite <- x. constructor; auto. eapply IHHeutt; eauto.
        assert (t1 ≈ ta).
        { specialize (itree_eta ta) as Hta. rewrite <- x in Hta.
          rewrite Hta. rewrite tau_eutt. reflexivity. }
        rewrite H. auto.
     - rewrite <- x. constructor; auto.
   Qed.
     
   Lemma eutt_div_imp_div : forall (A B : Type) (t1 : itree E A) (t2 : itree E B),
       eutt_div t1 t2 -> must_diverge t1.
   Proof.
     intros A B. pcofix CIH. intros. pfold. red.
     punfold H0.
     unfold_eqit.
     dependent induction H0; try contradiction; pclearbot.
     - rewrite <- x0. constructor. right. eapply CIH; eauto.
     - rewrite <- x0. constructor. intros. right. eapply CIH; eauto. eapply REL.
     - rewrite <- x. constructor. right. eapply CIH with (t2 := t2); eauto. 
       pfold. auto.
     -  eapply IHeqitF; eauto.
   Qed.

   Lemma eutt_div_sym : forall (A B : Type) (t1 : itree E A) (t2 : itree E B),
       eutt_div t1 t2 -> eutt_div t2 t1.
   Proof.
     intros A B. pcofix CIH. intros. pfold. red.
     punfold H0. unfold_eqit.
     dependent induction H0; try contradiction; pclearbot.
     - rewrite <- x0. rewrite <- x. constructor. right. auto.
     - rewrite <- x0. rewrite <- x. constructor. intros. unfold id.
       right. apply CIH. apply REL.
     - rewrite <- x. constructor; auto.
     - rewrite <- x. constructor; auto.
   Qed.
     
   Lemma eutt_div_trans : forall (A B C : Type) (t1 : itree E A) 
                                (t2 : itree E B) (t3 : itree E C),
       eutt_div t1 t2 -> eutt_div t2 t3 -> eutt_div t1 t3.
   Proof.
     intros. unfold eutt_div in *.
     apply eutt_subrel with (R1 := @rcompose A B C (fun a b => False) (fun b c => False) ).
     - intros. inversion H1; contradiction.
     - eapply eqit_trans; eauto.
   Qed.


   Instance proper_eutt_div {A B : Type} {R R'} : Proper ( (@eutt E A A R) ==> (@eutt E B B R') ==> iff) (eutt_div).
   Proof.
    intros t1 t2 Ht12 t3 t4 Ht34. split; intros.
    - apply eutt_div_imp_div in H as Ht1. apply eutt_div_sym in H. 
      apply eutt_div_imp_div in H as Ht3.
      apply eutt_div_trans with (t2 := t3).
      + apply eutt_div_trans with (t2 := t1).
        * apply eutt_div_sym. eapply eutt_imp_div; eauto.
        * apply eutt_div_sym. auto.
      + eapply eutt_imp_div; eauto.
    - apply eutt_div_imp_div in H as Ht2. 
      apply eutt_div_sym in H. apply eutt_div_imp_div in H as Ht3.
      assert (eutt_div t1 t2).
      { 
        apply eutt_div_sym. apply eutt_flip in Ht12. 
        eapply eutt_imp_div; eauto.
      }
      assert (eutt_div t3 t4).
      {
        apply eutt_div_sym. apply eutt_flip in Ht34.
        eapply eutt_imp_div; eauto.
      }
      apply eutt_div_sym in H.
      apply eutt_div_trans with (t2 := t4).
      + apply eutt_div_trans with (t2 := t2); auto.
      + apply eutt_div_sym. auto.
   Qed.

  Definition div_cast {A B : Type} (t : itree E A) : itree E B :=
    t >>= fun _ => spin.

  Lemma div_cast_nop : forall (A : Type) (t : itree E A),
      must_diverge t -> t ≈ div_cast t.
  Proof.
    intros. apply eutt_div_subrel. apply div_bind_nop. auto.
  Qed.


  Set Default Timeout 15.

  Ltac infer_div H := 
    match type of H with eutt_div ?t1 ?t2 => 
                         apply eutt_div_sym in H as ?H1; 
                         apply eutt_div_imp_div in H1;
                         apply eutt_div_imp_div in H as ?H end.

  Instance proper_eutt_div_cast {A B : Type} : Proper (@eutt_div A A ==> @eutt_div B B) div_cast.
  Proof.
    intros t1 t2 ?. infer_div H.
    eapply eutt_div_trans with (t2 := t2); try apply div_bind_nop; auto.
    eapply eutt_div_trans with (t2 := t1); auto.
    apply eutt_div_sym. apply div_bind_nop. auto.
  Qed.


  Lemma div_cast_cast : forall (A B : Type) (t1 t2 : itree E A) 
                               (R : A -> A -> Prop) (R' : B -> B -> Prop), 
      must_diverge t1 -> eutt R t1 t2 -> eutt R' (div_cast t1) (div_cast t2).
  Proof.
    intros.  apply eutt_div_subrel.
    apply eutt_imp_div in H0; auto.
    infer_div H0.
    apply eutt_div_trans with (t2 := t2); try apply div_bind_nop; auto.
    apply eutt_div_trans with (t2 := t1); auto.
    apply eutt_div_sym. apply div_bind_nop. auto.
 Qed.


  Program Definition bind_ex (A B: Type) (w: ITreeSpec A) (g : A -> ITreeSpec B) : ITreeSpec B :=
    fun p => w (fun t => (exists a, can_converge a t /\ g a p) \/ (must_diverge t /\  p (div_cast t)) ).
  Next Obligation.
  Proof.
    repeat red. split; intros; basic_solve.
    - left. exists a. rewrite H in H0. auto.
    - right. rewrite <- H at 1. split; auto.
      destruct p as [p Hp]; simpl in *.
      specialize (eutt_imp_div _ _ eq t1 t2 H0 H).
      intros. 
      specialize (div_cast_nop A t1 H0) as Ht1.
      rewrite H in H0. specialize (div_cast_nop A t2 H0) as Ht2.
      eapply Hp; eauto. 
      symmetry in H.
      eapply div_cast_cast; eauto.
    - left. exists a. split; auto. rewrite H. auto.
    - right. rewrite H at 1. split; auto.
      destruct p as [p Hp]; simpl in *.
      eapply Hp; eauto.
      eapply div_cast_cast; eauto.
      rewrite H. auto.
  Qed.
  Next Obligation.
  Proof.
    destruct w as [w Hw]. simpl in *.  eapply Hw; try apply H0.
    intros. simpl in *. 
    destruct p as [p Hp]. destruct p' as [p' Hp']. simpl in *.
    basic_solve.
    - left. exists a. split; auto. destruct (g a) as [ga Hga]. simpl in *. 
      eapply Hga; try apply H2.
      simpl. auto.
    - right. split; auto.
  Qed.

  Instance ItreeSpecEq : EqM ITreeSpec :=
    fun _ w1 w2 => forall p, p ∈ w1 <-> p ∈ w2.

  Instance ItreeSpecEquiv {A : Type} : Equivalence (ItreeSpecEq A).
  Proof.
    constructor; red; intros; red; try tauto.
    - red in H. intros. rewrite H. reflexivity.
    - intros. red in H. red in H0. rewrite H. rewrite H0.
      reflexivity.
  Qed.

  Instance ItreeSpecMonad : Monad ITreeSpec :=
    {
      ret := ret_itree;
      bind := bind_ex;
    }.


  Lemma invert_ret :  forall (A : Type) (a a' : A), can_converge a (Ret a') -> a = a'.
  Proof.
    intros. inversion H; subst; basic_solve; auto.
    pinversion H0.
  Qed.
    
  Program Instance ItreeSpecMonadLaws : MonadLaws ITreeSpec.
  Next Obligation.
    (*bind_ret*)
    repeat red. cbn. intros. split; intros; basic_solve.
    - apply invert_ret in H. subst. auto.
    - pinversion H.
    - left. exists x. split; auto. constructor. reflexivity.
  Qed.
  Next Obligation.
    (*ret_bind*)
    repeat red. cbn. intros. split; intros; basic_solve.
    - destruct x as [w Hw]. simpl in *. eapply Hw; try apply H.
      intros. simpl in *. basic_solve.
      +

        (*PROBLEM: if p just respects eutt, then p (ret a0) might mean
          p expects no events
          consider p := fun t => exists a, t ~ ret a
          but the evidence can_converge a0 t does not force t to be a Ret
          the issue seems to be that 
         *)

        (*
          The obvious solution is to further restrict predicates from resp eutt
          to respecting possible convergence. This is a bad solution,
          we want to be able to do something like have a predicate that 
          accepts all trees that print 5 and then return 6. This would be 
          an illegal predicate
         *)
        inversion H0; subst.
        * rewrite H2. auto.
        * rewrite H2. admit.
      + apply div_cast_nop in H0. 
        rewrite H0. auto.
    - destruct x as [w Hw]. simpl in *. eapply Hw; try apply H.
      intros. simpl. destruct (classic_converge _ t).
      + left. basic_solve. exists a0. split; auto.
        (*basically same problem as before, this time we know p t, but
          that might be reliant on some visible event behavior*)
        admit.
      + right. split; auto. apply div_cast_nop in H1.
        rewrite <- H1. auto.
  Admitted.
  Next Obligation.
    (*bind_bind*)
    repeat red. destruct x as [w Hw]. cbn. intros. split; intros; basic_solve.
    - eapply Hw; try apply H. simpl in *. intros. basic_solve.
      + left. exists a0. auto.
      + exfalso. clear H H2 Hw w. 
        eapply must_diverge_imp_not_conv; try apply H1.
        eapply eutt_div_imp_div. apply eutt_div_sym.
        apply div_bind_nop. auto.
      + right. split; auto.
        destruct p as [p Hp]. simpl in *. clear H.
        eapply Hp; try apply H2.
        apply eutt_div_subrel.
        rewrite bind_bind.
        apply eutt_div_trans with (t2 := t).
        * apply eutt_div_sym. apply div_bind_nop. auto.
        * apply div_bind_nop. auto.
    - eapply Hw; try apply H. simpl in *. intros. basic_solve.
      + left. exists a0. auto.
      + right. split; auto. right. split.
        * apply eutt_div_imp_div with (t2 := t); auto.
          apply eutt_div_sym. apply div_bind_nop. auto.
        * destruct p as [p Hp]. simpl in *. clear H.
          eapply Hp; try apply H1. rewrite bind_bind.
          apply eutt_div_subrel.
          apply eutt_div_trans with (t2 := t); try apply div_bind_nop; auto.
          apply eutt_div_sym. apply div_bind_nop. auto.
  Qed.


  Inductive Ev : Type := 
    ev (A : Type ) (e : E A) (a : A).



  (*  

      E := | Out ... | In ...
      WHist A := ((list E)  * A -> Prop) -> list E -> Prop



   *)

  Variant streamF {A : Type} {F : Type} : Type :=
    | NilF 
    | ConsF (h : A) (t : F).

  CoInductive stream (A : Type) : Type := go {_observe : @streamF A (stream A) } .

  Definition Nil {A} : stream A:=
    {| _observe := NilF |}.

  Definition Cons {A} (h : A) (t : stream A) := {| _observe := ConsF h t |}.

  (*need a way to relate trees across event types if they never use it*)

  Definition rel_eventless {E1 E2 R} (t1 : itree E1 R) (t2 : itree E2 R) : Prop := False.

  Inductive eqitEF {E1 E2 : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
            (vclo : (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop )
            (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
    | EqERet : forall r1 r2, RR r1 r2 -> eqitEF RR vclo sim (RetF r1) (RetF r2)
    | EqETau : forall (t1 : itree E1 R1) (t2 : itree E2 R2),
        sim t1 t2 -> 
        eqitEF RR vclo sim (TauF t1) (TauF t2)
    | EqETauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
        eqitEF RR vclo sim (observe t1) ot2 ->
        eqitEF RR vclo sim (TauF t1) ot2 
    | EqETauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
        eqitEF RR vclo sim ot1 (observe t2) ->
        eqitEF RR vclo sim ot1 (TauF t2).

  Hint Constructors eqitEF.

  Definition eqitE_ (E1 E2 : Type -> Type) (R1 R2 : Type) 
             (RR : R1 -> R2 -> Prop)
             (vclo :  (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop)
             (sim : itree E1 R1 -> itree E2 R2 -> Prop)
             (t1 : itree E1 R1) (t2 : itree E2 R2)
    := eqitEF RR vclo sim (observe t1) (observe t2).

  Definition eqitE {E1 E2} {R1 R2} RR := paco2 (eqitE_ E1 E2 R1 R2 RR id) bot2.

  Lemma eqitE_monot {E1 E2 R1 R2 RR} : monotone2  (@eqitE_ E1 E2 R1 R2 RR id).
  Proof.
    repeat red. intros. rename x0 into t1. rename x1 into t2.
    induction IN; eauto.
  Qed.

  Hint Resolve eqitE_monot : paco.

  Definition equivE {E1 E2} {R} : itree E1 R -> itree E2 R -> Prop := eqitE eq. 

  Variant eventlessF {E : Type -> Type} {R : Type} (F : itree E R -> Prop) : itree' E R -> Prop :=
    | eventlessRet (r : R) : eventlessF F (RetF r)
    | eventlessTau (t : itree E R) : F t -> eventlessF F (TauF t).

  Hint Constructors eventlessF.

  Definition eventless_ {E : Type -> Type} {R : Type} (F : itree E R -> Prop) 
    : itree E R -> Prop := fun t => eventlessF F (observe t).
            
  Hint Unfold eventless_.

  Definition eventless {E : Type -> Type} {R : Type} : itree E R -> Prop :=
    paco1 (eventless_) bot1.

  Lemma eventless_monot {E1 R} : monotone1 (@eventless_ E1 R).
  Proof.
    red. intros. red in IN. red. inversion IN; auto.
  Qed.

  Hint Resolve eventless_monot : paco.


  Instance proper_eventless_imp {E R} : Proper (eutt eq ==> impl) (@eventless E R) .
  Proof.
    repeat red. pcofix CIH.
    intros t1 t2 Heutt Hev.
    pfold. punfold Heutt.  red.
    unfold_eqit. assert (Hev' : eventless t1); auto. punfold Hev.
    dependent induction Heutt; subst; auto.
    - rewrite <- x. auto.
    - rewrite <- x. constructor. right. eapply CIH; eauto.
      specialize (itree_eta t1) as Ht1. rewrite <- x0 in Ht1.
      rewrite Ht1. rewrite tau_eutt. pclearbot. auto.
    - red in Hev. inversion Hev; subst.
      + rewrite <- H0 in x0. discriminate.
      + rewrite <- H in x0. discriminate.
    - red in Hev. rewrite <- x in Hev. inversion Hev; subst.
      pclearbot. eapply IHHeutt; try apply H0; eauto. red.
      punfold H0.
    - rewrite <- x. constructor. right. eapply CIH; eauto.
  Qed.

  Instance proper_eventless {E R} : Proper (eutt eq ==> iff) (@eventless E R).
  Proof.
    intros t1 t2 Heutt. split; intros Hev.
    - rewrite <- Heutt. auto.
    - symmetry in Heutt. rewrite <- Heutt. auto.
  Qed.


  
  Lemma eutt_eventless : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop) 
                 (t1 : itree E R1) (t2 : itree E R2), 
      eventless t1 -> eutt RR t1 t2 -> eqitE RR t1 t2.
  Proof.
    intros E1 R1 R2 RR. pcofix CIH. intros.
    punfold H1. unfold_eqit. pfold. red. dependent induction H1; auto.
    - rewrite <- x0. rewrite <- x. constructor. auto.
    - rewrite <- x0. rewrite <- x.
      constructor. right. 
      specialize (itree_eta t1) as Ht1. specialize (itree_eta t2) as Ht2.
      rewrite <- x0 in Ht1. rewrite <- x in Ht2.
      assert (t1 ≈ m1). { rewrite Ht1. rewrite tau_eutt. reflexivity. }
      assert (t2 ≈ m2). { rewrite Ht2. rewrite tau_eutt. reflexivity. }
      pclearbot.
      apply CIH; auto.
      rewrite <- H. auto.
    - exfalso. pinversion H0. 
      + rewrite <- H1 in x0. discriminate.
      + rewrite <- H in x0. discriminate.
    - rewrite <- x. constructor.
      specialize (itree_eta t1) as Ht1. rewrite <- x in Ht1.
      rewrite Ht1 in H0. pinversion H0. 
      subst. eapply IHeqitF; try apply H2; eauto.
    - rewrite <- x. constructor. eapply IHeqitF; eauto.
  Qed.

  Lemma eqitE_imp_eutt : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
                                (t1 : itree E R1) (t2 : itree E R2),
      eqitE RR t1 t2 -> eutt RR t1 t2.
  Proof.
    intros E1 R1 R2 RR. pcofix CIH.
    intros t1 t2 Heq. pfold. punfold Heq.
    red. red in Heq. induction Heq; auto.
    pclearbot. constructor. right. apply CIH.
    auto.
  Qed.

  Lemma eqitE_imp_eventlessl : forall (E1 E2 : Type -> Type) (R1 R2 : Type) 
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eventless t1.
  Proof.
    intros E1 E2 R1 R2 RR. pcofix CIH.
    intros. punfold H0. red in H0.
    pfold. red. induction H0; eauto.
    pclearbot.
    constructor. right. eapply CIH; eauto.
  Qed.

  Lemma eqitE_imp_eventlessr : forall (E1 E2 : Type -> Type) (R1 R2 : Type) 
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eventless t2.
  Proof.
    intros E1 E2 R1 R2 RR. pcofix CIH.
    intros. punfold H0. red in H0.
    pfold. red. induction H0; eauto.
    pclearbot.
    constructor. right. eapply CIH; eauto.
  Qed.


  (*need to get this done at some point*)
  Lemma eqitE_inv_tauLR : forall (E1 E2 : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
            (t1 : itree E1 R1) (t2 : itree E2 R2),
            eqitE RR (Tau t1) (Tau t2) -> eqitE RR t1 t2.
  Proof.
    intros E1 E2 R1 R2 RR. 

    pcofix CIH. intros.
    punfold H0. red in H0. simpl in H0.
    pfold. red. remember (TauF t1) as tt1.
    remember (TauF t2) as tt2. genobs t1 ot1.
    genobs t2 ot2. induction H0; try discriminate.
    - pclearbot. injection Heqtt1 as Heqtt1. injection Heqtt2 as Heqtt2. subst.
      punfold H. red in H. auto. eapply eqitE_monot; eauto.
      intros. pclearbot. left. eapply paco2_mon; try apply PR. intros. contradiction.
   Admitted.

  Lemma eqitE_trans : forall (E1 E2 E3 : Type -> Type) (R : Type) 
                             (t1 : itree E1 R) (t2 : itree E2 R) (t3 : itree E3 R),
      equivE t1 t2 -> equivE t2 t3 -> equivE t1 t3.
  Proof.
    intros E1 E2 E3 R.
    pcofix CIH. intros t1 t2 t3 INL INR.
    pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t3 ot3.
    hinduction INL before CIH; intros; subst; clear t1 t2; eauto.
    - remember (RetF r2) as ot.
      hinduction INR before CIH; intros; inv Heqot; eauto with paco.
    - assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
      { destruct ot3; eauto; right; red; intros; inv H; discriminate. }
      destruct DEC as [EQ | EQ].
      + destruct EQ as [m3 ?]; subst.
        econstructor. right. pclearbot. eapply CIH; eauto with paco.
        eapply eqitE_inv_tauLR.  (* eauto.  pfold. constructor.
        left.



      + inv INR; try (exfalso; eapply EQ; eauto; fail).
        econstructor; eauto.
        pclearbot. punfold REL. red in REL.
        hinduction REL0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
        * remember (RetF r1) as ot.
          hinduction REL0 before CIH; intros; inv Heqot; eauto with paco.
        * remember (VisF e k1) as ot.
          hinduction REL0 before CIH; intros; dependent destruction Heqot; eauto with paco.
          econstructor. intros. right.
          destruct (REL v), (REL0 v); try contradiction. eauto.
        * eapply IHREL0; eauto. pstep_reverse.
          destruct b1; inv CHECK0.
          apply eqit_inv_tauR. eauto.
    - remember (VisF e k2) as ot.
      hinduction INR before CIH; intros; dependent destruction Heqot; eauto.
      econstructor. intros.
      destruct (REL v), (REL0 v); try contradiction; eauto.
    - remember (TauF t0) as ot.
      hinduction INR before CIH; intros; dependent destruction Heqot; eauto.
      eapply IHINL; eauto. pclearbot. punfold REL.
  Qed. *) Admitted.
  

  Instance proper_eqitE_imp {E1 E2} {R1 R2} {RR} :Proper (  eutt eq ==> (eutt eq) ==> impl) (@eqitE E1 E2 R1 R2 RR).
  Proof.
    repeat red.
    intros t1 t2 Ht12 t3 t4 Ht34. intros.
    apply eqitE_imp_eventlessl in H as Ht1.
    apply eqitE_imp_eventlessr in H as Ht3.
    assert (Ht2 : eventless t2). 
    { rewrite <- Ht12. auto. }
    assert (Ht4 : eventless t4).
    { rewrite <- Ht34. auto. }

    pcofix CIH.

  Admitted.
  (*could also use an eventless predicate*)

  (*gets the idea across, obviously I want to pacoize this*)
  CoInductive itree_includes {R : Type} : itree E R -> stream Ev -> Delay R -> Prop := 
    | includes_base (t : itree E R) (d : Delay R) : equivE t d -> itree_includes t Nil d
    | cont_vis {A} (e : E A) (a : A) (k : A -> itree E R) (t : itree E R) (s : stream Ev ) (d : Delay R) :
        Vis e k ≈ t -> 
        itree_includes (k a) s d -> itree_includes t (Cons (ev A e a) s ) (Tau d).

  Variant itree_includesF {R : Type} (F : itree E R -> stream Ev -> Delay R -> Prop) : 
    itree E R -> stream Ev -> Delay R -> Prop :=
    | includes_baseF (t : itree E R) (d : Delay R) : equivE t d -> itree_includesF F t Nil d
    | cont_visF {A} (e : E A) (a : A) (k : A -> itree E R) (t : itree E R) (s : stream Ev) (d : Delay R) :
        Vis e k ≈ t ->
        F (k a) s d -> itree_includesF F t (Cons (ev A e a) s) (Tau d).



  (*then things I can prove about binding trees with this*)
  (*maybe think before doing too much work on this*)
(*write a function from itree Void -> itree E*)

(*
  Definition Event_list := list Ev.

  
  

  Definition PredDeriv ()
*)
End ITreeDijkstra.
