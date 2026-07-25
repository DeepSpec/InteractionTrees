From Coinduction Require Import all. 

From Stdlib Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Props.Infinite
     Props.EuttNoRet.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.DelaySpecMonad.

Import Monads.
Import MonadNotation.

#[local] Open Scope monad_scope.
#[local] Open Scope delayspec_scope.


Section ITreeDijkstra.

  Context (E : Type -> Type).

  Definition ITDInput (A : Type) := {p : itree E A -> Prop | resp_eutt p}.

  Definition ITreeSpec (A : Type) := {w : ITDInput A -> Prop |
                forall (p p' : ITDInput A), (forall t, t ∈ p -> t ∈ p') -> w p -> w p' }.

  Program Definition ret_itree (A : Type) (a : A) : ITreeSpec A := fun p => p (Ret a).

  Instance proper_itree_spec {R} {p : ITDInput R}: Proper (eutt eq ==> iff) (proj1_sig p).
  Proof.
    intros ? ? ?. destruct p as [p Hp]. simpl. split; intros; eapply Hp; eauto.
    now rewrite <- H.
  Qed.

  Program Definition bind_ex (A B: Type) (w: ITreeSpec A) (g : A -> ITreeSpec B) : ITreeSpec B :=
    fun p  =>
      w (fun t => (exists a, may_converge a t /\ g a p) \/ (all_infinite t /\  p (noret_cast t)) ).
  Next Obligation.
  Proof.
    repeat red. split; intros; basic_solve.
    - left. exists a. rewrite H in H0. auto.
    - right. rewrite <- H at 1. split; auto.
      destruct p as [p Hp]; simpl in *.
      specialize (all_infinite_euttNoRet H0 H).
      intros.
      specialize (noret_cast_nop H0) as Ht1.
      rewrite H in H0. specialize (noret_cast_nop H0) as Ht2.
      eapply Hp. 
      clear Ht2. 
      symmetry in H. 
      eapply noret_cast_cast. all: eauto.
    - left. exists a. split; auto. rewrite H. auto.
    - right. rewrite H at 1. split; auto.
      destruct p as [p Hp]; simpl in *.
      eapply Hp. 
      symmetry in H. 
      symmetry. 
      eapply noret_cast_cast; eauto.
      auto. 
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

  Instance ItreeSpecEq : Eq1 ITreeSpec :=
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

  (*
  Program Instance ItreeSpecMonadLaws : MonadLaws ITreeSpec.
  Next Obligation.
    (*bind_ret*)
    repeat red. cbn. intros. split; intros; basic_solve.
    - apply invert_ret in H. subst. auto.
    - sinv H.
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
          but the evidence may_converge a0 t does not force t to be a Ret
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
      + apply noret_cast_nop in H0.
        rewrite H0. auto.
    - destruct x as [w Hw]. simpl in *. eapply Hw; try apply H.
      intros. simpl. destruct (classic_converge _ t).
      + left. basic_solve. exists a0. split; auto.
        (*basically same problem as before, this time we know p t, but
          that might be reliant on some visible event behavior*)
        admit.
      + right. split; auto. apply noret_cast_nop in H1.
        rewrite <- H1. auto.
  Admitted.
  Next Obligation.
    (*bind_bind*)
    repeat red. destruct x as [w Hw]. cbn. intros. split; intros; basic_solve.
    - eapply Hw; try apply H. simpl in *. intros. basic_solve.
      + left. exists a0. auto.
      + exfalso. clear H H2 Hw w.
        eapply all_infinite_imp_not_conv; try apply H1.
        eapply euttNoRet_all_infinite. apply euttNoRet_sym.
        apply noret_bind_nop. auto.
      + right. split; auto.
        destruct p as [p Hp]. simpl in *. clear H.
        eapply Hp; try apply H2.
        apply euttNoRet_subrel.
        rewrite bind_bind.
        apply euttNoRet_trans with (t2 := t).
        * apply euttNoRet_sym. apply noret_bind_nop. auto.
        * apply noret_bind_nop. auto.
    - eapply Hw; try apply H. simpl in *. intros. basic_solve.
      + left. exists a0. auto.
      + right. split; auto. right. split.
        * apply euttNoRet_all_infinite with (t2 := t); auto.
          apply euttNoRet_sym. apply noret_bind_nop. auto.
        * destruct p as [p Hp]. simpl in *. clear H.
          eapply Hp; try apply H1. rewrite bind_bind.
          apply euttNoRet_subrel.
          apply euttNoRet_trans with (t2 := t); try apply noret_bind_nop; auto.
          apply euttNoRet_sym. apply noret_bind_nop. auto.
  Qed.
  *)

  Inductive Ev : Type :=
    ev (A : Type ) (e : E A) (a : A).

  Variant streamF {A : Type} {F : Type} : Type :=
    | NilF
    | ConsF (h : A) (t : F).

  CoInductive stream (A : Type) : Type := go {_observe : @streamF A (stream A) } .

  Notation stream' A := (@streamF A (stream A)).

  Definition Nil {A} : stream A:=
    {| _observe := NilF |}.

  Definition Cons {A} (h : A) (t : stream A) := {| _observe := ConsF h t |}.

  Definition observe_stream {A} : stream A -> stream' A := @_observe A.

  Variant is_infF {A : Type}  (F : stream A -> Prop) : stream' A -> Prop :=
    is_inf_cons (h : A) (t : stream A) : F t -> is_infF F (ConsF h t).

  Hint Constructors is_infF : itree.

  Definition is_inf_ {A : Type} (F : stream A -> Prop) : stream A -> Prop :=
    fun s => is_infF F (observe_stream s).

  Lemma is_inf_mono {A} : Proper (leq ==> leq) (@is_inf_ A). 
  Proof. monauto. Qed. 

  Definition is_inf_mon A : mon (stream A -> Prop) := 
  {| body := @is_inf_ A; Hbody := is_inf_mono |}. 

  Definition is_inf {A : Type} := gfp (@is_inf_mon A).

  CoFixpoint app' {A : Type} (osl: stream' A) (sr : stream A) : stream A :=
    match osl with
    | NilF => sr
    | ConsF h t => Cons h (app' (observe_stream t) sr)
    end.

  Definition app {A : Type} (sl : stream A) : stream A -> stream A :=
    app' (observe_stream sl).

  Variant bisimF {A : Type} (F : stream A -> stream A -> Prop) : stream' A -> stream' A -> Prop :=
    | bisimNil : bisimF F NilF NilF
    | bisimConsF (h : A) (s1 s2 : stream A) : F s1 s2 -> bisimF F (ConsF h s1) (ConsF h s2).

  Hint Constructors bisimF : itree.

  Definition bisim_ {A : Type} (F : stream A -> stream A -> Prop) : stream A -> stream A -> Prop :=
    fun s1 s2 => bisimF F (observe_stream s1) (observe_stream s2).

  Lemma bisim_mono {A} : Proper (leq ==> leq) (@bisim_ A). 
  Proof. monauto. Qed. 
  
  Definition bisim_mon {A} : mon (stream A -> stream A -> Prop) := 
  {| body := @bisim_ A ; Hbody := bisim_mono |}. 

  Definition bisim {A : Type} := gfp (@bisim_mon A).

  Instance bisim_equiv {A} : Equivalence (@bisim A).
  Proof.
    constructor; red.
    - coinduction c CIH. intros. cbn; red. destruct (observe_stream x); auto with itree.
    - coinduction c CIH. intros.
      cbn; red.
      red in H; sinv H; auto with itree.
    - unfold bisim at 3. coinduction c CIH. intros. cbn; red.
      red in H; sinv H; red in H0; sinv H0; auto with itree.
      + rewrite <- H in H3. discriminate.
      + rewrite <- H2 in H4. discriminate.
      + rewrite <- H2 in H. injection H; intros; subst.
        constructor. eauto.
   Qed.

(* step notes: 
step on elem should not reduce 
step on mon can reduce 
step on gfp can reduce. 
*)

  Instance proper_bisim_app {A} : Proper (@bisim A ==> bisim ==> bisim) app.
  Proof.
     coinduction c CIH. intros s1 s2 H12 s3 s4 H34.
     cbn; red. unfold app. sinv H12.
    - simpl. destruct s3. destruct s4. sinv H34; simpl in *; subst; auto with itree.
      constructor. now do 2 step. 
    - cbn. constructor. apply CIH; auto.
  Qed.



#[local] Tactic Notation "icbn" := repeat red; cbn.  

  Instance proper_bisim_inf_imp {A} : Proper (@bisim A ==> Basics.impl) is_inf.
  Proof.
    coinduction c CIH.
    intros s1 s2 H12 H. icbn. step in H. 
    step in H12. inv H12. 
    - rewrite <- H1 in H. inv H.
    - inversion H; subst. 
      constructor. eapply CIH; eauto.
      rewrite <- H3 in H0. inv H0.
  Qed.

  Instance proper_bisim_inf {A} : Proper (@bisim A ==> iff) (is_inf).
  Proof.
    split; try apply proper_bisim_inf_imp; auto.
    apply bisim_equiv. auto.
  Qed.

  Lemma app_inf : forall (A : Type) (s1 s2 : stream A), is_inf s1 -> bisim (app s1 s2) s1.
  Proof.
    intros A. coinduction c CIH. intros s1 s2 Hinf. icbn. unfold app.
    sinv Hinf.
    cbn. constructor. apply CIH; auto.
  Qed.

  Variant forall_streamF {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream' A -> Prop :=
    | forall_nil : forall_streamF P F NilF
    | forall_cons (h : A) (t : stream A) : P h -> F t -> forall_streamF P F (ConsF h t).

  Hint Constructors forall_streamF : itree.

  Definition forall_stream_ {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream A -> Prop :=
    fun s => forall_streamF P F (observe_stream s).

  Lemma forall_stream_mono (A : Type) (P : A -> Prop) : Proper (leq ==> leq) (forall_stream_ P).
  Proof. monauto. Qed.

  Definition forall_stream_mon A P := Build_mon (forall_stream_mono A P). 

  Definition forall_stream {A : Type} (P : A -> Prop) := gfp (forall_stream_mon A P).

  Inductive inf_manyF {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream' A -> Prop :=
    | cons_search (h : A) (t : stream A) : inf_manyF P F (observe_stream t) -> inf_manyF P F (ConsF h t)
    | cons_found (h : A) (t : stream A) : P h -> F t -> inf_manyF P F (ConsF h t)
  .

  Hint Constructors inf_manyF : itree.

  Definition inf_many_ {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream A -> Prop :=
    fun s => inf_manyF P F (observe_stream s).

  Lemma inf_many_mono (A : Type) (P : A -> Prop) : Proper (leq ==> leq) (inf_many_ P).
  Proof. monauto. Qed.

  Definition inf_many_mon A P := Build_mon (inf_many_mono A P). 

  Definition inf_many {A : Type} (P : A -> Prop) := gfp (inf_many_mon A P).

  Lemma inf_many_inf : forall (A : Type) (P : A -> Prop) (s : stream A),
      inf_many P s -> is_inf s.
  Proof.
    intros A P. coinduction c CIH. intros s Him.
    step in Him. icbn. 
    induction Him; auto with itree.
    constructor. apply CIH. now step. 
  Qed.

  Lemma inf_and_forall : forall (A : Type) (P : A -> Prop) (s : stream A),
      is_inf s -> forall_stream P s -> inf_many P s.
  Proof.
    intros A P. coinduction c CIH. intros s Hinf Hforall.
    icbn. step in Hinf. step in Hforall.
    inv Hinf.
    inv Hforall.
    - rewrite <- H in H2. discriminate.
    - rewrite <- H in H1. inv H1.
      apply cons_found; auto.
  Qed.

  (*bisim is proper under app*)

  (*need a way to relate trees across event types if they never use it*)

  Definition rel_eventless {E1 E2 R} (t1 : itree E1 R) (t2 : itree E2 R) : Prop := False.
  Inductive eqitEF {E1 E2 : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
            (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
    | EqERet : forall r1 r2, RR r1 r2 -> eqitEF RR sim (RetF r1) (RetF r2)
    | EqETau : forall (t1 : itree E1 R1) (t2 : itree E2 R2),
        sim t1 t2 ->
        eqitEF RR sim (TauF t1) (TauF t2)
    | EqETauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
        eqitEF RR sim (observe t1) ot2 ->
        eqitEF RR sim (TauF t1) ot2
    | EqETauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
        eqitEF RR sim ot1 (observe t2) ->
        eqitEF RR sim ot1 (TauF t2).

  Hint Constructors eqitEF : itree.

  Definition eqitE_ (E1 E2 : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
             (sim : itree E1 R1 -> itree E2 R2 -> Prop)
             (t1 : itree E1 R1) (t2 : itree E2 R2)
    := eqitEF RR sim (observe t1) (observe t2).

  Lemma eqitE_mono {E1 E2 R1 R2 RR} : Proper (leq ==> leq)  (@eqitE_ E1 E2 R1 R2 RR).
    Proof. monauto. Qed.

  Definition eqitE_mon {E1 E2 R1 R2 RR} := Build_mon (@eqitE_mono E1 E2 R1 R2 RR).

  Definition eqitE {E1 E2} {R1 R2} RR := gfp (@eqitE_mon E1 E2 R1 R2 RR).

  Definition equivE {E1 E2} {R} : itree E1 R -> itree E2 R -> Prop := eqitE eq.

  Variant eventlessF {E : Type -> Type} {R : Type} (F : itree E R -> Prop) : itree' E R -> Prop :=
    | eventlessRet (r : R) : eventlessF F (RetF r)
    | eventlessTau (t : itree E R) : F t -> eventlessF F (TauF t).

  Hint Constructors eventlessF : itree.

  Definition eventless_ {E : Type -> Type} {R : Type} (F : itree E R -> Prop)
    : itree E R -> Prop := fun t => eventlessF F (observe t).

  Hint Unfold eventless_ : itree.
  
  Lemma eventless_mono {E1 R} : Proper (leq ==> leq) (@eventless_ E1 R).
  Proof. monauto. Qed.

  Definition eventless_mon {E1 R} := Build_mon (@eventless_mono E1 R).

  Definition eventless {E : Type -> Type} {R : Type} : itree E R -> Prop :=
    gfp (@eventless_mon E R).

  Instance proper_eventless_imp {E1 R} : Proper (eutt eq ==> Basics.impl) (@eventless E1 R) .
  Proof.
    repeat red. coinduction c CIH.
    intros t1 t2 Heutt Hev.
    step in Heutt. icbn.
    assert (Hev' := Hev). step in Hev.
    dependent induction Heutt; subst; auto with itree.
    - simpobs. auto with itree.
    - simpobs. constructor. eapply CIH; eauto.
      inv Hev. 
    - simpobs. inv Hev. 
    - simpobs. inv Hev.
      eapply IHHeutt; try apply H0; eauto.
      now step in H0. 
    - simpobs. constructor. unstep in Heutt. eapply CIH; eauto with itree.
  Qed.

  Instance proper_eventless {E1 R} : Proper (eutt eq ==> iff) (@eventless E1 R).
  Proof.
    intros t1 t2 Heutt. split; intros Hev.
    - rewrite <- Heutt. auto.
    - symmetry in Heutt. rewrite <- Heutt. auto.
  Qed.

  Lemma eutt_eventless : forall (E1 : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
                 (t1 : itree E1 R1) (t2 : itree E1 R2),
      eventless t1 -> eutt RR t1 t2 -> eqitE RR t1 t2.
  Proof.
    intros E1 R1 R2 RR. coinduction c CIH. intros.
    step in H0. icbn. dependent induction H0; auto.
    - simpobs. eret. 
    - simpobs.
      constructor.  
      specialize (itree_eta t1) as Ht1. specialize (itree_eta t2) as Ht2.
      simpobs. 
      assert (t1 ≈ m1). { rewrite Ht1. rewrite tau_eutt. reflexivity. }
      assert (t2 ≈ m2). { rewrite Ht2. rewrite tau_eutt. reflexivity. }
      apply CIH; auto.
      now rewrite <- H0. 
    - exfalso. step in H; simpobs. inv H.
    - simpobs. constructor.
      specialize (itree_eta t1) as Ht1. simpobs. 
      sinv H. 
      + simpobs; easy.  
      + eapply IHeqitF; eauto. rewrite <- tau_eutt. step. 
      rewrite x, <- H1. now constructor. 
    - simpobs. constructor. eapply IHeqitF; eauto.
  Qed.

  Lemma eventless_div : forall (R : Type) (t : itree E R),
      eventless t -> all_infinite t -> t ≈ ITree.spin.
  Proof.
    intros R. coinduction c CIH. intros.
      sinv H.
    - specialize (itree_eta t) as Ht. simpobs. 
      rewrite Ht in H0. sinv H0.
    - icbn. simpobs. 
      red in H0. step in H0; simpobs; inv H0. 
      constructor.
      apply CIH; auto. 
  Qed.

  Lemma eventless_ret : forall (R : Type) (t : itree E R) (r : R),
      eventless t -> may_converge r t -> t ≈ Ret r.
  Proof.
    intros R t r.
    intros. induction H0; auto. rewrite H0 in H.
    sinv H.
  Qed.

  Lemma eqitE_imp_eutt : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
                                (t1 : itree E R1) (t2 : itree E R2),
      eqitE RR t1 t2 -> eutt RR t1 t2.
  Proof.
    intros E1 R1 R2 RR. coinduction c CIH.
    intros t1 t2 Heq. icbn. step in Heq. 
    induction Heq; auto with itree.
  Qed.

  Lemma eqitE_imp_eventlessl : forall (E1 E2 : Type -> Type) (R1 R2 : Type)
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eventless t1.
  Proof.
    intros E1 E2 R1 R2 RR. coinduction c CIH.
    intros. step in H. 
    icbn. induction H; eauto with itree.
    constructor. apply (CIH t0 (ITreeDefinition.go ot2)). now step. 
  Qed.

  Lemma eqitE_imp_eventlessr : forall (E1 E2 : Type -> Type) (R1 R2 : Type)
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eventless t2.
  Proof.
    intros E1 E2 R1 R2 RR. coinduction c CIH.
    intros. step in H.
    icbn. induction H; eauto with itree.
    constructor. apply (CIH (ITreeDefinition.go ot1) t0). now step. 
  Qed.

  Lemma eventless_spin : forall (E1 : Type -> Type) (R : Type),
      eventless (@ITree.spin E1 R).
  Proof.
    intros E1 R. coinduction c CIH. icbn. cbn. constructor.
    auto.
  Qed.

  CoFixpoint remove_events' {E1 E2 : Type -> Type} {A : Type}
              (t : itree' E1 A) : itree E2 A :=
    match t with
    | RetF r => Ret r
    | TauF t' => Tau (remove_events' (observe t'))
    | VisF _ _ => ITree.spin end.

  Definition remove_events {E1 E2 A} (t : itree E1 A) : itree E2 A :=
    remove_events' (observe t).

  Lemma remove_events_eventless_equivE : forall (E1 E2 : Type -> Type) (A : Type)
                                         (t : itree E1 A),
      eventless t -> @equivE E1 E2 A t (remove_events t).
  Proof.
    intros E1 E2 A. coinduction c CIH. intros.
    icbn. sinv H.
    - cbn. unfold remove_events. rewrite <- H1. cbn. auto with itree.
    - unfold remove_events. rewrite <- H0. cbn. constructor. apply CIH.
      auto.
  Qed.

  Lemma remove_events_eventless : forall (E1 E2: Type -> Type) (A : Type)
                                         (t : itree E1 A),
      eventless (@remove_events E1 E2 A t).
  Proof.
    intros E1 E2 A. coinduction c CIH. intros.
    icbn. unfold remove_events. destruct (observe t) eqn : Heq.
    - cbn. constructor.
    - cbn. constructor. apply CIH.
    - cbn. constructor. do 2 step. apply eventless_spin. 
  Qed.

  Lemma delay_eventless : forall (A : Type) (d : Delay A),
      eventless d.
  Proof.
    intros A. coinduction c CIH. intros.
    icbn. destruct (observe d); auto with itree.
    destruct e.
  Qed.

  Lemma eqitE_inv_Tau : forall (E1 E2 : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
            (t1 : itree E1 R1) (t2 : itree E2 R2),
            eqitE RR (Tau t1) (Tau t2) -> eqitE RR t1 t2.
  Proof.
    intros E1 E2 R1 R2 RR.

    coinduction c CIH. intros. icbn. 
    intros.
    step in H. 
    remember (TauF t1) as ot1. 
    remember (TauF t2) as ot2. 
    revert t1 t2 Heqot1 Heqot2. cbn in H. 
    induction H; intros t1' t2' Heqot1 Heqot2; try easy; subst.
    - inv Heqot1; inv Heqot2. now step.  
    - inv H; inv Heqot1; simpobs. 
      + constructor. now apply IHeqitEF. 
      + constructor. now apply IHeqitEF.
      + now do 2 step. 
    - inv H; inv Heqot2; simpobs. 
      + constructor. now apply IHeqitEF. 
      + now do 2 step. 
      + constructor. now apply IHeqitEF. 
  Qed. 


  Lemma inv_remove_events : forall (E1 E2 : Type -> Type) (R : Type)
                                   (t1 : itree E1 R) (t2 : itree E2 R),
      eventless t1 -> eventless t2 -> @remove_events E1 E2 R t1 ≈ @remove_events E2 E2 R t2 ->
      equivE t1 t2.
  Proof.
    intros E1 E2 R. coinduction c CIH.
    intros t1 t2 Hev1 Hev2 Heutt. icbn.
    step in Heutt. dependent induction Heutt; subst.
    - unfold remove_events in x0, x.
      destruct (observe t1); destruct (observe t2); try discriminate.
      constructor. cbn in *. inv x0; inv x. 
    - unfold remove_events in x0, x.
      destruct (observe t1) eqn : Heq1; destruct (observe t2) eqn : Heq2; try discriminate.
      + cbn in *. constructor.
        inv x0. inv x. intros.  
        apply CIH; auto.
        * specialize (itree_eta t1) as Ht1. rewrite Heq1 in Ht1.
          assert (t ≈ t1).
          { rewrite Ht1. rewrite tau_eutt. reflexivity. }
          rewrite H. auto.
        * specialize (itree_eta t2) as Ht2. rewrite Heq2 in Ht2.
          assert (t0 ≈ t2).
          { rewrite Ht2. rewrite tau_eutt. reflexivity. }
          rewrite H. auto.
      + sinv Hev2.
        * rewrite Heq2 in H0. discriminate.
        * rewrite Heq2 in H. discriminate.
      + sinv Hev1.
        * rewrite Heq1 in H0. discriminate.
        * rewrite Heq1 in H. discriminate.
      + sinv Hev1.
        * rewrite Heq1 in H0. discriminate.
        * rewrite Heq1 in H. discriminate.
    - unfold remove_events in *. destruct (observe t1); cbn in x0; discriminate.
    - unfold remove_events in x. destruct (observe t1) eqn : Heq; cbn in *; try discriminate.
      + injection x as x. constructor.
        apply IHHeutt; auto.
        * specialize (itree_eta t1) as Ht1. rewrite Heq in Ht1.
          assert (t ≈ t1).
          { rewrite Ht1. rewrite tau_eutt. reflexivity. }
           rewrite  H. auto.
        * unfold remove_events. rewrite x. auto.
      + exfalso. specialize (itree_eta t1) as Ht1. rewrite Heq in Ht1.
        rewrite Ht1 in Hev1. sinv Hev1.
    - unfold remove_events in x. destruct (observe t2) eqn : Heq; cbn in *; try discriminate.
      + injection x as x. constructor.
        apply IHHeutt; auto.
        * specialize (itree_eta t2) as Ht2. rewrite Heq in Ht2.
          assert (t ≈ t2).
          { rewrite Ht2. rewrite tau_eutt. reflexivity. }
          rewrite H. auto.
        * unfold remove_events. rewrite x. auto.
      + exfalso. specialize (itree_eta t2) as Ht2. rewrite Heq in Ht2.
        rewrite Ht2 in Hev2. sinv Hev2.
  Qed.

  Lemma remove_events_eqitE : forall (E1 E2 E3 E4 : Type -> Type) (R1 R2 : Type)
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eqitE RR (@remove_events E1 E3 R1 t1) (@remove_events E2 E4 R2 t2).
  Proof.
    intros E1 E2 E3 E4 R1 R2 RR. coinduction c CIH. intros.
    step in H. icbn. unfold remove_events.
    induction H; cbn; auto with itree.
    constructor. apply CIH; auto.
  Qed.

  Lemma eqitE_trans : forall (E1 E2 E3 : Type -> Type) (R : Type)
                             (t1 : itree E1 R) (t2 : itree E2 R) (t3 : itree E3 R),
      equivE t1 t2 -> equivE t2 t3 -> equivE t1 t3.
  Proof.
    intros E1 E2 E3 R t1 t2 t3 Ht12 Ht23.
    assert (Ht1 : eventless t1).
    { eapply eqitE_imp_eventlessl; eauto. }
    assert (Ht2 : eventless t2).
    { eapply eqitE_imp_eventlessl; eauto. }
    assert (Ht3 : eventless t3).
    { eapply eqitE_imp_eventlessr; eauto. }
    apply inv_remove_events; auto.
    assert (remove_events t1 ≈ @remove_events E2 E3 _ t2).
    {
      apply eqitE_imp_eutt. apply remove_events_eqitE. auto.
    }
    assert (remove_events t2 ≈ @remove_events E3 E3 _ t3).
    {
      apply eqitE_imp_eutt. apply remove_events_eqitE. auto.
    }
    rewrite H. auto.
  Qed.

  Lemma equivE_sym : forall (E1 E2 : Type -> Type) (R : Type)
                            (t1 : itree E1 R) (t2 : itree E2 R),
      equivE t1 t2 -> equivE t2 t1.
  Proof.
    intros E1 E2 R. coinduction c CIH. intros.
    step in H. icbn. 
    induction H; eauto with itree.
  Qed.


  Instance proper_eutt_equivE_imp {E1 E2} {R} : Proper (eutt eq ==> (eutt eq) ==> Basics.impl) (@equivE E1 E2 R).
  Proof.
    intros t1 t2 Ht12 t3 t4 Ht34. intro.
    apply eqitE_imp_eventlessl in H as Ht1.
    apply eqitE_imp_eventlessr in H as Ht3.
    assert (Ht2 : eventless t2).
    { rewrite <- Ht12. auto. }
    assert (Ht4 : eventless t4).
    { rewrite <- Ht34. auto. }
    apply eqitE_trans with (t2 := t1).
    - symmetry in Ht12. red. apply eutt_eventless; auto.
    - apply eqitE_trans with (t2 := t3); auto.
      apply eutt_eventless; auto.
  Qed.

  Instance proper_eutt_equivE  {E1 E2} {R}  :Proper (  eutt eq ==> (eutt eq) ==> iff) (@equivE E1 E2 R).
  Proof.
    split; intros.
    - rewrite <- H. rewrite <- H0. auto.
    - symmetry in H. symmetry in H0.
      rewrite <- H. rewrite <- H0. auto.
  Qed.


  (*could also use an eventless predicate*)


  (*this is a key part of an effect observation from *)
  CoInductive itree_includes' {R : Type} : itree E R -> stream Ev -> Delay R -> Prop :=
    | includes_base (t : itree E R) (d : Delay R) : equivE t d -> itree_includes' t Nil d
    | cont_vis {A} (e : E A) (a : A) (k : A -> itree E R) (t : itree E R) (s : stream Ev ) (d : Delay R) :
        Vis e k ≈ t ->
        itree_includes' (k a) s d -> itree_includes' t (Cons (ev A e a) s ) (Tau d).

  Variant itree_includesF {R : Type} (F : itree E R -> stream Ev -> Delay R -> Prop) :
    itree E R -> stream Ev -> Delay R -> Prop :=
    | includes_baseF (t : itree E R) (d : Delay R) : equivE t d -> itree_includesF F t Nil d
    | cont_visF {A} (e : E A) (a : A) (k : A -> itree E R) (t : itree E R) (s : stream Ev) (d : Delay R) :
        Vis e k ≈ t ->
        F (k a) s d -> itree_includesF F t (Cons (ev A e a) s) (Tau d).

  Hint Constructors itree_includesF : itree. 

  Lemma itree_includes_mono {R} : Proper (leq ==> leq) (@itree_includesF R).
  Proof. monauto. Qed. 

  Definition itree_includes_mon {R} := Build_mon (@itree_includes_mono R).   

  Definition itree_includes {R : Type} : itree E R -> stream Ev -> Delay R -> Prop :=
    gfp (@itree_includes_mon R).

End ITreeDijkstra.

Section RetBindCounter.

  Variant Sound : Type -> Prop :=
    Ring : Sound unit.

  (* Program Definition ret_itree (A : Type) (a : A) : ITreeSpec A := fun p => p (Ret a). *)

  (* Program Definition bind_ex (A B: Type) (w: ITreeSpec A) (g : A -> ITreeSpec B) : ITreeSpec B :=
    fun p  =>
      w (fun t => (exists a, may_converge a t /\ g a p) \/ (all_infinite t /\  p (noret_cast t)) ).
*)

  (* ret_bind : forall (a : Type) (x : DelaySpec a), bind x (fun y : a => ret y) ≈ x*)

  Program Definition p : ITDInput Sound unit := fun t => t ≈ Vis Ring (fun _ => Ret tt).
  Next Obligation.
    repeat red. intros. split; rewrite H; auto.
  Qed.


(*PROBLEM: if p just respects eutt, then p (ret a0) might mean
          p expects no events
          consider p := fun t => exists a, t ~ ret a
          but the evidence may_converge a0 t does not force t to be a Ret
          the issue seems to be that
         *)

        (*
          The obvious solution is to further restrict predicates from resp eutt
          to respecting possible convergence. This is a bad solution,
          we want to be able to do something like have a predicate that
          accepts all trees that print 5 and then return 6. This would be
          an illegal predicate
         *)

  Program Definition w : ITreeSpec Sound unit := fun p => p (Vis Ring (fun _ => Ret tt) ).
  (* This proof is hideous for a few reasons but it is a good start,
    and great confirmation that our whole IBranch excursion wasn't a
    soul crushing waste of time
   *)
  Lemma bind_ret_failure : ~ forall p, p ∈ w -> p ∈ (bind_ex Sound _ _ w (fun a => ret_itree Sound _ a) ).
  Proof.
    cbn. intros Hcontra.
    specialize (Hcontra p).
    assert (p ∋ Vis Ring (fun _ => Ret tt)).
    {
      unfold p. cbn. reflexivity.
    }
    apply Hcontra in H. clear Hcontra. basic_solve.
    - unfold p in H0. cbn in H0. sinv H0.
    - clear H0. sinv H; try apply all_infiniteF_mono'. ddestruction.
      specialize (H1 tt). step in H1; try apply all_infiniteF_mono'.
      inv H1.
  Qed.

End RetBindCounter.
