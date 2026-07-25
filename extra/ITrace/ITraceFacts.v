From Coinduction Require Import all. 

From Stdlib Require Import
     Morphisms.
     

From ITree Require Import
     Utils
     Axioms
     ITree
     ITreeFacts
     Eq.Rutt
     Eq.RuttFacts
     Props.Infinite.

From ITree.Extra Require Import
     ITrace.ITraceDefinition
.

Set Implicit Arguments.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Tactic Notation "step" := repeat red; step. 
Tactic Notation "step" "in" ident(h) := repeat red in h; step in h. 
Tactic Notation "sinv" ident(h) := step in h; inv h. 

Lemma classic_empty : forall (A : Type), ( exists e : A + (A -> void), True ).
Proof.
  intros. destruct (classic (exists a : A, True)).
  - destruct H; eauto.
  - assert (f : A -> void); eauto. intros.
    exfalso. apply H; eauto.
Qed.

Lemma REvRef_inv {E A} (e e' : E A) (a : A)
  : REvRef E unit A (evans A e a) e' -> e = e'.
Proof.
  intros x. inversion x. ddestruction. reflexivity.
Qed.

Lemma rer_inv {E A} ea e
  : REvRef E unit A ea e -> exists a, ea = evans A e a.
Proof.
  intros x. inversion x.
  - ddestruction. eexists; reflexivity.
  - enough (unit -> void) by contradiction. destruct H. auto.
Qed.

Lemma may_converge_trace : forall (E : Type -> Type) (R : Type)
                             (b : itrace E R) (r1 r2 : R),
    may_converge r1 b -> may_converge r2 b -> r1 = r2.
Proof.
  intros. induction H; inv H0. 
  - rewrite H in H1. sinv H1.
  - rewrite H in H1. sinv H1.
  - destruct e. destruct b. apply IHmay_converge.
    + rewrite H in H2. sinv H2. 
    + contra_void. 
  - destruct e; try contra_void. 
    destruct e0; try contra_void.
    destruct b. destruct b0.
    apply IHmay_converge. rewrite H in H2.
    sinv H2. ddestruction.
    subst. enough (k tt ≈ k0 tt); try apply REL.
    rewrite H0. auto.
Qed.

Lemma finite_nil {E : Type -> Type} : finite (@Nil E).
Proof.
  apply conv_ret. unfold Nil. reflexivity.
Qed.

Lemma finite_list_to_stream : forall (E : Type -> Type) (l : ev_list E),
    finite (ev_list_to_stream l).
Proof.
  red. intros. induction l.
  - cbn. constructor. reflexivity.
  - cbn. eapply conv_vis; try reflexivity. simpl. eauto.
    Unshelve. exact tt.
Qed.

Lemma finite_stream_list : forall (E : Type -> Type) (s : ev_stream E),
    finite s -> exists l, (s ≈ ev_list_to_stream l)%itree.
Proof.
  intros. red in H. induction H.
  - exists nil. auto.
  - destruct IHmay_converge as [l Hl]. unfold ev_list in l.
    inversion e. subst.
    exists (cons e l). simpl. rewrite H.
    destruct b. 
    apply eqit_Vis. 
    intros. now destruct u.
    subst. contradiction.
Qed.

Lemma append_vis : forall (E : Type -> Type) (R : Type)
                     (e : EvAns E unit) (k : unit -> ev_stream E) (b : itrace E R),
    Vis e k ++ b ≈ Vis e (fun a => k a ++ b).
Proof.
  intros E R. unfold append. intros.
  step. cbn. evis. 
Qed.

Global Instance proper_append {E R} : Proper (@eutt (EvAns E) unit unit eq ==> @eutt (EvAns E) R R eq ==> eutt eq) (@append E R).
Proof.
  intros log1 log2 Hlog b1 b2 Hb. unfold append. rewrite Hlog.
  eapply eutt_bind_eutt; eauto.
Qed.

Lemma may_converge_append : forall (E : Type -> Type) (R : Type)
                              (log : ev_stream E) (r : R),
    finite log -> may_converge r (log ++ Ret r).
Proof.
  intros. induction H.
  - unfold append. rewrite H. rewrite bind_ret_l.
    constructor. reflexivity.
  - rewrite H. inversion e. subst. rewrite append_vis.
    eapply conv_vis; eauto; try reflexivity. simpl. eauto.
    subst. contradiction.
Qed.

Lemma converge_itrace_ev_list : forall (E : Type -> Type) (R : Type)
                                  (b : itrace E R) (r : R),
    may_converge r b -> (exists log, (ev_list_to_stream log) ++ Ret r ≈ b)%itree .
Proof.
  intros. induction H.
  - exists nil. cbn. rewrite H.
    step. cbn. eret.  
  - destruct IHmay_converge as [log Hlog]. inversion e. subst.
    exists (cons e log). cbn. rewrite append_vis. rewrite H.
    step. constructor. intros. destruct v.  
    destruct b. apply Hlog. subst. contradiction.
Qed.

Lemma classic_converge_itrace : forall (E : Type -> Type) (R : Type) (b : itrace E R),
    (exists r, exists log, ( (ev_list_to_stream log) ++ Ret r ≈ b)%itree ) \/ all_infinite b.
Proof.
  intros.
  destruct (classic_converge b); auto. destruct H as [r Hr]. left.
  exists r. apply converge_itrace_ev_list. auto.
Qed.

Arguments classic_converge_itrace {E} {R}.

Lemma append_nil : forall (E : Type -> Type) (R : Type) (b : itrace E R),
    (Ret tt ++ b ≈ b)%itree.
Proof.
  intros. unfold append. rewrite bind_ret_l. reflexivity.
Qed.

Lemma append_assoc : forall (E : Type -> Type) (R : Type) (b : itrace E R)
                       (log log' : ev_list E),
    ev_list_to_stream (log ++ log')%list ++ b ≈
                      (ev_list_to_stream log) ++ (ev_list_to_stream log') ++ b.
Proof.
  intros E R b log. induction log.
  - simpl. intros. rewrite append_nil. reflexivity.
  - cbn. intros. rewrite append_vis. setoid_rewrite IHlog.
    rewrite append_vis. reflexivity.
Qed.

Lemma append_div : forall (E : Type -> Type) (R : Type) (b : itrace E R)
                     (log : ev_list E),
    all_infinite b -> all_infinite ((ev_list_to_stream log) ++ b).
Proof.
  intros. induction log.
  - cbn. unfold append. rewrite bind_ret_l. auto.
  - cbn. unfold append.
    step. repeat red. cbn. constructor. intro. auto. 
Qed.

Lemma inv_append_eutt : forall (E : Type -> Type) (R : Type) (r1 r2 : R)
                          (log1 log2 : ev_list E),
    ((ev_list_to_stream log1) ++ Ret r1 ≈ (ev_list_to_stream log2) ++ Ret r2)%itree ->
    log1 = log2 /\ r1 = r2.
Proof.
  intros. generalize dependent log2. induction log1; intros.
  - destruct log2.
    + split; auto. cbn in H. sinv H. 
    + sinv H.
  - destruct log2.
    + sinv H.
    + cbn in H. unfold append in H. sinv H. cbn in *. ddestruction.
      enough (log1 = log2 /\ r1 = r2).
      { destruct H. subst. auto. }
      apply IHlog1. apply REL. apply tt.
Qed.

Lemma trace_refine_proper_left' : forall (E : Type -> Type) (R : Type) (b1 b2 : itrace E R)
                                    (t : itree E R), (b1 ≈ b2) -> rutt (REvRef E) (RAnsRef E) eq b1 t ->
                                                     rutt (REvRef E) (RAnsRef E) eq b2 t.
Proof.
  intros E R. icoinduction c CIH. intros. 
  step in H0. repeat red in H0. step in H.
  genobs t ot3. clear Heqot3. 
  hinduction H before CIH; intros; subst; eauto.
  - remember (RetF r2) as ot1. hinduction H0 before CIH; intros; inv Heqot1; eauto.  
    + constructor. auto.
    + constructor. eapply IHruttF; eauto.
  (* Tau Tau case causes the most problems, seems *)
  -  assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
     { destruct ot3; eauto; right; red; intros; inv H. }
     destruct DEC as [EQ | EQ].
     + destruct EQ as [m3 ?]; subst.
       constructor. eapply CIH; eauto.
       apply rutt_inv_Tau. now step. 
     + inv H0; try (exfalso; eapply EQ; eauto; fail).
       constructor.
       step in REL. 
       hinduction H1 before CIH; intros; subst; try (exfalso; eapply EQ; eauto; fail).
       * dependent induction REL; rewrite <- x.
         ++ constructor. auto.
         ++ constructor. eapply IHREL; eauto.
       * dependent induction REL; rewrite <- x.
         ++ constructor; auto. intros. apply H0 in H1. 
            eapply CIH. apply REL. assumption. 
         ++ constructor. eapply IHREL; eauto.
       * eapply IHruttF; eauto. clear IHruttF.
         dependent induction REL; try (exfalso; eapply EQ; eauto; fail).
         ++ rewrite <- x. constructor; auto. now unstep. 
         ++ auto.
         ++ rewrite <- x. constructor; auto. eapply IHREL; eauto.
  - remember (VisF e k1) as ot1.
    hinduction H0 before CIH; intros; dependent destruction Heqot1.
    + constructor; auto. intros. apply H0 in H1.
      eapply CIH. apply REL. assumption. 
    + constructor. eapply IHruttF; eauto.
  - eapply IHeqitF; eauto. remember (TauF t1) as otf1.
    hinduction H0 before CIH; intros; dependent destruction Heqotf1; eauto.
    + constructor. now unstep. 
    + constructor. eapply IHruttF; eauto.
  - constructor. eapply IHeqitF; eauto.
Qed.

Lemma trace_refine_proper_right' : forall (E : Type -> Type) (R : Type) (b : itrace E R)
                                     (t1 t2 : itree E R), t1 ≈ t2 -> rutt (REvRef E) (RAnsRef E) eq b t1 ->
                                                          rutt (REvRef E) (RAnsRef E) eq b t2.
Proof.
  intros E R. icoinduction c CIH. intros. step in H. 
  step in H0. repeat red in H0. 
  genobs_clear t2 ot2.
  hinduction H before CIH; intros; clear t1; subst; eauto.
  - remember (RetF r2) as ot1. hinduction H0 before CIH; intros; inv Heqot1; eauto.
    + constructor; auto.
    + constructor. eauto.
  - remember (TauF m1) as otm1.
    hinduction H0 before CIH; intros; subst; try (inv Heqotm1).
    + constructor. eapply CIH; eauto.
    + constructor. eapply CIH; eauto.
      apply rutt_inv_Tau_r. now step. 
    + step in REL. 
      dependent induction REL; subst.
      * constructor. clear IHruttF.
        hinduction H0 before CIH; intros; dependent destruction x0.
        ++ rewrite <- x. constructor. auto.
        ++ constructor. auto.
      * eapply IHruttF. 2 : symmetry; eauto.
        step. rewrite <- x. constructor; auto.
        now step in REL. 
      * constructor. rewrite <- x.
        clear IHruttF. hinduction H0 before CIH; intros; dependent destruction x0.
        ++ constructor; auto. intros. apply H0 in H1.
          eapply CIH. apply REL. assumption. 
        ++ constructor. eapply IHruttF; eauto.
      * unstep in REL. eapply IHruttF; eauto.
      * constructor. rewrite <- x. eapply IHREL; eauto.
  - remember (VisF e k1) as ot1. hinduction H0 before CIH; intros; inv Heqot1.
    + ddestruction. constructor; auto. intros. apply H0 in H1.
      eapply CIH. apply REL. assumption. 
    + constructor. eauto.
  - eapply IHeqitF; eauto. remember (TauF t0) as otf0.
    hinduction H0 before CIH; intros; dependent destruction Heqotf0; eauto.
    + constructor. now unstep. 
    + constructor. eapply IHruttF; eauto.
  - constructor. eapply IHeqitF; eauto.
Qed.

#[global] Instance trace_refine_proper {E R} : Proper (@eutt E R R eq ==> eutt eq ==> iff) trace_refine.
Proof.
  intros b1 b2 Heuttb t1 t2 Heuttt.
  split; intros;
    try (eapply trace_refine_proper_right'; [eauto | eapply trace_refine_proper_left'; eauto]).
    now rewrite Heuttb, Heuttt.
Qed.

Lemma trace_refine_ret : forall (E : Type -> Type) (R : Type) (r : R),
    @trace_refine E R (Ret r) (Ret r).
Proof.
  intros. step. constructor. auto.
Qed.

Lemma trace_refine_ret_inv_r : forall (E : Type -> Type) (R : Type) (r : R)
                                 (t : itree E R),
    Ret r ⊑ t -> t ≈ Ret r.
Proof.
  intros. step. step in H. repeat red in H. 
  dependent induction H; subst.
  - rewrite <- x. constructor. auto.
  - rewrite <- x. constructor; auto.
Qed.

Lemma trace_refine_ret_inv_l : forall (E : Type -> Type) (R : Type) (r : R)
                                 (b : itrace E R),
    b ⊑ Ret r -> (b ≈ Ret r)%itree.
Proof.
  intros. step. step in H. repeat red in H.
  dependent induction H; subst.
  - rewrite <- x. constructor. auto.
  - rewrite <- x. constructor; auto.
Qed.

Lemma trace_refine_vis_inv : forall (E : Type -> Type) (R A: Type) (e : E A) (a : A)
                               (b :itrace E R) (k : A -> itree E R),
    trace_refine (Vis e k) (Vis (evans A e a) (fun _ => b))  -> trace_refine (k a) b .
Proof.
  intros E R A e a. intros.
  red in H. red. step in H. repeat red in H. inv H. ddestruction.
  subst.
  assert (RAnsRef E unit A (evans A e a) tt e a); eauto with itree.
Qed.

Lemma trace_refine_vis_add : forall (E : Type -> Type) (R A: Type) (e : E A) (a : A)
                               (b :itrace E R) (k : A -> itree E R),
    b ⊑ k a -> Vis (evans A e a) (fun _ => b) ⊑ Vis e k.
Proof.
  intros. step. constructor; eauto with itree.
  intros. inv H0. ddestruction.
  subst. auto.
Qed.

Lemma event_ans_constr : forall (E : Type -> Type) (R : Type) (e : E R),
  exists (A : Type), exists e' : EvAns E A, REvRef E A R e' e.
Proof.
  intros.
  destruct (classic_empty R) as  [ [a | Hempty]  _ ] .
  - exists unit. exists (evans R e a). eauto with itree.
  - exists void. exists (evempty R Hempty e). eauto with itree.
Qed.

(* Here are where some of the sketchy uses of axioms are *)

Section Determinize.

Context (classicT : forall (P : Type), P + (P -> False)).

CoFixpoint determinize_ (E : Type -> Type) (R : Type) (ot : itree' E R) : itrace E R.
Proof.
  destruct ot.
  - apply (Ret r).
  - apply (Tau (determinize_ E R (observe t) ) ).
  - destruct (classicT X) as [ | f].
    + apply (Vis (evans X e x) (fun _ =>  (determinize_ E R (observe (k x)) ) )).
    + apply (Vis (evempty X (fun x => match f x with end) e) (fun v : void => match v return itrace E R with end) ).
Defined.

Definition determinize {E R} (t : itree E R) : itrace E R := determinize_ (observe t).

End Determinize.

(* may be a better idea to make this an axiom *)
Lemma itree_refine_nonempty : forall (E : Type -> Type) (R : Type) (t : itree E R),
  exists b : itrace E R, b ⊑ t.
Proof.
  intros. destruct classicT_inhabited as [classicT].
  exists (determinize classicT t). generalize dependent t.
  icoinduction c CIH. 
  intros. unfold determinize. desobs t Hot.
  - cbn. eret.
  - cbn. constructor. apply CIH. 
  - unfold observe. cbn. destruct (classicT _).
    + constructor; eauto with itree. intros.
      inversion H. ddestruction.
      subst. apply CIH.
    + constructor; auto with itree. intros. contradiction.
Qed.

Lemma refine_set_eq_to_eutt_vis_aux : forall (E : Type -> Type) (R : Type) (r : itree E R -> itree E R -> Prop)
                                             (CIH : forall t1 t2 : itree E R, (forall b : itrace E R, b ⊑ t1 <-> b ⊑ t2) -> r t1 t2)
                                             (t1 t2 : itree E R)
                                             (H0 : forall b : itrace E R, b ⊑ t1 <-> b ⊑ t2)
                                             (A B : Type) (e : E A) (e0 : E B)
                                             (k : A -> itree E R) (k0 : B -> itree E R)
                                             (Ht1 : t1 ≅ Vis e k) (Ht2 : t2 ≅ Vis e0 k0 ),
    eqitF eq true true r (VisF e k) (VisF e0 k0).
Proof.
  intros.
  destruct (classic_empty A) as [ [a | Ha] _ ].
  - specialize  trace_refine_vis_add with (e := e) (k := k) (a := a) as Hbrv.
    assert (exists b, b ⊑ (k a) ).
    { apply itree_refine_nonempty. }
    destruct H as [b Hbk]. apply trace_refine_vis_add with (e := e) in Hbk.
    rewrite <- Ht1 in Hbk.
    apply H0 in Hbk as Hbk0.
    rewrite Ht1 in Hbk. rewrite Ht2 in Hbk0.
    sinv Hbk.
    sinv Hbk0. ddestruction.
    subst.
    inversion H8. ddestruction.
    subst. constructor.
    intros. eapply CIH; eauto.
    intros. setoid_rewrite Ht1 in H0. setoid_rewrite Ht2 in H0.
    split; intros.
    + apply trace_refine_vis_add with (e := e) in H. apply H0 in H.
      apply trace_refine_vis_inv in H. auto.
    + apply trace_refine_vis_add with (e := e) in H. apply H0 in H.
      apply trace_refine_vis_inv in H. auto.
  - set (fun v : void => match v return itrace E R with end) as ke.
    set (Vis (evempty A Ha e) ke) as b.
    assert (b ⊑ t1).
    {
      unfold b. rewrite Ht1. step. cbn.
      constructor. { apply ree. } { intros []. }
    }
    apply H0 in H as H1. unfold b in *. clear b.
    rewrite Ht1 in H. rewrite Ht2 in H1.
    sinv H. sinv H1. ddestruction.
    subst. inversion H6. ddestruction.
    constructor.
    intros. eapply CIH.
    intros. setoid_rewrite Ht1 in H0. setoid_rewrite Ht2 in H0.
    split; intros; contradiction.
Qed.

Lemma trace_refine_vis : forall (E : Type -> Type) (R A : Type) (b : itrace E R)
                           (e : E A) (k : A -> itree E R),
    b ⊑ Vis e k -> exists X, exists e0 : EvAns E X, exists k0, (b ≈ Vis e0 k0)%itree.
Proof.
  intros. step in H. repeat red in H. 
  dependent induction H.
  - exists A0. exists e1. exists k1.
    specialize (itree_eta b) as Hb. rewrite <- x in Hb.
    rewrite Hb. reflexivity.
  - enough
      (exists (X : Type) (e0 : EvAns E X) (k0 : X -> itree (EvAns E) R), (t1 ≈ Vis e0 k0)%itree).
    {
      destruct H0 as [ X [e0 [k0 Ht1] ] ].
      exists X. exists e0. exists k0.
      specialize (itree_eta b) as Hb. rewrite <- x in Hb. rewrite Hb.
      rewrite tau_eutt. auto.
    }
    eapply IHruttF; eauto.
Qed.

Lemma trace_refine_vis_l : forall (E : Type -> Type) (R A: Type) (t : itree E R)
                                  (e : EvAns E A) (k : A -> itrace E R),
    Vis e k ⊑ t -> exists X, exists e0 : E X, exists k0 : X -> itree E R, t ≈ Vis e0 k0.
Proof.
  intros. step in H. repeat red in H. 
  dependent induction H.
  - exists B. exists e2.  exists k2. specialize (itree_eta t) as Ht.
    rewrite <- x in Ht. rewrite Ht. reflexivity.
  - assert (t2 ≈ t).
    {
      specialize (itree_eta t). rewrite <- x. intros.
      rewrite H0. rewrite tau_eutt. reflexivity.
    }
    setoid_rewrite <- H0. eapply IHruttF; eauto.
Qed.

Lemma trace_refine_may_converge_ex : forall (E : Type -> Type) (R : Type)
                                            (t : itree E R) (r : R),
    may_converge r t -> exists b, may_converge r b /\ b ⊑ t.
Proof.
  intros. induction H.
  - exists (Ret r). rewrite H. split.
    + constructor. reflexivity.
    + apply trace_refine_ret.
  - destruct IHmay_converge as [br [Hrbr Hrefbr] ].
    exists  (Vis (evans B e b) (fun _ => br) ). split.
    + eapply conv_vis; try reflexivity. eauto. Unshelve. exact tt.
    + rewrite H. apply trace_refine_vis_add. auto.
Qed.

Lemma trace_refine_may_converge : forall (E : Type -> Type) (R : Type)
                                         (t : itree E R) (r : R) (b : itrace E R),
    may_converge r b -> b ⊑ t -> may_converge r t.
Proof.
  intros. generalize dependent t. induction H; intros.
  - rewrite H in H0. apply trace_refine_ret_inv_r in H0.
    rewrite H0. constructor. reflexivity.
  - rewrite H in H1. apply trace_refine_vis_l in H1 as Ht0.
    destruct Ht0 as [X [e0 [k0 Ht0] ] ].
    rewrite Ht0 in H1. sinv H1. subst.
    ddestruction. subst. rewrite Ht0.
    inversion H4; subst; ddestruction; subst; try contradiction.
    eapply conv_vis; try reflexivity. Unshelve. 2 : exact a.
    apply IHmay_converge. 
    specialize (H9 tt a). assert (RAnsRef E unit X (evans X e0 a) tt e0 a).
    constructor. apply H9 in H1. destruct b. auto.
Qed.

Lemma trace_refine_all_infinite : forall (E : Type -> Type) (R : Type)
                                    (t : itree E R) (b : itrace E R),
    all_infinite t -> b ⊑ t -> all_infinite b.
Proof.
  intros E R. unfold all_infinite at -1. 
  coinduction c CIH. 
  intros. step in H. step in H0. repeat red in H, H0; repeat red.   
  dependent induction H0.
  - rewrite <- x in H. inv H. 
  - rewrite <- x0. constructor. eapply CIH; eauto.
    rewrite <- x in H. inv H.
  - rewrite <- x0. rewrite <- x in H. constructor. inv H.
    ddestruction. subst. intros. 
    inv H1; subst; ddestruction; try contradiction. destruct b0.
    eapply CIH; try apply H3.
    specialize (H0 tt a). assert (RAnsRef _ _ _ (evans B e2 a) tt e2 a ).
    constructor. apply H0 in H. eauto.
  - rewrite <- x. constructor. apply (b_chain c). eapply IHruttF; eauto.
  - eapply IHruttF; auto. rewrite <- x in H. inv H.
    now step in H2. 
Qed.

Lemma trace_refine_converge_bind : forall (E : Type -> Type) (R S : Type)
                                          (b : itrace E R) (t : itree E R) (f : R -> itrace E S) (g : R -> itree E S) (r : R),
    may_converge r b -> b ⊑ t -> f r ⊑ g r -> ITree.bind b f ⊑ ITree.bind t g.
Proof.
  intros. generalize dependent t. dependent induction H; intros.
  - rewrite H. rewrite H in H0. apply trace_refine_ret_inv_r in H0.
    rewrite H0. repeat rewrite bind_ret_l. auto.
  - specialize (IHmay_converge H1).
    rewrite H in H2. apply trace_refine_vis_l in H2 as Ht.
    destruct Ht as [X [e0 [k0 Ht] ] ].
    rewrite Ht in H2. step in H2. repeat red in H2. inv H2. 
    ddestruction. subst.
    inversion H5; subst; ddestruction; try easy. 
    rewrite H. rewrite Ht.
    step. repeat red. cbn. constructor; auto.
    intros. apply H10 in H2.
    destruct a0. destruct b. apply IHmay_converge. auto.
Qed.

Lemma trace_refine_diverge_bind : forall (E : Type -> Type) (R S : Type)
                                         (b : itrace E R) (t : itree E R) (f : R -> itrace E S) (g : R -> itree E S),
    all_infinite b -> b ⊑ t -> ITree.bind b f ⊑ ITree.bind t g.
Proof.
  intros E R S b t f g. generalize dependent b. generalize dependent t.
  red. icoinduction c CIH. intros.
  step in H0. 
  step in H. repeat red in H0, H. 
  dependent induction H0.
  - rewrite <- x0 in H. inv H.
  - unfold observe. cbn. rewrite <- x0. rewrite <- x.
    cbn. constructor. apply CIH; auto.
    rewrite <- x0 in H. inv H. 
  - unfold observe. cbn. rewrite <- x0. rewrite <- x. cbn. constructor; auto.
    intros.
    rewrite <- x0 in H. inv H. ddestruction. subst. 
    apply H0 in H2. eapply CIH; eauto. apply H4.
  - unfold observe at 1. cbn. rewrite <- x. cbn. constructor.
    eapply IHruttF; eauto. rewrite <- x in H. inv H. now unstep.
  - unfold observe at 2. cbn. rewrite <- x. cbn. constructor.
    eapply IHruttF; eauto.
Qed.

Lemma refine_set_eq_to_eutt : forall (E : Type -> Type) (R : Type) (t1 t2 : itree E R),
    (forall b, b ⊑ t1 <-> b ⊑ t2) -> t1 ≈ t2.
Proof.
  intros E R. icoinduction c CIH. intros.
  remember (observe t1) as ot1. remember (observe t2) as ot2.
  destruct (ot1); destruct (ot2).
  all: specialize (itree_eta t1) as Ht1; rewrite <- Heqot1 in Ht1;
    specialize (itree_eta t2) as Ht2; rewrite <- Heqot2 in Ht2.
  (*Ret Ret*)
  - specialize (H (Ret r0)) as Hr0.
    rewrite Ht1 in Hr0. rewrite Ht2 in Hr0. 
    assert (Ret r0 ⊑ t1).
    { rewrite Ht1. apply Hr0. step. eret. }
    rewrite Ht1 in H0. sinv H0. 
  (*Ret Tau *)
  - setoid_rewrite Ht2 in H.
    specialize (H (Ret r) ).
    rewrite tau_eutt in H. taur. 
    assert (Ret r ⊑ t1).
    { rewrite Ht1. step. eret. }
    apply H in H0. step in H0. repeat red in H0; cbn in H0.
    clear H Ht1 Ht2 Heqot1 Heqot2. dependent induction H0.
    + rewrite <- x. eret. 
    + rewrite <- x. taur; auto.   
  (*Ret Vis*)
  - exfalso.
    assert (Ret r ⊑ t1).
    { rewrite Ht1. step. eret. }
    apply H in H0. rewrite Ht2 in H0. sinv H0. 
  (*Tau Ret*)
  - setoid_rewrite Ht1 in H. setoid_rewrite Ht2 in H.
    assert (Ret r ⊑ t2).
    { rewrite Ht2. step. eret. }
    rewrite Ht2 in H0. apply H in H0 as H1. step in H1. 
    clear Heqot1 Heqot2 Ht1 Ht2 H H0. repeat red in H1. cbn in *.
    taul. inv H1. dependent induction H2; intros; subst.
    + rewrite <- x. eret. 
    + rewrite <- x. taul; auto. 
  (*Tau Tau*)
  - constructor. eapply CIH. 
    intros.
    assert (t1 ≈ t). { rewrite Ht1. rewrite tau_eutt. reflexivity. }
    assert (t2 ≈ t0). { rewrite Ht2. rewrite tau_eutt. reflexivity. }
    now rewrite <- H0, <- H1. 
  (*Tau Vis*)
  - specialize (itree_refine_nonempty t1) as [b Hbt1].
    apply H in Hbt1 as Hbt2. rewrite Ht1 in Hbt1.
    rewrite tau_eutt in Hbt1.
    rewrite Ht2 in Hbt2.
    apply trace_refine_vis in Hbt2 as Hb.
    destruct Hb as [Y [e0 [k0 Hb] ] ].
    rewrite Hb in Hbt2.
    rewrite Hb in Hbt1. clear Hb b.
    constructor; auto.
    setoid_rewrite Ht1 in H. setoid_rewrite tau_eutt in H.
    clear Heqot1 Heqot2. clear Ht1 t1.
    step in Hbt1. repeat red in Hbt1. cbn in *.
    dependent induction Hbt1.
    + rewrite <- x.
      specialize (itree_eta t) as Ht. rewrite <- x in Ht.
      eapply refine_set_eq_to_eutt_vis_aux; eauto.
    + rewrite <- x. constructor; auto. eapply IHHbt1; eauto.
      assert (t0 ≈ t).
      {
        specialize (itree_eta t) as Ht. rewrite <- x in Ht. rewrite Ht.
        rewrite tau_eutt. reflexivity.
      }
      setoid_rewrite H0. auto.
  (*Vis Ret*)
  - exfalso.
    assert (Ret r ⊑ t2).
    { rewrite Ht2. step. eret. }
    apply H in H0. rewrite Ht1 in H0. sinv H0.
  (*Vis Tau*)
  - specialize (itree_refine_nonempty t2) as [b Hbt2].
    apply H in Hbt2 as Hbt1. rewrite Ht1 in Hbt1.
    rewrite Ht2 in Hbt2.
    rewrite tau_eutt in Hbt2.
    apply trace_refine_vis in Hbt1 as Hb.
    destruct Hb as [Y [e0 [k0 Hb] ] ].
    rewrite Hb in Hbt2.
    rewrite Hb in Hbt1. clear Hb b.
    constructor; auto.
    setoid_rewrite Ht2 in H. setoid_rewrite tau_eutt in H.
    clear Heqot1 Heqot2. clear Ht2 t2.
    step in Hbt2. repeat red in Hbt2. cbn in *.
    dependent induction Hbt2.
    + rewrite <- x.
      specialize (itree_eta t) as Ht. rewrite <- x in Ht.
      eapply refine_set_eq_to_eutt_vis_aux; eauto.
    + rewrite <- x. constructor; auto. eapply IHHbt2; eauto.
      assert (t2 ≈ t).
      {
        specialize (itree_eta t) as Ht. rewrite <- x in Ht. rewrite Ht.
        rewrite tau_eutt. reflexivity.
      }
      setoid_rewrite H0. auto.
  (*Vis Vis*)
    - eapply refine_set_eq_to_eutt_vis_aux; eauto.
Qed.

Lemma trace_set_complete : forall E R (t1 t2 : itree E R), (forall b, b ⊑ t1 <-> b ⊑ t2) <-> t1 ≈ t2.
Proof.
  intros. split; intros; try apply refine_set_eq_to_eutt; auto.
  rewrite H. split; auto.
Qed.

Lemma trace_refine_bind_cont_inv : forall (E : Type -> Type) (R S : Type)
                                          (b : itrace E R) (m : itree E R) (g : R -> itrace E S)
                                          (f : R -> itree E S) (r : R),
    may_converge r b -> b ⊑ m -> ITree.bind b g ⊑ ITree.bind m f -> g r ⊑ f r.
Proof.
  intros E R S. red. coinduction c CIH. intros b m g f a Hconv Hrefb Hrefbind.
  generalize  dependent m.
  dependent induction  Hconv; intros m Hrefb Hrefbind.
  - rewrite H in Hrefbind. rewrite bind_ret_l in Hrefbind. rewrite H in Hrefb.
    apply trace_refine_ret_inv_r in Hrefb. rewrite Hrefb in Hrefbind.
    rewrite bind_ret_l in Hrefbind. now step. 
  - (*m must be a vis, the continuations must refine then continuation in the m I use in the
      inductive hypothesis *)
    destruct e; try contradiction. rewrite H in Hrefb.
    rewrite H in Hrefbind. rewrite bind_vis in Hrefbind.
    apply trace_refine_vis_l in Hrefb as Hvis. destruct Hvis as [X [e' [k' Hvis ] ] ].
    rewrite Hvis in Hrefbind. rewrite bind_vis in Hrefbind.
    step in Hrefbind. repeat red in Hrefbind; cbn in Hrefbind. inv Hrefbind.
    ddestruction. inv H2. ddestruction; subst.
    rewrite Hvis in Hrefb. step in Hrefb. repeat red in Hrefb; cbn in Hrefb. inv Hrefb.
    ddestruction.
    assert (RAnsRef E unit A (evans _ e' ans) tt e' ans ); try (constructor; auto; fail).
    specialize (IHHconv (k' ans) ). apply IHHconv.
    + apply H8 in H0. destruct b. auto.
    + apply H7 in H0. destruct b. auto.
Qed.

Lemma may_converge_two_list:
  forall (E : Type -> Type) (A B : Type) (log : ev_list E) (b : itrace E A)
    (a : A) (log' : ev_list E),
    (ev_list_to_stream log) ++ b ≈ (ev_list_to_stream log') ++ Ret a -> may_converge a b.
Proof.
  intros. generalize dependent log'.
  induction log; cbn; intros.
  - simpl in H. setoid_rewrite bind_ret_l in H. rewrite H.
    apply may_converge_append. apply finite_list_to_stream.
  - assert ((Vis a0 (fun _ => ev_list_to_stream log)) ≈ ev_list_to_stream (cons a0 log) )%itree.
    { cbn. reflexivity. }
    rewrite H0 in H.
    destruct log' as [ | h t ].
    + setoid_rewrite bind_ret_l in H. simpl in H. sinv H. 
    + simpl in H. unfold append in H. repeat rewrite bind_vis in H. sinv H.
      ddestruction; subst.
      assert (ev_list_to_stream log ++ b ≈ ev_list_to_stream t ++ Ret a).
      { apply REL. apply tt. }
      eapply IHlog; eauto.
Qed.

Lemma all_infinite_bind_append: forall (E : Type -> Type) (A : Type)
                                  (log : ev_list E) (b' : itree (EvAns E) A),
    all_infinite (ev_list_to_stream log ++ b') -> all_infinite b'.
Proof.
  intros E A log b' Hdiv. induction log.
  - cbn in Hdiv. setoid_rewrite bind_ret_l in Hdiv. auto.
  - apply IHlog. simpl in Hdiv. unfold append in Hdiv.
    rewrite bind_vis in Hdiv. sinv Hdiv. ddestruction. subst. apply H0.
    apply tt.
Qed.
