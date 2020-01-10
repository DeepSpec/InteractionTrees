From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
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
     Dijkstra.StateITreeDijkstra
     Dijkstra.IterRel
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Section StateITreeIter.
  Context (St : Type).
  Lemma equiv_resp_eutt : forall A B (a : A) (s : St), resp_eutt Void _ (fun t : itree Void (St * (A + B)) => t ≈ ret (s,inl a) ).
  Proof.
    intros. intros t1 t2 H. split; intros.
    - rewrite <- H. auto.
    - rewrite H. auto.
  Qed.

  Definition spec_iter_arrow_rel {A B : Type} (f : A -> StateITreeSpec St (A + B)) (p1 p2 : St * A) :=
    let '(s1,a1) := p1 in let '(s2,a2) := p2 in 
    proj1_sig (f a1) (fun t => t ≈ ret (s2,inl a2)) (equiv_resp_eutt A B a2 s2) s1.

  Notation "x =[ f ]=> y" := (spec_iter_arrow_rel f x y) (at level 80).

  Variant iterF_body  {A B : Type} (p : itree Void (St * B) -> Prop ) (Hp : resp_eutt _ _ p)
          (g : A -> StateITreeSpec St (A + B) )  (F : A -> St -> Prop)  (t : itree Void (St * (A + B) )) : Prop:=
  | intern_div (Ht : divergence t) (Hspin : p spin) 
  | term_b (b : B) (s : St) (Ht : (ret (s,(inr b))) ≈ t) (Hbs : p (ret (s,b) ))
  | extern_div (a' : A) (s : St) (Hreta : ret (s,inl a') ≈ t) (Hnwf : not_wf_from _ (fun p1 p2 : (St * A) => p1 =[ g ]=> p2 ) (s,a') ) (Hspin : p spin)
  | cont_a (a' : A) (s : St) (Hreta : ret (s,inl a') ≈ t ) (Hrec : F  a' s ) 
  .
  Hint Constructors iterF_body.

  Lemma iterF_body_resp_eutt : forall A B (p : itree Void (St * B) -> Prop ) (Hp : resp_eutt _ _ p)
          (g : A -> StateITreeSpec St (A + B) ) (F : A -> St -> Prop), 
      resp_eutt _ _ (iterF_body p Hp g F).
  Proof.
    intros. intros t1 t2 Heutt. split; intros; inversion H; clear H.
    - rewrite Heutt in Ht. auto.
    - rewrite Heutt in Ht. eauto.
    - rewrite Heutt in Hreta. eauto.
    - rewrite Heutt in Hreta. eauto.
    - rewrite <- Heutt in Ht. eauto.
    - rewrite <- Heutt in Ht. eauto.
    - rewrite <- Heutt in Hreta. eauto.
    - rewrite <- Heutt in Hreta. eauto.
  Qed.

  Fixpoint approx_iter_fix {A B : Type} (n : nat) (g : A -> StateITreeSpec St (A + B) ) (a : A) (p : itree Void (St * B) -> Prop)
           (Hp : resp_eutt _ _ p) (s : St) : Prop :=
    match n with | 0 => False
                 | S m => proj1_sig (g a) (iterF_body p Hp g (fun a' s' => approx_iter_fix m g a' p Hp s')) 
                                    (iterF_body_resp_eutt A B p Hp g  (fun a' s' => approx_iter_fix m g a' p Hp s')) s  end.

  Definition _iter_fix {A B : Type} (g : A -> StateITreeSpec St (A + B) ) (a : A)
    (p : itree Void (St * B) -> Prop ) (Hp : resp_eutt _ _ p) (s : St) :=
    exists n, approx_iter_fix n g a p Hp s.

  Ltac gen_dep2 a s := generalize dependent a; generalize dependent s.

  Ltac dest_dep f a := destruct (f a) as [?fa ?Hfa] eqn : ?Heq; simpl in *.

  Ltac clear_ret_eutt_spin :=
    match goal with | H : ret ?a ≈ spin  |- _ => simpl in H; exfalso; eapply not_ret_eutt_spin; eauto
                    | H : Ret ?a ≈ spin  |- _ => exfalso; eapply not_ret_eutt_spin; eauto
                    | H : spin ≈ ret ?a  |- _ => exfalso; symmetry in H; eapply not_ret_eutt_spin; eauto
                    | H : divergence (ret _ ) |- _ => pinversion H
                    end.
  
  Ltac invert_evidence :=
    intros; repeat match goal with 
                   | H : _ /\ _ |- _ => destruct H
                   | H : _ \/ _ |- _ => destruct H 
                   | H : iterF_body _ _ _ _ _ |- _ => inversion H; clear H; subst
                   | H : exists a : ?A, _ |- _ => destruct H as [?a ?H]
                   | x : ?A + ?B |- _ => destruct x as [?a | ?b]
                   | x : ?S * ?X |- _ => destruct x as [?s ?x]
                   | H : upaco1 _ _ _ |- _ => pclearbot
           end.

  Ltac invert_ret := simpl in *; match goal with | H : Ret ?a ≈ Ret ?b |- _ => 
                                                   apply inv_ret in H; try discriminate; try (injection H as H);
                                                   subst end.


  Ltac basic_solve := invert_evidence; try clear_ret_eutt_spin; try invert_ret.


  Lemma iter_fix_monot_aux : forall A B n (g : A -> StateITreeSpec St (A + B) ) a (p p' : itree Void (St * B) -> Prop) Hp Hp' s, 
      (forall t, p t -> p' t) -> approx_iter_fix n g a p Hp s-> approx_iter_fix n g a p' Hp' s.
  Proof.
    intros. gen_dep2 a s. induction n; try contradiction. intros.
    cbn. cbn in H0. dest_dep g a. eapply Hfa; try apply H0. clear H0. intros t ?Ht. basic_solve; eauto.
  Qed.

  Lemma iter_fix_monot : forall A B (g : A -> StateITreeSpec St (A + B) ) a, 
      monotonicsi St _ (_iter_fix g a).
  Proof.
    unfold monotonicsi.
    intros. unfold _iter_fix in *. basic_solve. exists n. eapply iter_fix_monot_aux; eauto.
  Qed.

  Definition iter_fix {A B : Type} (g : A -> StateITreeSpec St (A + B) ) (a : A) := exist _ (_iter_fix g a) (iter_fix_monot A B g a).

  Definition STitree (A : Type) := stateT St (itree Void) A.

  Lemma iter_morph_aux_l : forall (A B : Type) (g : A -> STitree (A + B) ) (a : A) (p : itree Void (St * B) -> Prop ) Hp (s : St), 
      p (iter g a s) -> _iter_fix (fun x => obs _ (g x) ) a p Hp s.
  Proof.
   intros. set (fun p1 p2 => p1 =[ fun x => obs _ (g x) ]=> p2) as rg.
   destruct (classic (not_wf_from _ rg (s,a) ) ).
   - admit.
   - specialize (neg_wf_from_not_wf_from) as Hn.
     assert (wf_from (St * A) rg (s,a) ).
     { specialize (Hn _ rg (s,a)). specialize (classic (wf_from _ rg (s,a))); tauto. }
     clear Hn H0.
     set (fun '(s,a) => _iter_fix (fun x => obs _ (g x)) a p Hp s) as P.
     enough (P (s,a)). auto.
     (*some weirdness going on here*)
     set (iter g) as f. unfold Kleisli in f.
     set (fun '(s,a) =>  p (f a s) ) as Q.
     assert (p (f a s) ). auto. clear H. fold (Q (s,a) ) in H0.
     revert H0. unfold f in Q. intros.
     (*I think the weirdness is done now*)
     induction H1; basic_solve.
     + clear a s. rename a0 into a. rename s0 into s.
        unfold P. unfold Q in H0. destruct (eutt_reta_or_div _ (g a s)); basic_solve.
       * specialize (H (s0,a0)). symmetry in H1. contradiction. 
       * exists 1. cbn. red. eapply term_b; eauto.
         eapply Hp; eauto. setoid_rewrite unfold_iter_ktree. simpl.
         rewrite <- H1. setoid_rewrite bind_ret. setoid_rewrite bind_ret.
         simpl. reflexivity.
       * exists 1. cbn. red. eapply intern_div; eauto.
         eapply Hp; eauto. setoid_rewrite unfold_iter_ktree. simpl.
         apply div_spin_eutt in H1. rewrite H1.
         setoid_rewrite <- spin_bind. apply spin_bind.
     + clear a s. rename a0 into a. rename s0 into s. 
       unfold P, Q in *.
       destruct (eutt_reta_or_div _ (g a s)); basic_solve.
       * assert (rg (s,a) (s0, a0)).
         { unfold rg. symmetry in H2. auto. } 
         assert (p (iter g a0 s0)).
         { eapply Hp; eauto. 
           setoid_rewrite unfold_iter_ktree at 2. simpl.
           rewrite <- H2. setoid_rewrite bind_ret. setoid_rewrite bind_ret.
           simpl. cbn. rewrite tau_eutt. reflexivity. }
         specialize (H1 (s0,a0) H3 H4). simpl in H1.
         red in H1. destruct H1 as [n Hiter]. exists (S n). cbn. red.
         eauto.
       * exists 1. cbn. red. eapply term_b; eauto.
         eapply Hp; eauto. setoid_rewrite unfold_iter_ktree. simpl.
         rewrite <- H2. setoid_rewrite bind_ret. setoid_rewrite bind_ret.
         simpl. reflexivity.
       * exists 1. cbn. red. eapply intern_div; eauto.
         eapply Hp; eauto. setoid_rewrite unfold_iter_ktree. simpl.
         apply div_spin_eutt in H2. rewrite H2.
         setoid_rewrite <- spin_bind. apply spin_bind.
  Admitted.

  Lemma iter_morph : forall (A B : Type) (g : A -> STitree (A + B)) (a : A),
      obs _ (iter g a) ≈ iter_fix (fun x => obs _ (g x) ) a.
  Proof.
    intros. constructor.
    - intros. cbn in H. red in H. cbn. apply iter_morph_aux_l. auto.
    - intros. cbn. red. cbn in H. red in H. basic_solve.
      gen_dep2 a s.
      induction n; try contradiction; intros.
      cbn in H. red in H. basic_solve.
      + apply div_spin_eutt in Ht. eapply Hp; eauto.
        setoid_rewrite unfold_iter_ktree. simpl. rewrite Ht.
        repeat (setoid_rewrite <- spin_bind). reflexivity.
      + eapply Hp; eauto. setoid_rewrite unfold_iter_ktree. simpl. rewrite <- Ht.
        repeat (setoid_rewrite bind_ret). simpl. reflexivity.
      + admit. (*need the not_wf spin lemma*)
      + eapply Hp; eauto. setoid_rewrite unfold_iter_ktree at 1. simpl.
        rewrite <- Hreta.
        repeat (setoid_rewrite bind_ret). simpl. rewrite tau_eutt.
        reflexivity.
  Admitted.

  Instance StateITreeMonadITer : MonadIter (StateITreeSpec St) := fun B A => @iter_fix A B.

  Program Definition get_spec : StateITreeSpec St St :=
    fun p _ s => p (ret (s,s)).
  Next Obligation.
  intro. auto.
  Qed.

  Program Definition put_spec (s : St) : StateITreeSpec St unit :=
    fun p _ _ => p (ret (s,tt) ).
  Next Obligation.
  intro. auto.
  Qed.

  Definition HandlerStateITree : (stateE St) ~> (StateITreeSpec St) :=
    fun _ ev =>
      match ev with 
      | Get _ => get_spec
      | Put _ s => put_spec s
      end.

   Definition InterpStateITreeSpec := interp HandlerStateITree.

   Definition get_handle : St -> (itree Void (St * St) ) :=
     fun s => ret (s,s).

   Definition put_handle (s : St) : St -> (itree Void (St * unit )) :=
     fun _ => ret (s, tt).

   Definition HandlerState : (stateE St) ~> (stateT St (itree Void)) :=
     fun _ ev =>
       match ev with
       | Get _ => get_handle
       | Put _ s => put_handle s
       end.

   Definition interp_body_state_spec (A : Type) := (fun t1 : itree (fun H0 : Type => stateE St H0) A =>
     match observe t1 with
     | RetF r => retsi St (itree (fun H0 : Type => stateE St H0) A + A) (inr r)
     | TauF t2 => retsi St (itree (fun H0 : Type => stateE St H0) A + A) (inl t2)
     | @VisF _ _ _ X e k =>
         bindsi St X (itree (fun H0 : Type => stateE St H0) A + A) 
           (HandlerStateITree X e)
           (fun x : X => retsi St (itree (fun H0 : Type => stateE St H0) A + A) (inl (k x)))
     end) .

   Lemma sutt_to_eutt : forall A E (t1 t2 : itree E A), t1 ≅ t2 -> t1 ≈ t2.
   Proof.
     intros. rewrite H. reflexivity.
   Qed.

   Lemma interp_body_sutt : forall (A : Type) (t1 t2 : itree (stateE St) A),
       t1 ≅ t2 -> interp_body_state_spec A t1 ≈  interp_body_state_spec A t2.
   Proof.
     intros. constructor.
     - intros. unfold interp_body_state_spec in *.
       destruct (observe t1) eqn : ?Heq; destruct (observe t2) eqn : ?Heq.
       + specialize (itree_eta t1) as Ht1. specialize (itree_eta t2) as Ht2.
         rewrite Heq in Ht1. rewrite Heq0 in Ht2.
         enough (r = r0); subst; auto. apply sutt_to_eutt in Ht1. apply sutt_to_eutt in Ht2.
         rewrite H in Ht1. rewrite Ht1 in Ht2. basic_solve. auto.
       + (*contra case*) admit.
       + admit.
       + admit.
       + cbn. red. cbn in H0. red in H0.
         specialize (itree_eta t1). specialize (itree_eta t2). intros.
         rewrite Heq in H2. rewrite Heq0 in H1. 
         (*problem because t and t0 not equal, they are sutt, in reality p is the 
           lifting of a predicate over stateT itrees not itrees of that, need to 
           get that fact in somewhere*) admit.
       + admit.
       + admit.
       + admit.
       + destruct e; destruct e0.
         * cbn. red. cbn in H0. red in H0. unfold _retsi in *. basic_solve; auto.
           left. exists s. exists s. split ; try reflexivity. (*same issue as before*) admit.
         * admit.
         * admit.
         * cbn. red. cbn in H0. red in H0. unfold _retsi in *.
           basic_solve; auto.
           -- left. exists tt. exists s1. split; try reflexivity.
              (*same as before plus conclude that s0=s1 otherwise the trees not bisimilar*)
              admit.
           -- pinversion H0.
     - (*reformulate this lemma so that this symmetric case is not neccessary*) admit.
    Abort.

   (*need inversion principles for sutt*)
 
   (*think carefully about the vis cases, some form of refinement there
     is probably what you need for classes of interpretters, because in general only the
     first half of this proof will be possible*)



   Lemma interp_obs : forall (A : Type) (t : itree (stateE St) A ),
       InterpStateITreeSpec A t ≈ obs A (interp_state HandlerState t). 
   Proof.
     constructor.
     - cbn. red. intros. unfold _iter_fix in H. basic_solve.
       gen_dep2 t s. induction n; try contradiction. intros.
       cbn in H. destruct (observe t) eqn : ?Heq; simpl in *.
       + red in H. inversion H; basic_solve; basic_solve.
         specialize (itree_eta t) as H. rewrite Heq in H. basic_solve.
         eapply Hp; eauto. rewrite H. setoid_rewrite unfold_iter_ktree. simpl.
         repeat (setoid_rewrite bind_ret). simpl. reflexivity.
       + red in H. inversion H; basic_solve; basic_solve.
         * admit. (*not wf case*)
         * apply IHn. simpl in *. specialize (itree_eta t) as H.
           rewrite Heq in H. (*should be able to be refactored out to a lemma about iter on the same tree*) admit.



         * eapply Hp; eauto. (*needs some extra lemmas about iter on the same tree*) admit.
         * specialize (itree_eta t) as H. rewrite Heq in H. apply IHn.
           (*lemma about iter on the same tree*) admit.
       + destruct e.
         * simpl in *. unfold _bindsi in *. basic_solve.
           -- red in H0. basic_solve.
              ++ (*not_wf_case*) admit.
              ++ specialize (itree_eta t) as H. rewrite Heq in H.
                 apply IHn. simpl. (*iter on same tree plus how vis gets handdled*) admit.
           -- pinversion H.
         * simpl in *. unfold _bindsi in *. basic_solve; basic_solve.
           -- red in H0. basic_solve.
              ++ (*not_wf_case*) admit.
              ++ specialize (itree_eta t) as H. rewrite Heq in H.
                 apply IHn. (*iter on same tree plus how vis gets handled*)
                 (*the predicate probably is like give me an equiv for which if a equiv b
                   then g a equiv g b and forall a equiv b, iter g a equiv iter g b*) admit.
           -- pinversion H.
     - cbn. red. unfold _obssi. intros.
       match goal with | |- exists n, approx_iter_fix _ ?f _ _ _ _ => set f as g end.
       admit.
   Admitted.
              





  
    
    
