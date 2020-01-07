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
     Dijkstra.PureITreeDijkstra
     Dijkstra.IterRel
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma equiv_resp_eutt : forall A B (a : A), resp_eutt Void _ (fun t : itree Void (A + B) => t ≈ ret (inl a) ).
Proof.
  intros. intros t1 t2 H. split; intros.
  - rewrite <- H. auto.
  - rewrite H. auto.
Qed.

Definition spec_iter_arrow_rel {A B : Type} (f : A -> PureITreeSpec (A + B) ) (a1 a2: A) : Prop :=
  proj1_sig (f a1) (fun t => t ≈ ret (inl a2)) (equiv_resp_eutt A B a2).

Notation "x =[ f ]=> y" := (spec_iter_arrow_rel f x y) (at level 80).

Lemma obs_arrow_rel_det : forall A B (f : A -> itree Void (A + B) ) (a1 a2 a3: A), 
  a1 =[ fun x => obs _ (f x) ]=> a2 -> a1 =[ fun x => obs _ (f x) ]=> a3 -> a2 = a3.
Proof.
  intros. unfold spec_iter_arrow_rel in *.
  cbn in *. red in H. red in H0. rewrite H in H0. apply inv_ret in H0. injection H0. auto.
Qed.
(*
Section IterInd.

  Context (A B : Type).
  Context (g : A -> (itree Void ( A + B) -> Prop) -> Prop  ).

 
                                    

  Inductive iter_ind  (p : itree Void B -> Prop) : A -> Prop :=
    con (a : A) : g a (fun t : itree Void (A + B) => exists a' : A, 
                               (t ≈ ret (inl a')) /\ iter_ind p a') ->
  iter_ind p a.

End IterInd.
*)


Variant iter_bodyF {A B : Type} (g : A -> PureITreeSpec (A + B) )
        (p : itree Void B -> Prop) (Hp : resp_eutt _ _ p)
        (F : A -> Prop)
        (t : itree Void (A + B) ) : Prop := 
  | term_b (b : B) (Hretb : t ≈ ret (inr b) ) (Hb : p (ret b))
  | intern_div (Hdiv : divergence t) (Hspin : p spin)
  | extern_div (a : A) (Hreta : t ≈ ret (inl a)) (Hnwf : not_wf_from _ (fun a1 a2 => a1 =[ g ]=> a2) a  ) (Hspin : p spin)
  | cont_a (a : A) (Hreta : t ≈ ret (inl a)) (Hrec : F a)
.
Hint Constructors iter_bodyF.

Lemma iter_bodyF_resp_eutt : forall A B (g : A -> PureITreeSpec (A + B)) p Hp F,
    resp_eutt _ _ (iter_bodyF g p Hp F).
Proof.
  intros. intros t1 t2 H. split; intros; destruct H0; eauto.
  - rewrite H in Hretb. eauto.
  - rewrite H in Hdiv. eauto.
  - rewrite H in Hreta. eauto.
  - rewrite H in Hreta. eauto.
  - rewrite <- H in Hretb. eauto.
  - rewrite <- H in Hdiv. eauto.
  - rewrite <- H in Hreta. eauto.
  - rewrite <- H in Hreta. eauto.
Qed.

Fixpoint approx_iter_fix {A B :Type}  (n : nat) (g : A -> PureITreeSpec (A+ B) ) (a : A) 
          (p : itree Void B -> Prop) (Hp : resp_eutt _ _ p) : Prop :=
  match n with | 0 => False
               | S m => proj1_sig (g a) (iter_bodyF g p Hp (fun a' => approx_iter_fix m g a' p Hp))
                                  (iter_bodyF_resp_eutt A B g p Hp (fun a' => approx_iter_fix m g a' p Hp) ) end.

Definition _iter_fix {A B : Type}  (g : A -> PureITreeSpec (A+ B) ) (a : A) 
          (p : itree Void B -> Prop) (Hp : resp_eutt _ _ p) : Prop := exists n, approx_iter_fix n g a p Hp.

(*
Inductive iter_ind {A B : Type} (g : A -> PureITreeSpec (A+ B) ) (a : A) 
          (p : itree Void B -> Prop) (Hp : resp_eutt _ _ p) : Prop :=
  | con : proj1_sig (g a) (iter_bodyF g p Hp (fun a' => iter_ind g a' p Hp) ) 
                    (iter_bodyF_resp_eutt A B g p Hp (fun a' => iter_ind g a' p Hp) ) ->
          iter_ind g a p Hp
. *)

Ltac gen_dep2 a s := generalize dependent a; generalize dependent s.

Ltac dest_dep f a := destruct (f a) as [?fa ?Hfa] eqn : ?Heq; simpl in *.


Lemma iter_fix_monot_aux : forall (A B : Type) n (g : A -> PureITreeSpec (A + B) ) a (p p' : itree Void B -> Prop) Hp Hp', 
    (forall t, p t -> p' t) -> approx_iter_fix n g a p Hp -> approx_iter_fix n g a p' Hp'.
Proof.
  intros. generalize dependent a. induction n; try contradiction.
  cbn. intros. dest_dep g a. eapply Hfa; try apply H0. intros t Ht. inversion Ht; eauto.
Qed.

Definition iter_fix_n {A B : Type} (n : nat)  
           (g :  A -> PureITreeSpec (A + B) ) (a : A) : PureITreeSpec B :=
  exist _ (approx_iter_fix n g a) (iter_fix_monot_aux A B n g a).

Lemma iter_fix_monot : forall A B (g :  A -> PureITreeSpec (A + B) ) (a : A),
                              monotonici B ( _iter_fix g a).
Proof.
  intros. intro. intros.
  unfold  _iter_fix in H0. 
  destruct H0 as [n Hiter]. apply iter_fix_monot_aux with (p' := p') (Hp' := Hp') in Hiter; auto.
  exists n. auto.
Qed.

Definition iter_fix {A B : Type}  (g :  A -> PureITreeSpec (A + B) ) (a : A) : PureITreeSpec B :=
  exist _ ( _iter_fix g a ) (iter_fix_monot A B g a).

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
                   | H : iterF_body _ _ _ _ |- _ => inversion H; clear H; subst
                   | H : exists a : ?A, _ |- _ => destruct H as [?a ?H]
                   | x : ?A + ?B |- _ => destruct x as [?a | ?b]
                   | H : upaco1 _ _ _ |- _ => pclearbot
           end.

  Ltac invert_ret := simpl in *; match goal with | H : Ret ?a ≈ Ret ?b |- _ => 
                                                   apply inv_ret in H; try discriminate; try (injection H as H);
                                                   subst end.


  Ltac basic_solve := invert_evidence; try clear_ret_eutt_spin; try invert_ret.

Lemma strong_to_weak_bisim : forall E A (t1 t2 : itree E A),
      t1 ≅ t2 -> t1 ≈ t2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma observe_eutt_spin : forall E A (t : itree E A), t ≈ spin -> exists t0, observe t = TauF t0 /\ t0 ≈ spin.
Proof.
  intros. destruct (observe t) eqn : Heq; try discriminate.
  - specialize (itree_eta t) as Heta. rewrite Heq in Heta. rewrite Heta in H. pinversion H. 
    destruct (observe spin) eqn : ?Heq; try discriminate. admit.
  - exists t0. split; auto. specialize (itree_eta t) as H0. rewrite Heq in H0. rewrite H0 in H.
    rewrite tau_eutt in H. auto.
  - specialize (itree_eta t) as Heta. rewrite Heq in Heta. rewrite Heta in H. exfalso. clear Heq Heta.
    admit.
Admitted.

(*could use yannick or Li Yao's help on this one, should be true but has been problematic
  to prove*)
Lemma not_wf_iter_spin : forall (A B : Type) (g : A -> itree Void (A + B) ) (a : A),
          not_wf_from A (fun a1 a2 => a1 =[ fun x => obs _ (g x) ]=> a2) a -> spin ≈ iter g a.
Proof.
  intros. unfold spec_iter_arrow_rel in H. cbn in H. unfold _obsip in H. 
  remember spin as t. rewrite Heqt. rewrite <- Heqt. assert (t ≈ spin). { rewrite Heqt. reflexivity. }
  clear Heqt. gen_dep2 a t.
  pcofix CIH. intros t Ht a Hwfa. 
  pfold. punfold Hwfa; try apply not_wf_F_mono'.
  inversion Hwfa. pclearbot.
  specialize (unfold_iter_ktree g a) as Hiter. apply strong_to_weak_bisim in Hiter as Hiter'.
  rewrite Hrel in Hiter'. setoid_rewrite bind_ret in Hiter'. 
  apply observe_eutt_spin in  Ht as Ht0. basic_solve. red. rewrite H.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree, ITree.iter. unfold observe.
  cbn. destruct (observe (g a) ) eqn : ?Heq; simpl; basic_solve.
  - simpl. constructor; auto. right. apply CIH; auto.
    specialize (itree_eta (g a) ) as Hga. rewrite Heq in Hga. rewrite Hga in Hrel. basic_solve. auto.
  - exfalso. specialize (itree_eta (g a)) as Hga. rewrite Heq in Hga. rewrite Hga in Hrel. basic_solve.
  - constructor. specialize (itree_eta (g a)) as Hga. rewrite Heq in Hga. rewrite Hga in Hiter. 

Admitted.

Lemma iter_morph_aux_l : forall (A B : Type) (g : A -> itree Void (A + B) ) (a : A) (p : itree Void B -> Prop)
                                (Hp : resp_eutt _ _ p),  p (KTree.iter g a) -> _iter_fix (fun x => obs _ (g x) ) a p Hp.
Proof.
  intros. set (fun a1 a2 => a1 =[ fun x => obs _ (g x) ]=> a2) as rg.
  destruct (classic (not_wf_from _ rg a) ).
  - apply not_wf_iter_spin in H0 as Heutt. 
    punfold H0; try apply not_wf_F_mono'. destruct H0. pclearbot. unfold rg in Hrel. unfold spec_iter_arrow_rel in Hrel.
    cbn in Hrel. red in Hrel.
    red. exists 1. simpl. red. eapply extern_div; eauto; auto. eapply Hp; eauto.
  - specialize neg_wf_from_not_wf_from as Hn. specialize (Hn A rg). 
    assert (wf_from A rg a).
    { specialize (Hn a). destruct (classic (wf_from A rg a)); tauto. }
    clear Hn H0.
    induction H1.
    + unfold rg in H0. destruct (eutt_reta_or_div _ (g a) ); basic_solve.
      * rename a0 into a'. specialize (H0 a'). exfalso. apply H0. unfold spec_iter_arrow_rel.
        cbn. red. symmetry. eauto.
      * exists 1. cbn. red. symmetry in H1. eapply term_b; eauto.
        eapply Hp; eauto. setoid_rewrite unfold_iter_ktree. rewrite H1. setoid_rewrite bind_ret. reflexivity.
      * exists 1. cbn. red. eapply intern_div; eauto. apply div_spin_eutt in H1. eapply Hp; eauto.
        setoid_rewrite unfold_iter_ktree. rewrite H1. apply spin_bind.
    + destruct (eutt_reta_or_div _ (g a) ); basic_solve.
      * rename a0 into a'. symmetry in H2. specialize (H1 a').
        assert (rg a a').
        { unfold rg. unfold spec_iter_arrow_rel. cbn. red. auto. }
        assert (p (KTree.iter g a')).
        { eapply Hp; eauto. setoid_rewrite  unfold_iter_ktree. rewrite H2.
          setoid_rewrite <- unfold_iter_ktree. setoid_rewrite bind_ret. rewrite tau_eutt. reflexivity. }
        specialize (H1 H3 H4). red in H1. basic_solve. exists (S n). cbn. red. eapply cont_a; eauto.
      * exists 1. cbn. red. symmetry in H2. eapply term_b; eauto.
        eapply Hp; eauto. setoid_rewrite unfold_iter_ktree. rewrite H2. setoid_rewrite bind_ret. reflexivity.
      * exists 1. cbn. red. eapply intern_div; eauto. apply div_spin_eutt in H2. eapply Hp; eauto.
        setoid_rewrite unfold_iter_ktree. rewrite H2. apply spin_bind.
Qed.



Lemma iter_morph : forall (A B : Type) (g : A -> itree Void (A + B) ) (a : A),
      obs _ (iter g a) ≈ iter_fix (fun x => obs _ (g x) ) a.
Proof.
  constructor.
  - intros. cbn in H. red in H. cbn. apply iter_morph_aux_l. auto.
  - intros. cbn. red. cbn in H. red in H. basic_solve. generalize dependent a. induction n; try contradiction.
    intros. cbn in H.  red in H. inversion H; eauto; clear H.
    + eapply Hp with (t1 := ret b); auto. setoid_rewrite unfold_iter_ktree.
      rewrite Hretb. setoid_rewrite bind_ret. reflexivity.
    + eapply Hp with (t1 := spin); auto. setoid_rewrite unfold_iter_ktree.
      apply div_spin_eutt in Hdiv. rewrite Hdiv. apply spin_bind.
    + apply Hp with (t1 := spin); auto. apply not_wf_iter_spin.
      pfold. apply not_wf with (a' := a0); eauto.
    + apply Hp with (t1 := KTree.iter g a0); auto.
      setoid_rewrite unfold_iter_ktree with (a1 := a). rewrite Hreta. setoid_rewrite bind_ret.
      rewrite tau_eutt. reflexivity.
Qed.


Instance PureITreeIter :  Iter (Kleisli PureITreeSpec) sum := @iter_fix.

Ltac unf_bindg := unfold bindpi, _bindpi.

Ltac unf_bind H := unfold bindpi, _bindpi in H.

Lemma itree_spec_iter_unfold_aux_l : forall A B (g : A -> PureITreeSpec (A + B) ) a n p Hp,
    proj1_sig (iter_fix_n n g a) p Hp -> proj1_sig (cat g (case_ (iter_fix_n n g) (id_ B)) a) p Hp.
Proof.
  intros. generalize dependent a. induction n; try contradiction; intros.
  cbn. unf_bindg. cbn in H. dest_dep g a. eapply Hfa; eauto. intros ?t ?Ht. inversion Ht; clear Ht; auto.
  - left. exists (inr b). split; auto. symmetry. auto.
  - punfold Hnwf; try apply not_wf_F_mono'. destruct Hnwf. unfold spec_iter_arrow_rel in Hrel. 
    left. exists (inl a0). symmetry in Hreta. split; auto. cbn. pclearbot. dest_dep g a0.
    eapply Hfa0; try apply Hrel. intros ?t ?Ht. simpl in *. eapply extern_div; eauto. auto.
  -  specialize (IHn a0 Hrec) as IHn'. symmetry in Hreta. left. exists (inl a0). split; auto. cbn.
     cbn in IHn'. unf_bind IHn'. dest_dep g a0. eapply Hfa0; try apply IHn'. intros ?t ?Ht. simpl in *.
     basic_solve; eauto.
     + cbn in H1. specialize (IHn a1 H1). eapply cont_a; eauto. symmetry. eauto.
     + symmetry in H0. cbn in H1. red in H1. unfold id in *. eapply term_b; eauto. auto.
Qed.

Lemma itree_spec_iter_unfold_aux_r : forall A B (g : A -> PureITreeSpec (A + B) ) a n p Hp,
    proj1_sig (cat g (case_ (iter_fix_n n g) (id_ B)) a) p Hp -> proj1_sig (iter_fix_n (S n) g a) p Hp.
Proof.
  intros. generalize dependent a. induction n; intros.
  - cbn in H. unf_bind H. cbn. dest_dep g a. eapply Hfa; try apply H. intros ?t ?Ht.
    simpl in *. basic_solve; eauto; try contradiction.
    cbn in H1. red in H1. unfold id in *. symmetry in H0. eapply term_b; eauto. auto.
  - cbn in H. unf_bind H. cbn. dest_dep g a. eapply Hfa; try apply H. intros ?t ?Ht.
    simpl in *. basic_solve; eauto.
    + symmetry in H0. eapply cont_a; try apply H0. auto.
    + symmetry in H0. eapply term_b; try apply H0. auto.
Qed.


Instance PureITreeIterUnfold :  IterUnfold  (Kleisli PureITreeSpec) sum.
Proof.
  intros A B g.
  constructor.
  - specialize ( itree_spec_iter_unfold_aux_l A B g a) as H. cbn in H. cbn. intros. red in H0. basic_solve.
    specialize (H n p Hp H0). unf_bindg. unf_bind H. dest_dep g a. eapply Hfa; try apply H. intros ?t ?Ht.
    simpl in *. basic_solve; eauto. cbn in H2. left. exists (inl a0). split; auto. cbn.
    exists n. auto.
  - specialize  ( itree_spec_iter_unfold_aux_r A B g a) as H. cbn in H. cbn. intros. red.
    unf_bind H0. dest_dep g a. 
Admitted.


(*is a relation R well founded from point x*)
(*make iter inductive, add the option R is not well founded from x*)
