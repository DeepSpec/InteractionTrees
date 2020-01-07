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

(*could use yannick or Li Yao's help on this one, should be true but has been problematic
  to prove*)
Lemma not_wf_iter_spin : forall (A B : Type) (g : A -> itree Void (A + B) ) (a : A),
          not_wf_from A (fun a1 a2 => a1 =[ fun x => obs _ (g x) ]=> a2) a -> spin ≈ iter g a.
Proof.
  intros. generalize dependent a. pcofix CIH. intros. 
  pfold. punfold H0.
  - inversion H0. pclearbot. unfold spec_iter_arrow_rel in Hrel. cbn in Hrel. red in Hrel.
    specialize (unfold_iter_ktree g a) as Hiter. apply strong_to_weak_bisim in Hiter as Hiter'.
    rewrite Hrel in Hiter'. setoid_rewrite bind_ret in Hiter'. 
    destruct (observe (@spin Void B)) eqn : Heq; try discriminate.
    red. rewrite Heq. 
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree, ITree.iter.
    specialize (itree_eta (KTree.iter g a) ) as H. rewrite Hiter in H. simpl in H.
    admit.
  - admit.
Admitted.

Lemma iter_morph : forall (A B : Type) (g : A -> itree Void (A + B) ) (a : A),
      obs _ (iter g a) ≈ iter_fix (fun x => obs _ (g x) ) a.
Proof.
  constructor.
  - intros. cbn in H. red in H. cbn.
    (*need some notion of number of unfolds or extern div, that should be doable, *)
    admit.
  - intros. cbn. red. cbn in H. red in H. basic_solve. generalize dependent a. induction n; try contradiction.
    intros. cbn in H.  red in H. inversion H; eauto. 
    + eapply Hp with (t1 := ret b); auto. setoid_rewrite unfold_iter_ktree.
      rewrite Hretb. setoid_rewrite bind_ret. reflexivity.
    + eapply Hp with (t1 := spin); auto. setoid_rewrite unfold_iter_ktree.
      apply div_spin_eutt in Hdiv. rewrite Hdiv. apply spin_bind.
    + apply Hp with (t1 := spin); auto. apply not_wf_iter_spin.
      pfold. apply not_wf with (a' := a0); eauto.
    + apply Hp with (t1 := KTree.iter g a0); auto.
      setoid_rewrite unfold_iter_ktree with (a1 := a). rewrite Hreta. setoid_rewrite bind_ret.
      rewrite tau_eutt. reflexivity.
Admitted.


(*is a relation R well founded from point x*)
(*make iter inductive, add the option R is not well founded from x*)
