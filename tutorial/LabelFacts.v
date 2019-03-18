From ITree Require Import
     Basics.Basics
     Basics.Function
     ITree
     Basics.Category
     KTree
     KTreeFacts.

From Coq Require Import
     Psatz
     Vectors.Fin.

Require Import Program.Equality.

Require Import Label.

Section Label_Props.

  Import CatNotations.
  Local Open Scope cat_scope.
  Context {E: Type -> Type}.

  Lemma vanishing1_Label {A B} (f: Label A B) 
        (a : Fin.t A) :
    @loop_Label E A B 0 f a ≅ f a. 
  Proof.
    unfold loop_Label, loop.
    rewrite unfold_loop'; unfold loop_once, ITree.map. simpl.
    rewrite bind_bind. 
    rewrite <- (bind_ret2 (f a)) at 2.
    eapply eq_itree_bind; try reflexivity.
    intros; subst.
    rewrite bind_ret; reflexivity.
  Qed.

  Lemma vanishing_Label {A B: nat} (f: Label (0 + A) (0 + B)):
    @loop_Label E A B 0 f ⩯ unit_l' >>> f >>> unit_l.
  Proof.
    intros a.
    rewrite vanishing1_Label.
    unfold unit_l, UnitL_Coproduct, unit_l', UnitL'_Coproduct, case_, Case_Label, inr_, Inr_Label.
    unfold cat, Cat_Label, cat, Cat_ktree, ITree.cat, ITree.map, lift_ktree.
    simpl.
    rewrite bind_bind.
    rewrite bind_ret_.
    rewrite <- (bind_ret2 (f a)) at 1. 
    apply eutt_bind.
    - intros. reflexivity.
    - reflexivity.
  Qed.

  Lemma unit_l_ktree (A : nat) :
    unit_l ⩯ @lift_Label E (0 + A) A unit_l.
  Proof.
    reflexivity.
  Qed.

  Lemma unit_l'_Label (A : nat) :
    unit_l' ⩯ @lift_Label E A (0 + A) unit_l'.
  Proof.
    reflexivity.
  Qed.

  Lemma unit_r_Label (A : nat) :
    unit_r ⩯ @lift_Label E _ A unit_r.
  Proof.
    intros l.
    unfold unit_r.
    unfold lift_Label, Case_FinC, unit_l, UnitR_Coproduct, unit_l', UnitR'_Coproduct, case_, Case_Label, inr_, Inr_Label.
    destruct (split_fin_sum l).
    reflexivity.
    inv t.
  Qed.

  Lemma unit_r'_Label (A : nat) :
    unit_r' ⩯ @lift_Label E A (A + 0) unit_r'.
  Proof.
    reflexivity.
  Qed.

  Lemma case_l_Label {A B: nat} (ab: @Label E (0 + A) (0 + B)) :
    ab >>> unit_l ⩯ ab.
  Proof.
    rewrite unit_l_ktree.
    unfold lift_Label.
    simpl.
    unfold unit_l, UnitL_Coproduct, unit_l', UnitR'_Coproduct, case_, Case_Label, inr_, Inr_Label, Case_FinC,
    id_, Id_FinC.
    intros ?; simpl.
    unfold cat, Cat_Label, cat, Cat_ktree, ITree.cat.
    rewrite bind_ret2.
    reflexivity.
  Qed.

  Lemma case_l_Label' {A B: nat} (f: @Label E (0 + A) (0 + B)) :
    unit_l' >>> f ⩯ fun a => f a.
  Proof.
    rewrite unit_l'_Label.
    intro. unfold cat, Cat_Label, cat, Cat_ktree, ITree.cat, lift_Label.
    rewrite bind_ret_; reflexivity.
  Qed.

  Lemma case_r_Label' {A B: nat} (f: @Label E (A + 0) (B + 0)) :
    unit_r' >>> f ⩯ fun (a: t A) => f (L _ a).
  Proof.
    rewrite unit_r'_Label.
    intro. unfold lift_Label, cat, Cat_Label, cat, Cat_ktree, ITree.cat.
    rewrite bind_ret_; reflexivity.
  Qed.

  Lemma case_r_Label {A B: nat} (ab: @Label E A (B + 0)) :
    ab >>> unit_r ⩯ fun a => ITree.map unit_r (ab a).
  Proof.
    rewrite unit_r_Label.
    reflexivity.
  Qed.

  Lemma superposing1_Label {A B C D D'} (f : @Label E (C + A) (C + B))
        (g : @Label E D D') (a : t A) (d': t D') :
    ITree.map (L D') (loop_Label f a) ≅
              loop_Label
              (fun (cad: t (C + (A + D))) =>
                 match split_fin_sum cad with
                 | inl c => ITree.map (bimap id (L D')) (f (L _ c))
                 | inr ad => 
                   match split_fin_sum ad with
                   | inl a => ITree.map (bimap id (L D')) (f (R C a))
                   | inr d => ITree.map (R _ >>> R _)%cat (g d)
                   end
                 end) (L _ a).
  Proof.
    (*
    unfold loop_Label, loop.
    remember (inr a) as inra eqn:Hr.
    remember (inr (L D a)) as inla eqn:Hl.
    assert (Hlr : match inra with
                  | inl c => inl c
                  | inr a => inr (L D a)
                  end = inla).
    { subst; auto. }
    clear a Hl Hr.
    unfold ITree.map.
    pupto2_init. revert inla inra Hlr; pcofix self; intros.
    rewrite 2 unfold_loop'; unfold loop_once.
    rewrite bind_bind.
    destruct inra as [c | a]; subst.
    - rewrite bind_bind; setoid_rewrite bind_ret_.
      pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
      intros [c' | b]; simpl; intros; subst.
      + rewrite bind_tau. pfold; constructor.
        pupto2_final. auto.
      + rewrite bind_ret. pupto2_final; apply reflexivity.
    - rewrite bind_bind; setoid_rewrite bind_ret_.
      pupto2 eq_itree_clo_bind; econstructor; try reflexivity.
      intros [c' | b]; simpl; intros; subst.
      + rewrite bind_tau. pfold; constructor.
        pupto2_final. auto.
      + rewrite bind_ret_. pupto2_final; apply reflexivity.
     *)
  Admitted.

  Lemma bimap_Label_loop {I A B C D}
        (ab : @Label E (I + A) (I + B)) (cd : @Label E C D) :
    bimap (loop_Label ab) cd
          ⩯ loop_Label (assoc_l >>> bimap ab cd >>> assoc_r).
  Proof.
    (*
    (* rewrite assoc_l_ktree, assoc_r_ktree. *)
    (* rewrite lift_compose_ktree, compose_ktree_lift. *)
    unfold bimap, Bimap_Coproduct, cat, Cat_Label, cat, Cat_ktree, ITree.cat, case_, Case_Label, case_sum.
    unfold inl_, Inl_Label, inr_, Inr_Label.
    intros l; destruct (split_fin_sum l); simpl.
    - rewrite fold_map.
      rewrite (@superposing1_Label A B I C D).
      apply eutt_loop; try reflexivity.
      intros [|[]]; cbn.
      all: symmetry. (* protect the existential. *)
      all: rewrite fold_map.
      all: rewrite map_map.
      all: reflexivity.
    - unfold loop; rewrite unfold_loop.
      unfold loop_once; cbn.
      rewrite map_bind.
      rewrite bind_bind.
      apply eutt_bind; [ | reflexivity ].
      intros d.
      rewrite bind_ret; cbn.
      reflexivity.
     *)
  Admitted.

End Label_Props.      
