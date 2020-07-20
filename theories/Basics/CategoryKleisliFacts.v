(** Proofs that the Kleisli category of a monad is in fact a category. *)

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.Basics
     Basics.Typ
     Basics.HeterogeneousRelations
     Basics.Category
     Basics.Monad
     Basics.CategoryMonad
     Basics.CategoryFunctor
     Basics.CategoryKleisli
     Basics.Function.

Import CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.


Section BasicFacts.

  Context {m : typ -> typ}.
  Context {m_Monad : Monad typ_proper m}.
  Context {EqmRm : EqmR m}.
  Context {EqmROKm : EqmR_OK m}.
  Context {ML : EqmRMonad m}.

  Instance Proper_Kleisli_apply {a b} :
    Proper (eq2 ==> eq ==> equalE (m b)) (@Kleisli_apply m a b).
  Proof.
    repeat intro.
    unfold Kleisli_apply. rewrite H0. apply eqmR_equal. apply H.
  Qed.

  Lemma fold_Kleisli {a b} (f : Kleisli m a b) (x : a) :
    f @ x = Kleisli_apply f x.
  Proof. reflexivity. Qed.

  Global Instance Equivalence_Kleisli_eq2 {a b} : @Equivalence (Kleisli m a b) eq2.
  Proof.
    split; repeat intro.
    - apply eqmR_equal. cbn. reflexivity.
    - red. rewrite H. eapply eqmR_equal. cbn. reflexivity.
    - red. rewrite H. rewrite H0. eapply eqmR_equal. cbn. reflexivity.
  Qed.

  Global Instance Functor_pure
    : Functor arrow_typ (Kleisli m) (fun x => x) (@pure m _ _ _).
  Proof.
    constructor; intros.
    - unfold Fmap_Id. intro. reflexivity.
    - unfold Fmap_Cat. repeat intro.
      apply eqmR_equal; cbn.
      unfold pure, pure_, cat_. cbn.
      destruct g, f. cbn.
      rewrite eqmR_bind_ret_l. cbn. reflexivity.
    - intros ? ? ? ? ?. unfold pure. intro.
      apply eqmR_equal. cbn. unfold pure_. rewrite H.
      reflexivity.
  Qed.

(* This is subsumed by [category_proper_cat] and the [Category]
   instance for Kleisli.
   Adding this as an instance (i.e., marking this as [Global]) would confuse
   typeclass search, as it would often be picked for categories whose arrow
   types are definitionally equal to some [Kleisli m a b]
   (e.g., [sub (Kleisli m) f]), which puts the rest of the search in the wrong
   category.
 *)
Instance Proper_cat_Kleisli {a b c}
  : @Proper (Kleisli m a b -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) cat.
Proof.
  repeat intro.
  unfold cat, Cat_Kleisli.
  eapply eqmR_bind_ProperH; eauto.
  apply H. intros. cbn in *.
  repeat red in H0.
  rewrite H2. apply H0.
  intros. cbn in H2. rewrite H2. rewrite H0.
  apply eqmR_equal; cbn; reflexivity.
Qed.

Local Opaque bind ret eqm.

Typeclasses eauto := 5.

Program Definition case_typ_proper'
  {A B C : typ} (f : A -=-> m C) (g : B -=-> m C) : (A ⨥ B) -=-> m C :=
    (fun (x : A ⨥ B) =>
      match x with
      | inl a => f @ a
      | inr b => g @ b
      end).
Next Obligation.
  repeat red.
  intros x y.
  destruct C; destruct x; destruct y; cbn in *; try tauto.
  - intros. destruct f. cbn. apply p. assumption.
  - intros. destruct g. cbn. apply p. assumption.
Qed.

Instance sum_assocL : AssocL (Kleisli m) sum_typ :=
  AssocL_Coproduct (Kleisli m) _ sum_typ (@case_typ_proper') _ _.

Instance sum_assocL_typ : AssocL typ_proper sum_typ :=
  AssocL_Coproduct typ_proper _ sum_typ (@case_typ_proper) (@inl_typ_proper) (@inr_typ_proper).

Instance sum_assocR : AssocR (Kleisli m) sum_typ :=
  AssocR_Coproduct (Kleisli m) _ sum_typ (@case_typ_proper') _ _.

Instance sum_assocR_typ : AssocR typ_proper sum_typ :=
  AssocR_Coproduct typ_proper _ sum_typ (@case_typ_proper) (@inl_typ_proper) (@inr_typ_proper).

Lemma pure_assoc_l {a b c : typ}
  : assoc_l (C := Kleisli m) (bif := sum_typ)
  ⩯ pure (m := m) (a := a ⨥ (b ⨥ c))%type assoc_l.
Proof.
  intros x.
  destruct x as [ | []]; red; cbn;
    unfold assoc_l, pure, inl_, sum_assocL, AssocL_Coproduct, case_,
    case_typ_proper, case_typ_proper', inl_; cbn;
    unfold Inl_Kleisli, inl_typ_proper, pure, pure_, cat_, sum_assocL_typ; cbn.
  - setoid_rewrite eqmR_bind_ret_l. cbn.
    match goal with
    | |- eqm @ (?l, _) => remember l as l'
    end.
    (* IY : Ltac question---here, I'm not sure how to get the type of
     [(a ⨥ b) ⨥ c] using a match. *)
    change (eqmR ((a ⨥ b) ⨥ c) @ (l', l')).
    apply eqmR_equal.
    cbn; reflexivity.
  - setoid_rewrite eqmR_bind_ret_l. cbn.
    match goal with
    | |- eqm @ (?l, _) => remember l as l'
    end.
    change (eqmR ((a ⨥ b) ⨥ c) @ (l', l')).
    apply eqmR_equal.
    cbn; reflexivity.
  - match goal with
    | |- eqm @ (?l, _) => remember l as l'
    end.
    change (eqmR ((a ⨥ b) ⨥ c) @ (l', l')).
    apply eqmR_equal.
    cbn; reflexivity.
Qed.

Lemma pure_assoc_r {a b c : typ} :
  (@assoc_r _ (Kleisli m) sum_typ _ _ _ _) ⩯ (@pure m _ _ _ ((a ⨥ b) ⨥ c)%type _ assoc_r).
Proof.
  intros x.
  destruct x as [ [] | ]; red; cbn;
    unfold assoc_r, pure, inr_, sum_assocR, AssocR_Coproduct, case_,
    case_typ_proper, case_typ_proper', inr_; cbn;
    unfold Inr_Kleisli, inr_typ_proper, pure, pure_, cat_, sum_assocR_typ; cbn.
  - match goal with
    | |- eqm @ (?l, _) => remember l as l'
    end.
    change (eqmR (a ⨥ (b ⨥ c)) @ (l', l')).
    apply eqmR_equal.
    cbn; reflexivity.
  - setoid_rewrite eqmR_bind_ret_l. cbn.
    match goal with
    | |- eqm @ (?l, _) => remember l as l'
    end.
    change (eqmR (a ⨥ (b ⨥ c)) @ (l', l')).
    apply eqmR_equal.
    cbn; reflexivity.
  - setoid_rewrite eqmR_bind_ret_l. cbn.
    match goal with
    | |- eqm @ (?l, _) => remember l as l'
    end.
    change (eqmR (a ⨥ (b ⨥ c)) @ (l', l')).
    apply eqmR_equal.
    cbn; reflexivity.
Qed.


Arguments catK {_ _ _ _ _}.
Arguments cat_ {_ _ _ _ _}.
Global Instance CatAssoc_Kleisli : CatAssoc (Kleisli m).
Proof.
  red.
  (* f >>> g >>> h ⩯ f >>> (g >>> h). *)
  intros a b c d f g h.
  unfold cat, Cat_Kleisli, eq2, Eq2_Kleisli, pointwise_relation.
  intros x. cbn. unfold catK, cat_. cbn.
  red.
  match goal with
  | |- eqm @ (?l, ?r) => remember l as l'; remember r as r'
  end.
  change (eqmR d @ (l', r')).
  subst.
  apply eqmR_equal.
  pose proof eqmR_bind_bind.
  specialize (H m EqmRm m_Monad ML b c d (f @ x) g h).
  unfold cat, Cat_Kleisli, cat_typ_proper in H. cbn in H.
  unfold cat, Cat_Fun in H. rewrite H. cbn.
  apply eqmR_equal.
  eapply eqmR_bind_ProperH; eauto.
  Unshelve.
  apply eqmR_equal; cbn. reflexivity.
  intros. cbn.
  apply eqmR_equal. cbn.  rewrite H1. cbn. reflexivity.
  intros. apply eqmR_equal. cbn. rewrite H1. cbn. reflexivity.
Qed.

(** *** [id_ktree] respect identity laws *)
Global Instance CatIdL_Kleisli : CatIdL (Kleisli m).
Proof.
  intros A B f a; unfold cat, Cat_Kleisli, id_, Id_Kleisli, pure.
  cbn. red. unfold cat_, pure_, id_. cbn.
  rewrite eqmR_bind_ret_l. change (eqmR B @ (f @ a, (` f) a)).
  apply eqmR_equal. cbn. reflexivity.
Qed.

Ltac eqm_to_eqmR x :=
  match goal with
  | |- eqm @ (?l, ?r) => change (eqmR x @ (l, r))
  end
.

Global Instance CatIdR_Kleisli : CatIdR (Kleisli m).
Proof.
  intros A B f a.
  (* f >>> id_ B ⩯ f *)
  unfold cat, Cat_Kleisli, Id_Kleisli, pure.
  cbn. red. unfold cat_, pure_.
  eqm_to_eqmR B.
  apply eqmR_equal; cbn.
  pose proof eqmR_bind_ret_r.
  specialize (H m _ _ _ _ _ (f @ a)).
  unfold typ_proper_app in H at 3.
  rewrite <- H.
  apply eqmR_equal. eapply eqmR_bind_ProperH; eauto.
  apply eqmR_equal; cbn; reflexivity.
  intros.
  eapply eqmR_equal. cbn. rewrite H1. reflexivity.
  intros. cbn. rewrite H1. apply eqmR_equal. cbn; reflexivity.
Qed.

Global Instance Category_Kleisli : Category (Kleisli m).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance InitialObject_Kleisli : InitialObject (Kleisli m) bot_typ.
Proof. intros A f []. Qed.


Global Instance Case_Kleisli : Case (Kleisli m) sum_typ.
Proof.
  intros a b c f g.
  refine (-=->! (fun p =>
                   match p with
                   | inl x => f @ x
                   | inr x => g @ x
                   end
                ) _).
  cbn. repeat intro.
  destruct x, y; try destruct H; rewrite H; reflexivity.
Defined.

Global Instance Proper_case_Kleisli {a b c}
  : @Proper (Kleisli m a c -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro; destruct (_ : _ + _); cbn; auto;
    [rewrite H | rewrite H0]; red; eqm_to_eqmR c;
      apply eqmR_equal; cbn; reflexivity.
Qed.

(** *** [pure] is well-behaved *)

(* SAZ: not sure about the naming conventions here. *)

Global Instance Proper_pure {A B} :
  Proper (eq2 ==> eq2) (@pure _ _ _ _ A B).
Proof.
  repeat intro.
  unfold pure. cbn.
  red. eqm_to_eqmR B; apply eqmR_equal; cbn.
  unfold pure_. rewrite H. reflexivity.
Qed.

Lemma pure_id {A: typ}: (id_ A ⩯ @pure _ _ _ _ A A (id_ A))%cat.
Proof.
  reflexivity.
Qed.

Fact compose_pure {A B C} (ab : A -=-> B) (bc : B -=-> C) :
  (pure ab >>> pure bc ⩯ pure (ab >>> bc))%cat.
Proof.
  intros a.
  unfold pure, cat, Cat_Kleisli. cbn; red.
  eqm_to_eqmR C; apply eqmR_equal; cbn.
  unfold cat_, pure_. cbn.
  rewrite eqmR_bind_ret_l. cbn. reflexivity.
Qed.

Fact compose_pure_l {A B C D} (f: A -=-> B) (g: B -=-> C) (k: Kleisli m C D) :
  (pure f >>> (pure g >>> k) ⩯ pure (f >>> g) >>> k)%cat.
Proof.
  rewrite <- cat_assoc.
  rewrite compose_pure.
  reflexivity.
Qed.

Fact compose_pure_r {A B C D} (f: B -=-> C) (g: C -=-> D) (k: Kleisli m A B) :
  ((k >>> pure f) >>> pure g ⩯ k >>> pure (f >>> g))%cat.
Proof.
  rewrite cat_assoc.
  rewrite compose_pure.
  reflexivity.
Qed.

Fact pure_cat {A B C : typ}:
  forall (f: A -=-> B) (bc: Kleisli m B C)
    (p : Proper (equalE A ==> equalE (m C)) (fun a : A => bc @ (f @ a))),
    pure f >>> bc ⩯ -=->! (fun a => bc @ (f @ a)) p.
Proof.
  intros. intro a.
  unfold pure, pure, cat, Cat_Kleisli. cbn.
  red.
  eqm_to_eqmR C ; apply eqmR_equal; cbn.
  unfold cat_, pure_. cbn.
  rewrite eqmR_bind_ret_l. reflexivity.
Qed.


Fact cat_pure {A B C}: forall (ab: Kleisli m A B) (g:B -=-> C),
    (ab >>> pure g)
  ⩯ (map g ab).
Proof.
  reflexivity.
Qed.

Global Instance Swap_typ_proper : Swap typ_proper sum_typ.
Proof.
  repeat intro.
  refine (-=->! (fun p => match p with
                       | inl x => inr x
                       | inr x => inl x
                       end
                ) _).
  repeat intro.
  destruct x, y; try inversion H;
    destruct a; destruct b; cbn in *; apply H.
Defined.

Lemma pure_swap {A B}:
  @pure _ _ _ _ (A ⨥ B) _ swap ⩯ swap.
Proof.
  intros []. cbn; red.
  eqm_to_eqmR (B ⨥ A). apply eqmR_equal. cbn.
  unfold pure_, inr_typ_proper. reflexivity.
  cbn.
  red. eqm_to_eqmR (B ⨥ A). apply eqmR_equal; cbn.
  unfold pure_, inr_typ_proper. reflexivity.
Qed.

Lemma pure_inl {A B}
  : pure (b := A ⨥ B) inl_ ⩯ inl_.
Proof. reflexivity. Qed.

Lemma pure_inr {A B}
  : pure (b := A ⨥ B) inr_ ⩯ inr_.
Proof. reflexivity. Qed.


Lemma case_pure {A B C} (ac : A -=-> C) (bc : B -=-> C) :
    case_ (pure ac) (pure bc)
  ⩯ pure (@case_ _ typ_proper sum_typ _ _ _ _ ac bc).
Proof.
  intros [].
  cbn; red.
  eqm_to_eqmR C. apply eqmR_equal; cbn.
  unfold pure_, case_. cbn; reflexivity.
  cbn; red.
  eqm_to_eqmR C. apply eqmR_equal; cbn.
  unfold pure_, case_. cbn; reflexivity.
Qed.

(* (** *** [Unitors] lemmas *) *)

(* This is probably generalizable into [Basics.Category]. *)

Lemma unit_l_pure (A : typ) :
  unit_l ⩯ @pure _ _ _ _ (bot_typ ⨥ A) A unit_l.
Proof.
  intros [[]|]. cbn; red.
  eqm_to_eqmR A; apply eqmR_equal; cbn.
  unfold pure_, unit_l. cbn; reflexivity.
Qed.

Lemma unit_l'_pure (A : typ) :
  unit_l' ⩯ @pure _ _ _ _ A (bot_typ ⨥ A) unit_l'.
Proof.
  intro. cbn; red. eqm_to_eqmR (bot_typ ⨥ A); apply eqmR_equal; cbn.
  unfold pure_, unit_l'. cbn; reflexivity.
Qed.

Lemma unit_r_pure (A : typ) :
  unit_r ⩯ @pure _ _ _ _ (A ⨥ bot_typ) A unit_r.
Proof.
  intros [|[]].
  cbn; red. eqm_to_eqmR A; apply eqmR_equal; cbn.
  unfold pure_, unit_l'. cbn; reflexivity.
Qed.

Lemma unit_r'_pure (A : typ) :
  unit_r' ⩯ @pure _ _ _ _ A (A ⨥ bot_typ) unit_r'.
Proof.
  intro.
  cbn; red. eqm_to_eqmR (A ⨥ bot_typ); apply eqmR_equal; cbn.
  unfold pure_, unit_l'. cbn; reflexivity.
Qed.

(* SAZ: was named "case_l_ktree" *)
Lemma case_l {A B: typ} (ab: Kleisli m A (bot_typ ⨥ B)) :
  ab >>> unit_l ⩯ map unit_l ab.
Proof.
  rewrite unit_l_pure. intro.
  cbn; red. eqm_to_eqmR B; apply eqmR_equal; cbn.
  unfold pure_, unit_l'. cbn; reflexivity.
Qed.

(* SAZ: was named "case_l'_ktree" *)
Lemma case_l' {A B: typ} (f: Kleisli m (bot_typ ⨥ A) (bot_typ ⨥ B)) :
  forall (p : Proper (equalE A ==> equalE (m (bot_typ ⨥ B))) (fun a : A => f @ inr a)),
  unit_l' >>> f ⩯ -=->! (fun a => f @ (inr a)) p.
Proof.
  intros.
  rewrite unit_l'_pure.
  intro. unfold cat, Cat_Kleisli, pure.
  cbn; red. eqm_to_eqmR (bot_typ ⨥ B); apply eqmR_equal; cbn.
  unfold cat_, pure_. cbn.
  rewrite eqmR_bind_ret_l; reflexivity.
Qed.


Lemma case_r {A B: typ} (ab: Kleisli m A (B ⨥ bot_typ)) :
  ab >>> unit_r ⩯ map unit_r ab.
Proof.
  rewrite unit_r_pure.
  intro.
  cbn; red. eqm_to_eqmR B; apply eqmR_equal; cbn.
  unfold pure_, unit_l'. cbn; reflexivity.
Qed.

Lemma case_r' {A B: typ} (f: Kleisli m (A ⨥ bot_typ) (B ⨥ bot_typ)) :
  forall (p : Proper (equalE A ==> equalE (m (B ⨥ bot_typ))) (fun a : A => f @ inl a)),
    unit_r' >>> f ⩯ -=->! (fun a => f @ (inl a)) p.
Proof.
  intros.
  rewrite unit_r'_pure.
  intro. unfold cat, Cat_Kleisli, pure.
  cbn; red. eqm_to_eqmR (B ⨥ bot_typ); apply eqmR_equal; cbn.
  unfold cat_, pure_. cbn.
  rewrite eqmR_bind_ret_l; reflexivity.
Qed.

Fact bimap_id_pure {A B C : typ} (f : B -=-> C) :
  bimap (bif := sum_typ) (id_ A) (pure f) ⩯ pure (bimap (id_ A) f).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l; rewrite <- !case_pure. rewrite <- !compose_pure. rewrite <- pure_id.
  rewrite !cat_id_l.
  reflexivity.
Qed.

Fact bimap_pure_id {A B C : typ} (f : A -=-> B) :
  bimap (bif := sum_typ) (pure f) (id_ C) ⩯ pure (bimap f (id_ C)).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l, <- case_pure, <- compose_pure.
  reflexivity.
Qed.

Global Instance Coproduct_Kleisli : Coproduct (Kleisli m) sum_typ.
Proof.
  constructor.
  - intros a b c f g.
    unfold inl_, Inl_Kleisli.
    intro.
    rewrite pure_cat.
    cbn; red.
    eqm_to_eqmR c; apply eqmR_equal; cbn.
    reflexivity.
  - intros a b c f g.
    unfold inr_, Inr_Kleisli.
    intro; rewrite pure_cat.
    cbn; red.
    eqm_to_eqmR c; apply eqmR_equal; cbn.
    reflexivity.
  - intros a b c f g fg Hf Hg [x | y].
    + unfold inl_, Inl_Kleisli in Hf.
      rewrite pure_cat in Hf.
      specialize (Hf x). simpl in Hf.
      cbn. apply Hf.
    + unfold inr_, Inr_Kleisli in Hg.
      rewrite pure_cat in Hg.
      specialize (Hg y). simpl in Hg. cbn.
      apply Hg.
  - typeclasses eauto.
    Unshelve.
    + repeat intro; rewrite H; reflexivity.
    + repeat intro; rewrite H; reflexivity.
    + repeat intro; rewrite H; reflexivity.
    + repeat intro; rewrite H; reflexivity.
Qed.


Global Instance bimap_id_kleisli : BimapId (Kleisli m) sum_typ.
Proof.
  unfold BimapId, bimap, Bimap_Coproduct.
  intros.
  rewrite! cat_id_l.
  unfold inl_, inr_, Inl_Kleisli, Inr_Kleisli.
  rewrite case_pure.
  unfold pure, id_, case_, Case_Kleisli, case_sum, Id_Kleisli, pure.
  red. intro. cbn; red.
  eqm_to_eqmR (a ⨥ b); apply eqmR_equal; cbn.
  unfold pure_, inl_typ_proper. cbn.
  destruct a0; reflexivity.
Qed.

Lemma map_inl_case_kleisli:
  forall (a1 b1 b2 c1 c2 : typ) (f1 : Kleisli m a1 b1) (g1 : Kleisli m b1 c1) (g2 : Kleisli m b2 c2),
    map inl_ f1 >>> case_ (map inl_ g1) (map inr_ g2) ⩯ map inl_ (f1 >>> g1).
Proof.
  intros a1 b1 b2 c1 c2 f1 g1 g2.
  intro. cbn; red.
  eqm_to_eqmR (c1 ⨥ c2).
  setoid_rewrite eqmR_bind_bind; eauto.
  eapply eqmR_bind_ProperH; eauto.
  apply eqmR_equal; red; cbn; reflexivity.
  cbn.
  unfold pure_, case_, inl_, inr_. cbn.
  unfold inl_, map, inr_.
  unfold cat, Cat_Fun, Cat_Kleisli, case_.
  intros. setoid_rewrite eqmR_bind_ret_l. cbn.
  unfold cat_.
  apply eqmR_equal; cbn. rewrite H0. reflexivity.
  cbn. intros. 
  unfold pure_, case_, inl_, inr_. cbn.
  unfold inl_, map, inr_.
  unfold cat, Cat_Fun, Cat_Kleisli, case_.
  intros. setoid_rewrite eqmR_bind_ret_l. cbn.
  unfold cat_.
  apply eqmR_equal; cbn. rewrite H0. reflexivity.
Qed.

  Lemma map_inr_case_kleisli:
    forall (a2 b1 b2 c1 c2 : typ) (f2 : Kleisli m a2 b2) (g1 : Kleisli m b1 c1) (g2 : Kleisli m b2 c2),
      map inr_ f2 >>> case_ (map inl_ g1) (map inr_ g2) ⩯ map inr_ (f2 >>> g2).
  Proof.
    intros a2 b1 b2 c1 c2 f2 g1 g2.
    intro. cbn; red.
    eqm_to_eqmR (c1 ⨥ c2).
    setoid_rewrite eqmR_bind_bind; eauto.
    eapply eqmR_bind_ProperH; eauto.
    apply eqmR_equal; red; cbn; reflexivity.
    - cbn.
      unfold pure_, case_, inl_, inr_. cbn.
      unfold inl_, map, inr_.
      unfold cat, Cat_Fun, Cat_Kleisli, case_.
      intros. setoid_rewrite eqmR_bind_ret_l. cbn.
      unfold cat_.
      rewrite H0.
      apply eqmR_equal; cbn; reflexivity.      
    - cbn.
      unfold pure_, case_, inl_, inr_. cbn.
      unfold inl_, map, inr_.
      unfold cat, Cat_Fun, Cat_Kleisli, case_.
      intros. setoid_rewrite eqmR_bind_ret_l. cbn.
      unfold cat_.
      rewrite H0.
      apply eqmR_equal; cbn; reflexivity.      
  Qed.


Global Instance bimap_cat_kleisli : BimapCat (Kleisli m) sum_typ.
Proof.
  unfold BimapCat, bimap, Bimap_Coproduct.
  intros.
  unfold inl_, inr_, Inl_Kleisli, Inr_Kleisli.
  rewrite! cat_pure. rewrite! cat_case.
  rewrite map_inl_case_kleisli.
  rewrite map_inr_case_kleisli.
  reflexivity.
Qed.

Global Instance proper_bimap_kleisli : forall a b c d,
    @Proper (Kleisli m a c -> Kleisli m b d -> Kleisli m _ _) (eq2 ==> eq2 ==> eq2) bimap.
Proof.
  intros.
  repeat intro.
  unfold bimap, Bimap_Coproduct. cbn.
  red. eqm_to_eqmR (c ⨥ d). destruct a0.
  - unfold cat_.
    eapply eqmR_bind_ProperH; eauto.
    rewrite H. apply eqmR_equal; cbn; reflexivity.
    intros.
    eapply eqmR_equal; eauto. rewrite H2; cbn; reflexivity.
    intros; unfold cat_. apply eqmR_equal. cbn. rewrite H2; cbn; reflexivity.
  - unfold cat_. unfold inr_.
    eapply eqmR_bind_ProperH; eauto.
    rewrite H0. apply eqmR_equal; cbn; reflexivity.
    intros. rewrite H2. eapply eqmR_equal; eauto. cbn; reflexivity.
    intros.
    eapply eqmR_equal; eauto. rewrite H2; cbn; reflexivity.
Qed.


Global Instance Bifunctor_Kleisli : Bifunctor (Kleisli m) sum_typ.
constructor; typeclasses eauto.
Qed.

End BasicFacts.

Notation Proper_iter m a b :=
  (@Proper (Kleisli m a%type (sum_typ a b)%type -> (Kleisli m a%type b%type))
           (pointwise_relation _ eqm ==> pointwise_relation _ eqm)
           iter).
