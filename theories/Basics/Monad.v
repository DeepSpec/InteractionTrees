(** * Monad laws and associated typeclasses *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryMonad
     Basics.CategoryTheory
     Basics.Typ
     Basics.HeterogeneousRelations
     Basics.Function.
(* end hide *)

Set Primitive Projections.

Import Carrier.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope typ_scope.
Section EqmR.

(* SAZ: really HeterogenousRelations should be proper.  We could remove all those assumptions here. *)

  (* We consider heterogeneous relations on computations parameterized by a relation on the return types *)
  (* Rq: if we make [EqMR] a singleton class, the type checker tends to craft dumb instances for itself behind our back.
    I wrapped it up in a record, it seems to prevent this behavior.
  *)
  Class EqmR (m : typ -> typ) : Type :=
    {
      eqmR : forall (A B : typ) (R : relationH A B), relationH (m A) (m B) ;
      eqmR_equal : forall (A : typ), eq_rel (eqmR A A A) (m A)
    }.

  (*
    The more traditional notion of monadic equivalence is recovered at the equality relation
    [forall A,  m A -> m A -> Prop]
   *)
  Definition eqm {m : typ -> typ} `{@EqmR m} {A: typ} := eqmR A A A.

End EqmR.

(* YZ: I don't think [A] should be maximally inserted, but putting it back as is for now for retro-compatibility *)
Arguments eqmR {m _ A B}.
Arguments eqm {m _ A}.
Arguments eqmR_equal {m _}.
Infix "A ≈ B" := (eqm @ (A, B)) (at level 70) : monad_scope.

Section EqmRRel.
  Context (m : typ -> typ).
  Context {EqMR : EqmR m}.

  Import RelNotations.
  Local Open Scope relationH_scope.

(*
  Global Instance Proper_transpose_relationH {A B : typ} (R: relationH A B) `{Proper _ (equalE A ==> equalE B ==> iff)%signature R} : Proper (equalE B ==> equalE A ==> iff) (†R).
  Proof.
    repeat red.
    unfold transpose; intros; cbn in *.
    apply H; assumption.
  Qed.

  Global Instance Proper_compose_relationH {A B C: typ}
         (R1: relationH A B)
         (R2 : relationH B C)
         `{Proper _ (equalE A ==> equalE B ==> iff)%signature R1}
         `{Proper _ (equalE B ==> equalE C ==> iff)%signature R2}
    : Proper (equalE A ==> equalE C ==> iff) (R2 ∘ R1).
  Proof.
    repeat red. unfold HeterogeneousRelations.compose.
    intros; cbn in *.
    split; intros (b & Hxb & Hbx); exists b; split; intros.
    - specialize (H _ _ H1).
*)

  (* Requirements of well-formedness of [eqmR] *)
  Class EqmR_OK : Type :=
    {
    (* [eqmR] should transport elementary structures of the relation [R] *)
    (* Question: should it transport anti-symmetry? *)

    eqmR_transport_symm :>  forall {A : typ} (R : relationH A A), Symmetric ↓R -> Symmetric ↓(eqmR R);

    eqmR_transport_trans :> forall {A : typ} (R : relationH A A), Transitive ↓R -> Transitive ↓(eqmR R);

      (* [eqmR] is associative by composing the underlying relationHs *)
    eqmR_rel_trans : forall {A B C : typ}
                       (R1 : relationH A B)
                       (R2 : relationH B C)
                       (ma : m A) (mb : m B) (mc : m C),
        eqmR R1 @ (ma, mb) ->
        eqmR R2 @ (mb, mc) ->
        eqmR (R2 ∘ R1) @ (ma, mc);

    eqmR_lift_transpose : forall {A B : typ} (R : relationH A B)
      , eq_rel (eqmR †R) (†(eqmR R));

    eqmR_rel_prod : forall {A1 A2 B1 B2 : typ}
                          (RA : relationH A1 A2)
                          (RB : relationH B1 B2)
                          (f : A1 -> B1 -> m (A1 × B1))
                          (g : A2 -> B2 -> m (A2 × B2))
                          (x1 : A1) (x2 : A2) (y1 : B1) (y2 : B2),
      RA @ (x1, x2) ->
      RB @ (y1, y2) ->
      eqmR (RA ⊗ RB) @ (f x1 y1, g x2 y2);

      (* [eqmR] respects extensional equality of the underlying relationH
         and [eqm] on both arguments over the monad *)
      (* SAZ: We need to restrict this to only Proper relations R, otherwise even
         the identity monad doesn't work.
         - option 1 : change relationH to be A -=-> B -=-> Prop_type
           keep the old fully-general version

         - option 2 : restrict eqmR_Proper as shown:
      *)
    eqmR_Proper :> forall {A B : typ},
        Proper (@eq_rel A B ==> eq_rel) eqmR;

      (* [eqmR] is monotone as a morphism on relationHs *)
    eqmR_Proper_mono :> forall {A B},
        Proper (@subrelationH _ _ ==> @subrelationH _ _) (@eqmR m _ A B);
    }.

End EqmRRel.


(* SAZ: Renamed "Domain" to "Image" -- more accurate *)
Section Image.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmROKm : EqmR_OK m}.


  Definition eq_rel' {A B: Type} (R S : A -> B -> Prop)  :=
    forall a b, R a b <-> S a b.

  Definition transpose' {A B:Type} (R : A -> B -> Prop) : B -> A -> Prop :=
    fun x y => R y x.

  Definition subrelation' {A B:Type} (R S : A -> B -> Prop) : Prop :=
    forall a b, R a b -> S a b.

  Definition comp' {A B C} (R : A -> B -> Prop) (S : B -> C -> Prop) : A -> C -> Prop :=
    fun a c => exists b, R a b /\ S b c.
  
  Definition Property (A B : Type) (R : A -> B -> Prop) :=
    subrelation' R (comp' R (comp' (transpose' R) R))
    /\
    subrelation' (transpose' R) (comp' (transpose' R) (comp' R (transpose' R))).

  
  Lemma symmetric_property (A:Type) (R : A -> A -> Prop) (HP: Property A A R) : Symmetric R.
  Proof.
    repeat red. intros.
    repeat red in HP. destruct HP.  cbn in *.
    apply H0 in H. red in H. destruct H as (b & Rb & (a & Ra)).

  Lemma transitive_property (A:Type) (R : A -> A -> Prop) (HP: Property A A R) : Transitive R.
    
  
  Program Definition imageH {A1 A2:typ} (m1 : m A1) (m2 : m A2) : relationH A1 A2 :=
    fun (p : A1 × A2) =>
      forall (R : relationH A1 A2)
        (HS : SymmetricH R) 
        (TS : TransitiveH R)
        (EQ: eqmR R @ (m1, m2)), R @ p.

  Definition image {A:typ} (m : m A) : relationH A A := imageH A A m m.

  

  (* SAZ:
     We *don't* want the image to be reflexive because it's not true.

     Consider itrees then [image spin] is the empty PER because there
     are no elements that can be returned.


     Q: should we instead define this as a predicate of type A -=-> prop_typ ?
   *)
  Program Definition image {A:typ} (m : m A) : relationH A A :=
    fun p =>
      forall (R : relationH A A)
        (HS : SymmetricH R)
        (TS : TransitiveH R)
        (EQ: eqmR R @ (m, m)), R @ p.
  Next Obligation.
    do 2 red.
    intros (x1 & y1) (x2 & y) (H1 & H2). cbn in *.
    split; intros.
    - specialize (H R).
      rewrite <- H1.
      rewrite <- H2.
      apply H; assumption.
    - specialize (H R).
      rewrite H1, H2.
      apply H; assumption.
  Qed.

  (* Using image we can define the [mayRet] predicate, which identifies
     the subset of A on which the computation ma can halt with
     a [ret x]

  *)
  Program Definition mayRet {A:typ} (ma : m A) : A -=-> prop_typ :=
    (fun (a:A) => image ma @ (a, a)).
  Next Obligation.
    do 2 red.
    intros a1 a2 HA; split; intros.
    - rewrite <- HA. apply H; auto.
    - rewrite HA; apply H; auto.
  Qed.

  Lemma transpose_eq {A} (R : relationH A A) (x:A) :
    R @ (x, x) <-> (transpose R) @ (x, x).
  Proof.
    split; intros.
    destruct R; cbn in *.
    assumption.
    destruct R; cbn in *.
    assumption.
  Qed.
  
  Lemma image_symmetric {A} (ma : m A) : SymmetricH (image ma).
  Proof.
    red.
    intros a.
    repeat intro.
    apply HS. apply H; auto.
  Qed.

  Lemma image_transitive {A} (ma : m A) : TransitiveH (image ma).
  Proof.
    red.
    intros.
    destruct p; destruct q; cbn in *.
    intros.
    pose proof (TS (t, t0) (t1, t2)). apply H2. apply H; assumption.
    apply H0; assumption. apply H1.
  Qed.

    Lemma image_Reflexive_l {A:typ} (ma : m A) (a1 a2:A) 
    (H : image ma @ (a1, a2)) : image ma @ (a1, a1).
  Proof.
    assert (image ma @ (a2, a1)).
    { apply image_symmetric in H. apply H. }
    eapply image_transitive in H. apply H in H0. apply H0. reflexivity.
  Qed.

  Lemma image_Reflexive_r {A:typ} (ma : m A) (a1 a2:A) 
    (H : image ma @ (a1, a2)) : image ma @ (a2, a2).
  Proof.
    assert (image ma @ (a2, a1)).
    { apply image_symmetric in H. apply H. }
    eapply image_transitive in H0. apply H0 in H. apply H. reflexivity.
  Qed.
  
  
  Lemma image_least {A} (ma : m A) (R : relationH A A)
        (HS : SymmetricH R)
        (TS : TransitiveH R)
        (G: eqmR R @ (ma, ma))
    : subrelationH (image ma) R.
  Proof.
    intros x y D.
    unfold image in D.
    cbn in *.
    apply D; assumption.
  Qed.
  
  Global Instance Proper_image {A} :
    Proper (equalE (m A) ==> eq_rel) image.
  Proof.
    do 2 red.
    intros x y EQ.
    split.
    - red. intros a b H.
      repeat red.
      intros.
      repeat red in H.
      rewrite <- EQ in EQ0.
      specialize (H R HS TS EQ0).
      apply H.
    - red. intros a b H.
      repeat red.
      intros.
      repeat red in H.
      rewrite  EQ in EQ0.
      specialize (H R HS TS EQ0).
      apply H.
  Qed.

  Global Instance Proper_image2 {A}  :
    Proper (equalE (m A) ==> equalE (A × A) ==> iff) (fun ma => (proj1_sig (image ma))).
  Proof.
    do 3 red.
    intros a b H (p1 & p2) (q1 & q2) (HP & HQ).
    split; intros; cbn in *;  intros.
    - rewrite <- HP.
      rewrite <- HQ.
      apply H0; auto. rewrite H. assumption.
    - rewrite HP.
      rewrite HQ.
      apply H0; auto. rewrite <- H. assumption.
  Qed.

  Global Instance Proper_image3 {A}  :
    Proper (equalE (m A) ==> (@eq2 typ typ_proper _ _ _)) image.
  Proof.
    do 3 red.
    intros a b H (p1 & p2) (q1 & q2) (HP & HQ).
    cbn in HP, HQ. rewrite HP. rewrite HQ. 
    split; intros; cbn in *;  intros.
    - apply H0; auto. rewrite H. assumption.
    - apply H0; auto. rewrite <- H. assumption.
  Qed.

  
  Global Instance Proper_mayRet {A:typ} :
    Proper (equalE (m A) ==> (equalE A) ==> iff) (fun ma => (proj1_sig (mayRet ma))).
  Proof.
    do 3 red.
    intros x y H x0 y0 H0.
    split; intros; cbn in *; intros.
    - rewrite <- H0. apply H1; auto. rewrite H. assumption.
    - rewrite H0. apply H1; auto. rewrite <- H. assumption.
  Qed.      

  Global Instance Proper_mayRet2 {A}  :
    Proper (equalE (m A) ==> (@eq2 typ typ_proper _ _ _)) mayRet.
  Proof.
    repeat red.
    intros; split; intros; cbn in *; intros.
    - rewrite <- H0. apply H1; auto. rewrite H. auto.
    - rewrite H0. apply H1; auto. rewrite <- H. auto.
  Qed.

  
  Lemma image_subset {A:typ} (ma : m A) :
    subrelationH (eqmR (image ma)) (m A).
  Proof.
    unfold subrelationH.
    intros.
    apply eqmR_equal.
    specialize (@image_least A ma).
    intros P.
    specialize (P (relationH_of_typ A)).
    eapply eqmR_Proper_mono; eauto.
    apply P.
    - apply relationH_symmetric.
    - apply relationH_transitive.
    - apply eqmR_equal. apply (@relationH_reflexive (m A)).
  Qed.

End Image.



(* In particular, well-formedness of [eqmR] recovers that [eqm] is an equivalence relationH *)
Section EqmRMonad.
  Context (m : typ -> typ).
  Context {EqMRm : EqmR m}.
  Context {Mm : Monad typ_proper m}.

  (* Generalization of monadic laws.
     These are of two quite distinct natures:
     * Heterogeneous generalizations of the usual three monad laws
     * Reasoning principles relating [eqmR R] to [R]
     *)
  Class EqmRMonad :=
    {
      (* SAZ: we can prove only one direction of this law.
          - for StateT we can take the void state, which also cannot be inverted.

          - However, for some monads we do get the other direction:
            (itree E) and StateT S when S is non-void, for example.  So we
            break the other direction out into a different typeclass that
            can be instantiated differently.
       *)
      eqmR_ret : forall {A1 A2 : typ} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        RA @ (a1, a2) -> eqmR RA @ (ret @ a1, ret @ a2);

      eqmR_bind_ProperH : forall {A1 A2 B1 B2 : typ}
                            (RA : relationH A1 A2)
                            (RB : relationH B1 B2)
                            ma1 ma2
                            (kb1 : A1 -=-> m B1) (kb2 : A2 -=-> m B2),
          eqmR RA @ (ma1, ma2) ->
          (forall a1, mayRet m ma1 @ a1 ->
                 exists (a2:A2), RA @ (a1, a2) /\ (mayRet m ma2 @ a2) /\ eqmR RB @ (kb1 @ a1, kb2 @ a2))
          ->
          (forall a2, mayRet m ma2 @ a2 ->
                 exists (a1:A1), RA @ (a1, a2) /\ (mayRet m ma1 @ a1) /\ eqmR RB @ (kb1 @ a1, kb2 @ a2))
          ->
          eqmR RB @ (bind kb1 @ ma1, bind kb2 @ ma2);

    (* Question: The following helps _proving_ [eqmR _ (bind _ _)].
       Should we require something to invert such an hypothesis?
    eqmR_Proper_bind :> forall {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop),
        (Proper (eqmR RA ==> (RA ==> (eqmR RB)) ==> eqmR RB) bind);
     *)

      eqmR_bind_ret_l : forall {A B : typ}
                          (f : A -=-> m B)
                          (a : A),

          equalE (m B) (bind f @ (ret @ a)) (f @ a);

      eqmR_bind_ret_r : forall {A B : typ}
                          (ma : m A),
          equalE (m A) (bind ret @ ma) ma;

       (* forall (a b c : obj) (f : C a (M b)) (g : C b (M c)), bind f >>> bind g ⩯ bind (f >>> bind g) *)
      eqmR_bind_bind : forall {A B C : typ}
                       (ma : m A)
                       (f : A -=-> m B)
                       (g : B -=-> m C),
          equalE (m C) ((bind f >>> bind g) @ ma) (bind (f >>> bind g) @ ma)
    }.

End EqmRMonad.

Arguments eqmR_bind_ret_l {_ _ _ _}.

Section Laws.

  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.

  Local Open Scope monad_scope.

  Global Instance monad_eqmR : MonadLaws Mm.
  Proof.
    split; intros.
    - intros x y H.
      pose proof eqmR_bind_ret_l as Hbr.
      specialize (Hbr a b f).
      specialize (Hbr x).
      rewrite <- H.
      apply Hbr.
    - intros x y H. cbn.
      rewrite eqmR_bind_ret_r. apply H. apply EqmRm. eauto.
    - repeat intro.
      pose proof eqmR_bind_bind.
      rewrite H.
      specialize (H0 m _ _ _ _ _ _ y f g).
      assumption.
    - repeat intro. rewrite H0.
      pose proof (eqmR_bind_ProperH).
      specialize (H1 _ _ _ _ a a b b a b x0 y0 x y).
      assert (eqmR a @ (x0, y0)).
      { apply eqmR_equal. assumption. }
      specialize (H1 H2).
      rewrite <- H0 at 1.
      apply eqmR_equal.
      apply H1.
      + intros. exists a1. split; [|split].
        * cbn. reflexivity.
        * rewrite <- H0. assumption.
        * apply eqmR_equal. apply Proper_typ_proper_app. 
          apply H. reflexivity.
      + intros. exists a2. split; [| split].
        * cbn. reflexivity.
        * rewrite H0. assumption.
        * apply eqmR_equal. apply Proper_typ_proper_app. 
          apply H. reflexivity.
  Qed.

End Laws.



Section EqmRInversion.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.


  Class EqmRMonadInverses :=
    {
    image_eqmR {A : typ} (ma : m A) : eqmR (image m ma) @ (ma, ma);
    
    eqmR_ret_inv : forall {A1 A2 : typ} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        eqmR RA @ (ret @ a1, ret @ a2) -> RA @ (a1, a2);

    eqmR_bind_inv : forall {A1 A2 : typ} {B1 B2 : typ} (RB : relationH B1 B2)
                      (ma1 : m A1) (ma2 : m A2)
                      (k1 : A1 -=-> m B1)
                      (k2 : A2 -=-> m B2),
        eqmR RB @ (bind k1 @ ma1, bind k2 @ ma2) ->
        forall (RA : relationH A1 A2),   (* P a1 a2 <-> mayRet ma1 @ a1 <-> mayRet ma2 @ a2  *)
          eqmR RA @ (ma1, ma2) ->
          (forall a1, mayRet m ma1 @ a1 -> exists (a2:A2), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2))
          /\
          (forall a2, mayRet m ma2 @ a2 -> exists (a1:A1), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2))
    }.

End EqmRInversion.

Section InversionFacts.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.
  Context {MI : EqmRMonadInverses m}.

  Lemma mayRet_choice {A:typ} (ma : m A) :
    (exists a, mayRet m ma @ a) \/ ~(exists a, mayRet m ma @ a).
  Proof.
    admit. (* TODO: import classical logic *)
  Admitted.


  
  (* SAZ: This one is probably not needed 
     It is unfortunate that k can't have type A -=-> m B -- we need
     some kind of typecast "conversion lemma":
  *)
  Lemma empty_image {A:typ} (ma : m A) : 
    ~(exists a, mayRet m ma @ a) -> forall (k : A -=-> m A), bind k @ ma == ma.
  Proof.
    intros N k.
    assert (ma == (bind ret @ ma)).
    { rewrite bind_ret_r. cbn. reflexivity. }
    rewrite H at 2.
    apply eqmR_equal.
    apply eqmR_bind_ProperH with (RA := (image m ma)). assumption.
    eapply image_eqmR. apply MI. 
    intros.
    assert (exists a, image m ma @ (a, a)).
    { exists a1. eapply image_Reflexive_l. apply H0. }
    contradiction.
    intros.
    assert (exists a, image m ma @ (a, a)).
    { exists a2. eapply image_Reflexive_l. apply H0. }
    contradiction.
  Qed.

  Import RelNotations.
  Local Open Scope relationH_scope.


  Lemma mayret_eqmR {A B:typ} (ma : m A) (mb : m B)
        (R : relationH A B)
        (* SAZ : Not sure if we need these assumptions *)
        (RS: SymmetricH (†R ∘ R)) (RT: TransitiveH (†R ∘ R))
        (EQ : eqmR R @ (ma, mb)):
    forall (a : A), mayRet m ma @ a -> exists (b:B), mayRet m mb @ b /\ R @ (a, b).
  Proof.
    intros a HA.
    do 6 red in HA.
    specialize (HA (†R ∘ R) RS RT).
    assert (eqmR (†R) @ (mb, ma)).
    { apply eqmR_lift_transpose; assumption. }
    specialize (eqmR_rel_trans m _ _ _ _ _ EQ H) as HR.
    apply HA in HR.
    repeat red in HR. destruct HR as (b & Rab & Rba). cbn in *.
    exists b; split; [|assumption].
    intros.
  Admitted.    
    
    
  
  Lemma mayret_bind {A B:typ} (ma : m A) (k : A -=-> m B) (b : B) :
    mayRet m (bind k @ ma) @ b -> exists a, mayRet m ma @ a /\ mayRet m (k @ a) @ b.
  Proof.
    intros HM.
    unfold mayRet in HM. cbn in HM.
    assert ((exists a : A, mayRet m ma @ a /\ mayRet m (k @ a) @ b) \/
            ~((exists a : A, mayRet m ma @ a /\ mayRet m (k @ a) @ b))).
    { admit. (* TODO: classical logic *) }
    destruct H; auto.
    assert (forall a, ~(mayRet m ma @ a /\ mayRet m (k @ a) @ b)).
    { intros. intros E. assert (exists a : A, mayRet m ma @ a /\ mayRet m (k @ a) @ b).
      exists a. assumption. contradiction. }
  Admitted.

  (* A sanity check about the images: *)
  Program Definition singletonR {A:typ} (x:A) : relationH A A :=
    (fun p => (fst p) == (snd p) /\ (fst p) == x).
  Next Obligation.
    do 2 red.
    intros.
    destruct x0, y; cbn in *.
    destruct H.
    split; intros (HA & HB); split.
    - rewrite <- H. rewrite <- H0. assumption.
    - rewrite <- H. assumption.
    - rewrite H. rewrite H0. assumption.
    - rewrite H. assumption.
  Qed.


  Lemma singletonR_SymmetricH {A:typ} (x:A) : SymmetricH (singletonR x).
  Proof.
    repeat red. intros (a1 & a2) H. unfold singletonR in H. cbn in *.
    destruct H. split; symmetry. tauto. rewrite <- H. symmetry. assumption.
  Qed.

    
  (* Global Instance singletonR_symetric  *)
  (* Proof. *)
  (*   repeat red. intros. unfold singletonR in H. *)
  (*   destruct H. split; symmetry. tauto. rewrite <- H. symmetry. assumption. *)
  (* Qed. *)

  Lemma singletonR_TransitiveH {A:typ} (x:A) : TransitiveH (singletonR x).
  Proof.
      repeat red. intros (a1 & a2) (b1 & b2) HA HB H. unfold singletonR in *. cbn in *.
      destruct HA, HB; split; etransitivity; eauto. rewrite <- H3. assumption. PER_reflexivity.
  Qed.

(*    
  Global Instance singletonR_transitive {A:typ} (x:A) : Transitive (singletonR x).
  Proof.
      repeat red. intros. unfold singletonR in *.
      destruct H, H0; split; etransitivity; eauto. rewrite <- H2. assumption. PER_reflexivity.
  Qed.
 *)

  (*
  Global Instance singletonR_PER {A:typ} (x:A) : PER (singletonR x).
  Proof.
    split; typeclasses eauto.
  Qed.
   *)
(*
  Global Instance Proper_singletonR {A:typ} (x:A) : Proper (equalE A ==> equalE A ==> iff) (singletonR x).
  Proof.
    repeat red; intros; unfold singletonR in *.
    split; intros (HA & HB); split.
    - rewrite <- H. rewrite HA. assumption.
    - rewrite <- H. assumption.
    - rewrite H. rewrite H0. assumption.
    - rewrite H. assumption.
  Qed.
*)
  Lemma ret_image {A:typ} (x:A) : eq_rel (image m (ret @ x)) (singletonR x).
  Proof.
    split.
    - repeat red. intros. 
      unfold image in H. cbn in *.
      specialize (H (singletonR x)).
      assert (SymmetricH (singletonR x)).
      { apply singletonR_SymmetricH. }
      assert (TransitiveH (singletonR x)).
      { apply singletonR_TransitiveH. }
      specialize (H H0 H1).
      assert (eqmR (singletonR x) @ (ret @ x, ret @ x)).
      { apply eqmR_ret. typeclasses eauto.  repeat red. cbn. split. reflexivity. reflexivity. }
      apply H in H2. repeat red in H2. assumption.
    - do 4 red. intros.
      unfold singletonR in H. destruct H. cbn in *.
      rewrite <- H. rewrite H0.
      eapply eqmR_ret_inv; eauto.
  Qed.

  
End InversionFacts.
