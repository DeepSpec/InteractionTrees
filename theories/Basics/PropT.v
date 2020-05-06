From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Typ_Class2
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
.

(*  We are working in a category C.
    Objects:    Typ
    Hom (Typ eqA) (Typ eqB) := { f | Proper (eqA ==> eqB) f }
    ID in Hom (Typ eqA) (Typ eqA) := fun (x:A) => x
*)
Section TypCat.

  Definition typ_proper (TA TB : typ) := {f | Proper (equalE TA ==> equalE TB) f}.

  Instance eq2_typ_proper : Eq2 typ_proper :=
    (fun a b tp tp' =>
       let f := proj1_sig tp in
       let g := proj1_sig tp' in
       forall x y, x ∈ a -> y ∈ a -> equalE a x y -> equalE b (f x) (g y)).

  Lemma id_ok: forall (TA : typ),
      Proper (equalE TA ==> equalE TA) (fun x => x).
  Proof.
    intros.
    repeat red. tauto.
  Qed.

  Lemma compose: forall (TA TB TC : typ) (f : TA -> TB) (g : TB -> TC)
      (P1: Proper (equalE TA ==> equalE TB) f)
      (P2: Proper (equalE TB ==> equalE TC) g),
      Proper (equalE TA ==> equalE TC) (fun x => g (f x)).
  Proof.
    intros TA TB TC f g P1 P2.
    repeat red.
    intros.
    apply P2. apply P1. assumption.
  Qed.

  Instance id_typ_proper : Id_ typ_proper :=
    fun TA : typ =>
    exist (fun f : TA -> TA => Proper (equalE TA ==> equalE TA) f)
      (fun x : TA => x) (id_ok TA).

  Instance cat_typ_proper : Cat typ_proper :=
    fun (a b c : typ) (TA : typ_proper a b) (TB : typ_proper b c) =>
    exist (fun f : a -> c => Proper (equalE a ==> equalE c) f)
      (fun x : a => (` TB) ((` TA) x))
      (compose a b c (` TA) (` TB) (proj2_sig TA) (proj2_sig TB)).

  Instance cat_IdL_typ_proper : CatIdL typ_proper.
    repeat intro. destruct f. cbn. apply p. assumption.
  Defined.

  Instance cat_IdR_typ_proper : CatIdR typ_proper.
    repeat intro. destruct f. cbn. apply p. assumption.
  Defined.

  Instance cat_assoc_typ_proper : CatAssoc typ_proper.
    refine (fun a b c d TA TB TC => _). repeat intro.
    destruct TA, TB, TC. eapply p1. eapply p0. eapply p. assumption.
  Defined.

  Instance proper_typ_proper (a b c : typ) : Proper ((@eq2 typ _ _ a b) ==> (@eq2 typ _ _ b c) ==> (@eq2 typ _ _ a c)) (cat).
    repeat intro.
    destruct x, y, x0, y0. unfold eq2, eq2_typ_proper in H0.
    cbn in H0. unfold eq2, eq2_typ_proper in H. cbn in H. cbn.
    specialize (H x1 y1 H1 H2 H3).
    specialize (H0 (x x1) (x2 y1)).
    apply H0. 3 : apply H. apply p. apply H1. apply p0. apply H2.
  Defined.

  Global Instance category_typ_proper : Category typ_proper.
    constructor; try typeclasses eauto.
  Defined.

  (*
    FUNCTOR:
    obj: TYP -> TYP
    fmap:  (TYP -> TYP) -> (TYP -> TYP)

      An endo functor: F C => C is a pair:
        F : Type -> Type
        eqF : forall a (eqa : Rel A), Rel (F A) (F A)
   *)

  (* Definition fmap (F : typ -> typ) : forall a b : typ, typ_proper a b -> typ_proper (F a) (F b). *)
  (* Admitted. *)

  (* IY: We get "OK Laws" for free from the definition of arrows in our category,
   *     and can use the functor definition in [CategoryFunctor.v] *)

  (* Class FUNCTOR (F : typ -> typ) := *)
  (* { *)
  (*   feq : forall {A : typ}, rel (F A); *)
  (*   (* feq_ok : forall (A : typ), Typ (@feq A); *) *)
  (*   fmap : forall {A B : typ}, (A -> B) -> (F A -> F B); *)
  (*   fmap_ok : forall {A B : typ} (f : A -> B) *)
  (*               (WF: f ∈ (A ~~> B)), *)
  (*               (fmap f) ∈ (@feq A ~~> @feq B) *)
  (* }. *)


  (* IY : Defined [CategoryMonad.v]. *)
  
  (* Class MONAD (M : typ -> typ) := *)
  (*  { *)
  (*    ret  : forall {A : typ}, typ_proper A (M A); *)
  (*    bind : forall {A B : typ}, *)
  (*        M A -> (A -> M B) -> M B *)
  (*  }. *)

End TypCat.

(* Section MonadLaws. *)


(*   Class MonadProperties : Prop := *)
(*     { *)
(*       (* mon_ret_proper  :> forall {A : typ} `{PER A (equalE A)}, *) *)
(*       (*     Proper ((equalE A) ==> feq) ret; *) *)

(*       (* mon_bind_proper :> forall {A B : typ} `{PER A (equalE A)} `{PER B (equalE B)}, *) *)
(*       (*                 Proper (feq ==> (equalE A ==> feq) ==> feq) *) *)
(*       (*                 bind; *) *)

(*       bind_ret_l : forall {A B : typ} `{PER A (equalE A)} `{PER B (equalE B)} *)
(*           (f : A -> M B) (PF:Proper (equalE A ==> feq) f), *)
(*         (equalE (equalE A ~~> feq)) (fun (a:A) => bind (ret a) f)  f; *)

(*       bind_ret_r : forall {A : typ} `{PER A (equalE A)}, *)
(*           (equalE (feq ~~> feq)) (fun x => bind x ret) (id); *)

(*       bind_bind : forall {A B C : typ} *)
(*                     `{PER A (equalE A)} `{PER B (equalE B)} `{PER C (equalE C)} *)
(*                     (f : A -> M B) (g : B -> M C) *)
(*                     (PF:Proper (equalE A ==> feq) f)  (* f \in TYP (eqa ~~> eqb) *) *)
(*                     (PG:Proper (equalE B ==> feq) g), *)
(*         (equalE (feq ~~> feq)) *)
(*           (fun (x: M A) => (@bind M _ B C (bind x f) g)) *)
(*           (fun (x: M A) => (@bind M _ A C x (fun (y : A) => (bind (f y) g)))) *)
(*     }. *)
(* End MonadLaws. *)


Section MonadPropT.

  Context {M : typ -> typ}.
  Context `{F : Functor typ typ typ_proper typ_proper M}.
  Context `{FL : FunctorLaws typ typ typ_proper typ_proper M}.
  Context `{CM : Monad typ typ_proper M}.
  Context `{ML : MonadLaws typ typ_proper M}.

  (*
     PropT : TYP -> TYP

     Instance Prop_TYP : TYP :=
       {
         A = Prop;
         eqa := fun p q => forall x, eqx x p x <-> q x
       }
   *)

  (* IY: feq is equalE (M X). *)
  (* Context {feq : forall (A : typ), rel (M A)}. *)

  Definition PropT : typ -> typ :=
    fun (X : typ) =>
      {|
        Ty := { p : M X -> Prop | Proper (equalE (M X) ==> iff) p };
        equal :=
          fun PA1 PA2 =>
            forall (ma : M X), equalE (M X) ma ma -> ` PA1 ma <-> ` PA2 ma
      |}.

  Instance PropT_Monad : Monad typ_proper PropT.
  Admitted.

  Instance PropT_MonadLaws : MonadLaws PropT_Monad.
  Admitted.

End MonadPropT.

(* Outdated sketches. *)
  (* Lemma transport_refl_feq_PM: forall {X : typ}, *)
  (*     Reflexive (equalE X) -> Reflexive (feq_PM X). *)
  (* Proof. *)
  (*   intros X eqx T H. *)
  (*   repeat red. *)
  (*   tauto. *)
  (* Qed. *)

  (* Lemma transport_symm_feq_PM : forall {X : typ}, *)
  (*     Symmetric (equalE X) -> Symmetric (feq_PM X). *)
  (* Proof. *)
  (*   repeat red. intros X H x y H0 ma H1. *)
  (*   split. Admitted. *)

  (* Lemma transport_symm_feq : *)
  (*   forall {X : typ}, (Symmetric (equalE X) -> Symmetric feq). *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)

  (* Lemma transport_trans_feq : *)
  (*   forall {X : typ}, (Transitive (equalE X) -> Transitive feq). *)
  (* Proof. *)
  (*   intros. red in H. *)
  (* Admitted. *)

  (* Program Definition ret_PM {A : typ} `{Symmetric A (equalE A)} `{Transitive A (equalE A)} (a : A) : @PropT A := *)
  (*   exist _ (fun (x:M A) => feq (ret a) x) _. *)
  (* Next Obligation. *)
  (*   repeat red. *)
  (*   intros. split. intros. eapply transitivity. eassumption. eassumption. *)
  (*   intros. eapply transitivity. eassumption. *)
  (*   apply (transport_symm_feq H). assumption. *)
  (*   Unshelve. apply transport_trans_feq. assumption. *)
  (*   Unshelve. apply transport_trans_feq. assumption. *)
  (* Defined. *)


(*  
  Global Instance monad_return_PM : @MonadReturn PM A _ _ := @ret_PM.
  
  Definition bind_PM (m : PM A) (f : A -> PM B) : PM B := 
    fun (b:B) =>
      exists (a:A), eqa a a /\ m a /\ f a b.

  Global Instance monad_bind_PM : @MonadBind PM _ _ _ _ TA TB := @bind_PM.
    
  Global Instance functor_PM : Functor PM.
  unfold Functor. unfold PM.
  exact (fun A eqa P Q => forall (a b:A), eqa a b -> (P a <-> Q b)).
  Defined.

  Global Instance functorOK_PM : @FunctorOK PM functor_PM.
  unfold FunctorOK.
  intros.
  unfold transport, functor_PM.
  constructor.
  - red. intros. symmetry. apply H. symmetry. assumption.
  - red. intros x y z H H1 a b H2. 
    eapply transitivity. apply H. apply H2. apply H1. eapply transitivity. symmetry. apply H2. apply H2.
  Defined.
End MonadProp.

Section MonadPropLaws.
  Context {A B C : Type}.
  Context {eqa : rel A} {eqb : rel B} {eqc : rel C}.
  Context (TA: TYP eqa).
  Context (TB: TYP eqb).
  Context (TC: TYP eqc).

  About MonadProperties.

  Instance monad_properties_PM : @MonadProperties PM A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  split.
  - repeat reduce.
    + unfold ret, monad_return_PM, ret_PM. split.
      intros. eapply transitivity. symmetry. apply H0. eapply transitivity. apply H1. assumption.
      intros. eapply transitivity. apply H0. eapply transitivity. apply H1. symmetry. assumption.      

  - repeat reduce.
    unfold bind, monad_bind_PM, bind_PM. split.
    intros. destruct H4 as (a0 & I & J & K).
    exists a0. repeat split; try tauto. eapply H.  apply I. tauto. eapply H0.
    apply I. apply H1. apply K.
    intros. destruct H4 as (a0 & I & J & K).
    exists a0. repeat split; try tauto. eapply H; tauto. eapply H0. apply I. tauto. tauto.

  - repeat reduce.
    unfold ret, monad_return_PM, ret_PM.
    unfold bind, monad_bind_PM, bind_PM.
    split.
    + intros.
      destruct H1 as (a1 & I & J & K).
      apply (PF a1 a); eauto.
    + intros.
      exists a. tauto.

  - repeat reduce.
    unfold ret, monad_return_PM, ret_PM.
    unfold bind, monad_bind_PM, bind_PM.
    split.
    + intros.
      destruct H1 as (a1 & I & J & K).
      unfold id. unfold transport in H. unfold functor_PM in H.

                                                  
*)
