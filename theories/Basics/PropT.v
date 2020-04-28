From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.

Definition rel A := A -> A -> Prop.

(* 
  DELAY_SPEC A := (DELAY A -> Prop) -> Prop
  DELAY A, ≈   
*)

(* Type TYP : Type := *)
(*   { t :> Type ; eq : rel t }. *)

Class TYP {A:Type} (eq:rel A) : Type.

Definition contains {A} {eq} (T:TYP eq) (a:A) : Prop := eq a a.
Notation "a ∈ T" := (contains T a) (at level 70).
  
Instance nat_eq_TYP : TYP (@eq nat).
Defined.
Instance bool_eq_TYP : TYP (@eq bool).
Defined.

Goal 3 ∈ (_:TYP (@eq nat)).
Proof.
  reflexivity.
Qed.  

Definition top {A} : rel A := fun a b => True.
Definition bot {A} : rel A := fun a b => False.


Instance nat_total_TYP : TYP (fun (n m:nat) => True).
Defined.

Definition prjtyp {A} {eq} `{T:TYP A eq} := A.
Definition prjeq {A} {eq} `{T:TYP A eq} := eq.


Definition prod_rel {A} {B} (eqa : rel A) (eqb : rel B) : rel (A * B) :=
  fun p q => eqa (fst p) (fst q) /\ eqb (snd p) (snd q).

Notation "e × f" := (prod_rel e f) (at level 70).

Instance prod_TYP {A B} {eqa} {eqb} `{TYP A eqa} `{TYP B eqb} :  TYP (eqa × eqb).
Defined.

Definition arr_rel {A} {B} (eqa : rel A) (eqb : rel B) : rel (A -> B) :=
  fun f g => forall a1 a2, eqa a1 a2 -> eqb (f a1) (g a2).

Notation "e ~~> f" := (arr_rel e f) (at level 60).

Instance arrow_TYP {A B} {eqa} {eqb} `{TYP A eqa} `{TYP B eqb} : TYP (eqa ~~> eqb).
Defined.

Goal TYP ((@eq nat) ~~> ((@eq nat) × (@eq nat))).
Proof.
  typeclasses eauto.
Qed.

Goal (fun n => (n, n)) ∈ (_: TYP ((@eq nat) ~~> ((@eq nat) × (@eq nat)))).
Proof.
  repeat red. intros. subst. split; reflexivity.
Qed.  

Lemma arrow_TYP_Proper :
  forall {A B} {eqa} {eqb} `{TYP A eqa} `{TYP B eqb}
    (f : A -> B), f ∈ (_ : TYP (eqa ~~> eqb)) <-> Proper (eqa ==> eqb) f.
Proof.
  intros A B eqa eqb TA TB f.
  split. intros TAB. apply TAB.
  intros H. apply H.
Qed.
  
Goal TYP ((@eq nat) ~~> (@bot nat)).
Proof.
  Fail typeclasses eauto. (* no instance *)
Abort.

Lemma id_ok: forall A eqa `{TYP A eqa},
    Proper (eqa ==> eqa) (fun (x:A) => x).
Proof.
  intros.
  repeat red. tauto.
Qed.  

Lemma cmp: forall A eqa B eqb C eqc `{TYP A eqa} `{TYP B eqb} `{TYP C eqc} (f : A -> B) (g : B -> C)
    (P1: Proper (eqa ==> eqb) f) 
    (P2: Proper (eqb ==> eqc) g),
    Proper (eqa ==> eqc) (fun x => g (f x)).
Proof.
  intros A eqa B eqb C eqc H H0 H1 f g P1 P2.
  repeat red.
  intros.
  apply P2. apply P1. assumption.
Qed.  


(*  We are working in a category  C
    Objects:    TYP eqA
    Hom (TYP eqA) (TYP eqB) := { f | Proper (eqA ==> eqB) f }
    ID in Hom (TYP eqA) (TYP eqA) := fun (x:A) => x
    
    An endo functor: F C => C is a pair:
       F : Type -> Type      
       eqF : forall a (eqa : Rel A), Rel (F A) (F A)
*)
(* 

 Definition: TYP := 
   {|
   A <: Type; 
   eqa <: rel A
   |}

 FUNCTOR:
   obj: TYP -> TYP
   fmap:  (TYP -> TYP) -> (TYP -> TYP)

class FUNCTOR (F : TYP -> TYP) := { ... }

*)          
Class FUNCTOR (F : Type -> Type)  :=
  {
    feq : forall {A} {eqa:rel A} (T:TYP eqa), rel (F A);

    feq_ok : forall {A} {eqa : rel A} `{TYP _ eqa}, TYP (@feq A eqa _); 
    
    fmap : forall {A} {eqa: rel A} `{TYP _ eqa} {B} {eqb: rel B} `{TYP _ eqb}, (A -> B) -> (F A -> F B);

    fmap_ok : forall {A B} {eqa} {eqb} `{TYP A eqa} `{TYP B eqb} (f : A -> B)
                (WF: f ∈ (_ : TYP (eqa ~~> eqb))),
                     (fmap f) ∈ (_ : TYP (@feq A eqa _ ~~> @feq B eqb _))
                  
  }.

  

  Class MONAD (M : Type -> Type) :=
   {
     ret  : forall {A} {eqa: rel A} `{TYP _ eqa}, A -> M A  ;
     bind : forall {A} {eqa: rel A} `{TYP _ eqa} {B} {eqb: rel B} `{TYP _ eqb},
         M A -> (A -> M B) -> M B
   }.

Section MonadLaws.
  Context {M : Type -> Type}.
  Context {FM : FUNCTOR M}.
  Context {MM : MONAD M}.

  
  Class MonadProperties : Prop :=
    {
      mon_ret_proper  :> forall A {eqa : rel A} `{PER A eqa} `{TYP _ eqa},
          Proper ((eqa) ==> (feq _)) ret;
      
      mon_bind_proper :> forall {A} {eqa: rel A} `{PER A eqa} `{TYP _ eqa}
                           {B} {eqb: rel B} `{PER B eqb} `{TYP _ eqb},
                      Proper ((feq _) ==> (eqa ==> (feq _)) ==> (feq _))
                      bind;

      bind_ret_l : forall {A} {eqa: rel A} `{PER A eqa} `{TYP _ eqa}
                           {B} {eqb: rel B} `{PER B eqb} `{TYP _ eqb}
          (f : A -> M B) (PF:Proper (eqa ==> (feq _)) f), 
        (eqa ~~> (feq _)) (fun (a:A) => bind (ret a) f)  f;

      bind_ret_r : forall A {eqa : rel A} `{PER A eqa} `{TYP _ eqa},
          ((feq _) ~~> (feq _)) (fun x => bind x ret) (id);

      
      bind_bind : forall {A} {eqa: rel A} `{PER A eqa} `{TYP _ eqa}
                    {B} {eqb: rel B} `{PER B eqb} `{TYP _ eqb}
                    {C} {eqc: rel C} `{PER C eqc} `{TYP _ eqc}
                    (f : A -> M B) (g : B -> M C)
                    (PF:Proper (eqa ==> (feq _)) f)  (* f \in TYP (eqa ~~> eqb) *) 
                    (PG:Proper (eqb ==> (feq _)) g), 
        ((feq _) ~~> (feq _))
          (fun (x:M A) => (@bind M _ B eqb _ C eqc _ (@bind M _ A eqa _ B eqb _ x f) g))
          (fun (x: M A) => (@bind M _ A eqa _ C eqc _ x (fun (y : A) => (bind (f y) g))))
    }.
End MonadLaws.


About MonadProperties.

Section MonadPropT.

  Context {M : Type -> Type}.
  Context {FM : FUNCTOR M}.
  Context {MM : MONAD M}.

  Context {A B C : Type}.                             
  Context {eqa : rel A} {eqb : rel B} {eqc : rel C}.
  Context (TA: TYP eqa).
  Context (TB: TYP eqb).
  Context (TC: TYP eqc).
  

  (* 
     PropT : TYP -> TYP
       
     Instance Prop_TYP : TYP :=
       { 
         A = Prop;
         eqa := fun p q => forall x, eqx x p x <-> q x
       }
  *)
  Definition PropT {X : Type} {eqx: rel X} (TX:TYP eqx) := { p : M X -> Prop | Proper (feq TX ==> iff) p }.

  Notation "! p" := (proj1_sig p) (at level 5).

About feq.
  
  Definition feq_PM : forall {A} {eqa:rel A} (TA:TYP eqa), rel (PropT TA) :=
    fun A eqa T PA1 PA2 =>
      (forall (ma : M A), (@feq M _ A eqa _) ma ma -> !PA1 ma <-> !PA2 ma).

  Lemma transport_refl_feq_PM: forall {X} {eqx: rel X} (T: TYP eqa),
      Reflexive eqa -> Reflexive (feq_PM T).
  Proof.
    intros X eqx T H.
    repeat red.
    tauto.
  Qed.



  
  Program Definition ret_PM {A} {eqa:rel A} `{Symmetric A eqa} `{Transitive A eqa} (TA:TYP eqa) (a:A) : PropT TA :=
    exist _ (fun (x:M A) => (@feq M _ A eqa _) (ret a) x) _.
  Next Obligation.
    repeat red.
    intros. split. intros. eapply transitivity. eassumption. eassumption.
    intros. eapply transitivity. eassumption. symmetry. assumption.
  Defined.
    
  


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
