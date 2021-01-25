From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
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
     Dijkstra.TracesIT
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Variant nonempty (A : Type) : Prop := ne (a : A).

Class Preorder :=
  {
    L : Type;
    leq : L -> L -> Prop;
  }.

(* will need more propositional constrainst on Preorders *)

Section SecureUntimed.
  Context {E : Type -> Type} {R1 R2 : Type}.
  Context (Label : Preorder).
  Context (priv : forall A, E A -> L).
  Context (RR : R1 -> R2 -> Prop).

  Inductive secure_eqitF (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop := 

    (* eqitF constructors *)
    | secEqRet r1 r2 : RR r1 r2 -> secure_eqitF b1 b2 l vclo sim (RetF r1) (RetF r2)
    | secEqTau t1 t2 : sim t1 t2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) (TauF t2)
    | secEqTauL t1 ot2 (CHECK : b1) : secure_eqitF b1 b2 l vclo sim (observe t1) ot2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) ot2
    | secEqTauR ot1 t2 (CHECK : b2) : secure_eqitF b1 b2 l vclo sim ot1 (observe t2) -> secure_eqitF b1 b2 l vclo sim ot1 (TauF t2)
    (* info_flow protecting coinductive constructors *)
    | EqVisPriv {A} (e : E A) k1 k2 (SECCHECK : leq (priv A e) l) : 
        ((forall a, vclo sim (k1 a) (k2 a) : Prop)) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (VisF e k2)
    | EqVisUnPrivTauLCo {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim (k1 a) t2) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (TauF t2)
    | EqVisUnPrivTauRCo {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim t1 (k2 a)) -> secure_eqitF b1 b2 l vclo sim (TauF t1) (VisF e k2)
    | EqVisUnPrivVisCo {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l) :
        (forall a b, vclo sim (k1 a) (k2 b)) -> secure_eqitF b1 b2 l vclo sim (VisF e1 k1) (VisF e2 k2)
    (* info_flow protecting inductive constructors *)
    | EqVisUnPrivLInd {A} (e : E A) k1 t2 (CHECK : b1) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe (k1 a)) (observe t2) ) ->
        secure_eqitF b1 b2 l vclo sim (VisF e k1) (observe t2)
    | EqVisUnPrivRLInd {A} (e : E A) t1 k2 (CHECK : b2) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe t1) (observe (k2 a) )) ->
        secure_eqitF b1 b2 l vclo sim (observe t1) (VisF e k2)
    (*| (halt : E A) k (Hempty : empty A) (r) : forall r', RR r' r -> eqit_secure (Vis halt k) (Ret r)

     *)
  .

  Hint Constructors secure_eqitF : core.

  Definition secure_eqit_ (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => secure_eqitF b1 b2 l vclo sim (observe t1) (observe t2).

  Hint Unfold secure_eqit_ : core.

  Lemma secure_eqitF_mono b1 b2 l x0 x1 vclo vclo' sim sim'
        (IN: secure_eqitF b1 b2 l vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    secure_eqitF b1 b2 l vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma secure_eqit_mono b1 b2 l vclo (MON: monotone2 vclo) : monotone2 (secure_eqit_ b1 b2 l vclo).
  Proof.
    do 2 red. intros; eapply secure_eqitF_mono; eauto.
  Qed.

  Hint Resolve secure_eqit_mono : paco.

  Definition eqit_secure b1 b2 l := paco2 (secure_eqit_ b1 b2 l id) bot2.

  (* want and eqitC_secure which could help prove some interesting stuff

   *)


  (*
    Note that this is not reflexive (think it is symmetric and transitive) 
    Suppose SecureFlip : E bool has privilege 1 and trigger SecureFlip is 
    observed at privilege 0. We end to prove eqit_secure false false 0 of it 
    requires us to show forall a b, eqit_secure false false 0 (Ret a) (Ret b)
    this is false, suppose a = true and b = false and the relation is equality

   *)


End SecureUntimed.

Definition NatPreorder : Preorder :=
  {|
  L := nat;
  leq := fun n m => n <= m
  |}.

Section SecureUntimedUnReflexive.
  
  Variant NonDet : Type -> Type :=
    | SecureFlip : NonDet bool
    | PublicOut : NonDet unit
    | Halt : NonDet void

. 

  Definition priv_counter : forall A, NonDet A -> nat :=
    fun _ e =>
      match e with
      | SecureFlip => 1
      | PublicOut => 0 
      | Halt => 10
      end.
  

  Variant Exc : Type -> Type :=
    Throw : Exc void.

  Definition refl_counter : itree NonDet bool := trigger SecureFlip.

  Lemma refl_counter_counter : ~ eqit_secure NatPreorder priv_counter eq true true 0 refl_counter refl_counter.
    Proof.
      intro Hcontra. punfold Hcontra; try eapply secure_eqit_mono; eauto.
      red in Hcontra. cbn in *. inv Hcontra; ITrace.inj_existT; subst.
      - cbv in SECCHECK. inv SECCHECK.
      - specialize (H0 true false). pclearbot. pinversion H0; try eapply secure_eqit_mono; eauto.
        discriminate.
      - rewrite H3 in H0. clear H3. specialize (H0 true). cbn in *.
        inv H0; ITrace.inj_existT; subst. specialize (H2 false). rewrite H in H2.
        inv H2. discriminate.
      -  rewrite H in H0. injection H0; intros; ITrace.inj_existT; subst; ITrace.inj_existT; subst.
         specialize (H1 true). cbn in *. inv H1; ITrace.inj_existT; subst; ITrace.inj_existT; subst.
         rewrite H6 in H3. specialize (H3 false). cbn in *. inv H3; discriminate.
    Qed.


    Lemma halt_eq_all : forall R (t : itree NonDet R) k , eqit_secure NatPreorder priv_counter eq true true 0 (Vis Halt k) t.
    Proof.
      intros. pfold. red. cbn. constructor; auto; try intros; try contradiction.
      intro Hc; inv Hc.
    Qed.
    (*transitivity problems in presence of E void *)
    Definition refl_counter2 : itree NonDet unit := ITree.bind refl_counter (fun b : bool => if b then Ret tt else trigger PublicOut).

    Lemma refl_counter2_counter : ~ eqit_secure NatPreorder priv_counter eq true true 0 refl_counter2 refl_counter2.
      Proof.
        Admitted.

End SecureUntimedUnReflexive.

Section SecureTimed.

  Variant TimedEv (E : Type -> Type) : Type -> Type :=
    | TE {A : Type} (e : E A) (n : nat) : TimedEv E A.

  Fixpoint handle_timed_aux {E A} (e : E A) (n : nat) : itree E A :=
    match n with
    | 0 => Vis e (fun a => Ret a)
    | S m => Tau (handle_timed_aux e m) end.

  Definition handle_timed {E A} (e : TimedEv E A) : itree E A :=
    match e with TE _ e' a => handle_timed_aux e' a end.


End SecureTime.
