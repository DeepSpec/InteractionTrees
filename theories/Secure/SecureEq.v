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
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Class Preorder :=
  {
    L : Type;
    leq : L -> L -> Prop;
  }.

(* will need more propositional constrainst on Preorders *)

Section SecureUntimed.
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  Context {Label : Preorder}.
  Context (priv : forall A, E A -> L).

  Inductive secure_eqitF (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop := 

    (* eqitF constructors *)
    | secEqRet r1 r2 : RR r1 r2 -> secure_eqitF b1 b2 l vclo sim (RetF r1) (RetF r2)
    | secEqTau t1 t2 : sim t1 t2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) (TauF t2)
    | secEqTauL t1 ot2 (CHECK : b1) : secure_eqitF b1 b2 l vclo sim (observe t1) ot2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) ot2
    | secEqTauR ot1 t2 (CHECK : b2) : secure_eqitF b1 b2 l vclo sim ot1 (observe t2) -> secure_eqitF b1 b2 l vclo sim ot1 (TauF t2)
    (* info_flow protecting coinductive constructors *)
    | EqVisPriv {A} (e : E A) k1 k2 (SECCHECK : leq (priv A e) l) : 
        ((forall a, vclo sim (k1 a) (k2 a) : Prop)) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (VisF e k2)
    | EqVisUnPrivLCo {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim (k1 a) t2) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (TauF t2)
    | EqVisUnPrivRCo {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim t1 (k2 a)) -> secure_eqitF b1 b2 l vclo sim (TauF t1) (VisF e k2)
    (* info_flow protecting inductive constructors *)
    | EqVisUnPrivLInd {A} (e : E A) k1 t2 (CHECK : b1) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe (k1 a)) (observe t2) ) ->
        secure_eqitF b1 b2 l vclo sim (VisF e k1) (observe t2)
    | EqVisUnPrivRLInd {A} (e : E A) t1 k2 (CHECK : b2) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe t1) (observe (k2 a) )) ->
        secure_eqitF b1 b2 l vclo sim (observe t1) (VisF e k2)
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


End SecureUntimed.

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
