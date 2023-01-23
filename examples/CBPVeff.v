(* Example interpreting CBPV language 
   using interaction trees *)

From Coq Require Import
     Arith
     Lia
     List.

From ExtLib Require Import
     Monad
     Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts.

Import Basics.Basics.Monads.
Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.

Require Import Coq.MSets.MSets.

(* Example CBPV syntactic effect *)
Inductive eff_names := 
  | eff_state : eff_names.

Inductive eff := 
  eff_get | eff_put.

Definition get_eff_name e :=
  match e with
  | eff_get => eff_state
  | eff_put => eff_state
  end.


(* 
Module Type EffectNamesSig. 
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_dec : 
    forall (o1: t) (o2: t), { o1 = o2 } + { ~ (o1 = o2) }.
End EffectNamesSig.
*)


Module EffectNames.
  Definition t := eff_names.
  Definition eq : t -> t -> Prop  := Logic.eq.
  Lemma eq_dec : 
    forall (o1: t) (o2: t), { o1 = o2 } + { ~ (o1 = o2) }.
  Proof. decide equality. Defined.
End EffectNames.
Module UDT_Effect := Coq.Structures.Equalities.Make_UDT(EffectNames).
Module EffectSet := MSetWeakList.Make(UDT_Effect). 

Definition eff_name : Type := EffectNames.t.
Definition effects : Type := EffectSet.t.

Definition bot : effects := EffectSet.empty.
Definition single : eff_name -> effects := EffectSet.singleton.
Definition plus : effects -> effects -> effects := EffectSet.union.
Definition sub : effects -> effects -> Prop := EffectSet.Subset.

Inductive vtyp : Type :=
| One
| Nat
| Prod (A1:vtyp) (A2:vtyp)
| U (E : effects) (B:ctyp)
with ctyp : Type :=
| F (A:vtyp)
| Arr (A:vtyp) (B:ctyp).


Definition eff_ctyp e :=
  match e with 
  | eff_get => F Nat
  | eff_put => Arr Nat (F One)
  end.

Section Terms.
  
  Variable V : vtyp -> Type.  (* PHOAS variables *)

  Inductive val : vtyp -> Type :=
  | Unit : val One
  | Lit (n:nat) : val Nat
  | Var : forall (A:vtyp), V A -> val A
  | Pair : forall (A1 A2:vtyp), val A1 -> val A2 -> val (Prod A1 A2)
  | Thunk : forall e (B:ctyp), comp e B -> val (U e B)

  with comp : effects -> ctyp -> Type :=
  | Val : forall (A:vtyp), val A -> comp bot (F A)
     (* Should Itree's allow different E1 +' E2 here? *)
  | Let : forall E (A:vtyp) (B:ctyp) 
      (m : comp E (F A)) (body : (V A -> comp E B)), comp E B
  | Force : forall e (B:ctyp),
      val (U e B) -> comp e B
  | App : forall e A B 
            (m : comp e (Arr A B)) (v : val A), comp e B
  | Abs : forall e A B
            (body : V A -> comp e B), comp e (Arr A B)
  | Opr : forall (v1 : val Nat) (v2 : val Nat), comp bot (F Nat)
  | Split : forall e (A1 A2:vtyp) (B:ctyp), 
      val (Prod A1 A2) -> (V A1 -> V A2 -> comp e B) -> comp e B
  | Trigger : forall (e : eff), comp (single (get_eff_name e)) (eff_ctyp e)
  | Sub : forall E F B, sub E F -> comp E B -> comp F B
  .

  Fixpoint open_val (G : list vtyp) (A:vtyp) : Type :=
    match G with
    | [] => val A
    | A1::As =>  V A1 -> (open_val As A)
    end.
  Fixpoint open_comp (G : list vtyp) e (B:ctyp) : Type :=
    match G with
    | [] => comp e B
    | A::As =>  V A -> (open_comp As e B)
    end.


End Terms.

Definition ValTerm (G : list vtyp) (u:vtyp) := 
  forall (V : vtyp -> Type), open_val V G u.
Definition CompTerm (G : list vtyp) e (u:ctyp) := 
  forall (V : vtyp -> Type), open_comp V G e u.

Arguments Unit {V}.
Arguments Lit {V}.
Arguments Var {V A}.
Arguments App {V e A B}.
Arguments Abs {V e A B}.
Arguments Thunk {V e B}.
Arguments Force {V e B}.
Arguments Val {V A}.
Arguments Let {V E A B}.
Arguments Opr {V}.
Arguments Pair {V A1 A2}.
Arguments Split {V e A1 A2 B}.
Arguments Trigger {V}.
Arguments Sub {V E F B}.


From ITree Require Import Events.State.

Section DENOTATION.

Definition denote_eff_type (e : eff_name) : Type -> Type :=
  match e with 
  | eff_state => stateE nat
  end.


Fixpoint denote_list_eff (es : list eff_name) : Type -> Type :=
  match es with 
  | nil => void1
  | cons e es => denote_eff_type e +' denote_list_eff es
  end.

Definition denote_effects (es : effects) := 
  denote_list_eff (EffectSet.elements es).

Fixpoint denote_vtyp (A:vtyp) : Type :=
  match A with
  | One => Datatypes.unit
  | Nat => nat
  | Prod A1 A2 => denote_vtyp A1 * denote_vtyp A2 
  | U e B => denote_ctyp (denote_effects e) B
  end
with 
denote_ctyp E (B:ctyp) : Type :=
  match B with 
  | F A => itree E (denote_vtyp A)
  | Arr A B => (denote_vtyp A) -> (denote_ctyp E B)
  end.


Definition denote_eff (e : eff) : 
  denote_ctyp (denote_eff_type (get_eff_name e)) (eff_ctyp e) :=
  match e return denote_ctyp (denote_eff_type (get_eff_name e)) (eff_ctyp e) with 
  | eff_get => ITree.trigger (@Get nat)
  | eff_put => fun x : nat => ITree.trigger (Put nat x)
  end.

(*
ITree.bind
     : itree ?E ?T -> (?T -> itree ?E ?U) -> itree ?E ?U
*)

Fixpoint ctyp_bind {A} {B : ctyp}{ e }
   (m : denote_ctyp e (F A)) : (denote_vtyp A -> denote_ctyp e B) -> denote_ctyp e B :=
   match B return (denote_vtyp A -> denote_ctyp e B) -> denote_ctyp e B with 
   | F A2 => fun k => ITree.bind m k
   | Arr A2 B1 => fun k => let KK := @ctyp_bind A B1 e m in 
                           fun v => KK (fun x => (k x v))
end.

Lemma sub_denote_effects {e f} : sub e f -> (denote_effects e) -< (denote_effects f).
Proof.
  intros.
Admitted.

Lemma subevent_itree {E F A} : E -< F -> itree E A -> itree F A.
Proof.
  intros.
  eapply translate; eauto.
Qed. 

Lemma subevent_denote_ctyp {E F B} : E -< F -> denote_ctyp E B -> denote_ctyp F B.
Proof.
  intros.
  induction B.
  - simpl in *.
    eapply subevent_itree; eauto.
  - simpl in *.
    intros x. eauto.
Qed.

Lemma eq_eff : forall eff, denote_eff_type eff -< denote_effects (single eff).
Proof.
  intros.
  unfold single. unfold denote_effects. simpl.
  unfold ReSum. unfold IFun.
  intros. 
  eapply inl1.
  auto.
Qed.

Fixpoint denote_closed_val {A:vtyp} (v : val (denote_vtyp) A)
    : denote_vtyp A :=
    match v in val _ A return denote_vtyp A with
    | Unit => tt
    | Lit n => n
    | Var x => x
    | Pair v1 v2 => (denote_closed_val v1, denote_closed_val v2)
    | Thunk m => denote_closed_comp m
    end with
  denote_closed_comp {e:effects} {B:ctyp} 
    (m : comp (denote_vtyp) e B) : denote_ctyp (denote_effects e) B :=
    match m in comp _ e B
          return denote_ctyp (denote_effects e) B with
    | Val v => ret (denote_closed_val v)
    | Let m body => ctyp_bind (denote_closed_comp m) 
                    (fun x => 
                    (denote_closed_comp (body x)))
    | Force v => denote_closed_val v
    | Abs body => fun x => denote_closed_comp (body x)
    | App m1 m2 => (denote_closed_comp m1) (denote_closed_val m2)
    | Opr v1 v2 => Ret (denote_closed_val v1 + denote_closed_val v2)
    | Split v m => let '(x1,x2) := denote_closed_val v in
                   denote_closed_comp (m x1 x2) 
    | Trigger eff => subevent_denote_ctyp (eq_eff (get_eff_name eff)) (denote_eff eff)
    | Sub s m1 => subevent_denote_ctyp (sub_denote_effects s) (denote_closed_comp m1)
   end.


Fixpoint denotation_val_vtyp (V:vtyp -> Type) 
  (G : list vtyp) (A:vtyp) :=
  match G with
  | [] => V A
  | A1::As => (V A1) -> denotation_val_vtyp V As A
  end.

Fixpoint denotation_comp_ctyp (V:vtyp -> Type) (C:ctyp -> Type) 
  (G : list vtyp) (B:ctyp) :=
  match G with
  | [] => C B
  | A::As => (V A) -> denotation_comp_ctyp V C As B
  end.



Program Fixpoint denote_rec_val
          (V:vtyp -> Type) 
          (base : forall A (v : val V A), V A)
          (G: list vtyp) (A:vtyp) (m : open_val V G A) :
  denotation_val_vtyp V G A :=
    match G with
    | [] => base A _
    | t::ts => fun (x : V t) => denote_rec_val V base ts A _
    end.
  Next Obligation.
    simpl in m.
    exact m.
  Defined.
  Next Obligation.
    simpl in m.
    apply m in x.
    exact x.
  Defined.

Program Fixpoint denote_rec_comp
          (V:vtyp -> Type) (C:ctyp -> Type) e
          (base : forall B (c : comp V e B), C B)
          (G: list vtyp) (B:ctyp) (m : open_comp V G e B) : 
  denotation_comp_ctyp V C G B :=
  match G with
  | [] => base B _
  | t::ts => fun (x : V t) => denote_rec_comp V C e base ts B _
  end.
  Next Obligation.
    simpl in m.
    exact m.
  Defined.
  Next Obligation.
    simpl in m.
    apply m in x.
    exact x.
  Defined.


  Program Definition denote_val (G : list vtyp) (A:vtyp) 
    (m : ValTerm G A)
    : denotation_val_vtyp denote_vtyp G A :=
    denote_rec_val denote_vtyp (@denote_closed_val) G A _.
  Next Obligation.
    unfold ValTerm in m.
    specialize (m (denote_vtyp)).
    exact m.
  Defined.

  Program Definition denote_comp (G : list vtyp) e (B:ctyp) 
    (m : CompTerm G e B)
    : denotation_comp_ctyp denote_vtyp (denote_ctyp (denote_effects e)) G B :=
    denote_rec_comp denote_vtyp (denote_ctyp (denote_effects e)) e 
      (@denote_closed_comp e) G B _.
  Next Obligation.
    unfold CompTerm in m.
    specialize (m (denote_vtyp)).
    exact m.
  Defined.

End DENOTATION.


Definition id_tm : CompTerm [] bot (Arr Nat (F Nat)) :=
  fun V => Abs (fun x => Val (Var x)).


Definition get_tm : CompTerm [] (single eff_state) (Arr Nat (F Nat)) :=
  fun V => Abs (fun x => Trigger eff_get).


Definition example : CompTerm [] bot (F Nat) :=
  fun V => App (id_tm V) (Lit 3).

Lemma example_equiv : (denote_comp [] bot (F Nat) example) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

Definition twice : CompTerm [] bot (Arr (U bot (Arr Nat (F Nat))) (Arr Nat (F Nat))) :=
  fun V => Abs (fun f => 
                  Abs (fun x => 
                         Let (App (Force (Var f)) (Var x))
                           (fun v => App (Force (Var f)) (Var v)))).

Definition example2 : CompTerm [] bot (F Nat) :=
  fun V => App (App (twice V) (Thunk (id_tm V))) (Lit 3).

Lemma big_example_equiv : (denote_comp [] bot (F Nat) example2) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

Definition add_2_tm : CompTerm [] bot (Arr Nat (F Nat)) :=
  fun V => Abs (fun x => (Opr (Var x) (Lit 2))).

Definition example3 : CompTerm [] bot (F Nat) :=
  fun V => App (App (twice V) (Thunk (add_2_tm V))) (Lit 3).

Lemma big_example2_equiv : (denote_comp [] bot (F Nat) example3) ≈ Ret 7.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

