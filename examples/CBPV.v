(* Example interpreting CBPV language 
   using interaction trees.

   On one hand, this interpretation is really cool because it 
   identifies the CBPV computation type 'F A' with 'itree'.

   On the other hand, this interpretation is rather trivial 
   because there are no effects in pure CBPV.
 *)

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

Section SYNTAX.

  Inductive vtyp :=
  | One
  | Nat
  | Prod (A1:vtyp) (A2:vtyp)
  | U (B:ctyp)
  with ctyp :=
  | Arr (A:vtyp) (B:ctyp)
  | Tensor (B1:ctyp) (B2:ctyp)
  | F (A:vtyp).

  Variable V : vtyp -> Type.  (* PHOAS variables *)

  Inductive val : vtyp -> Type :=
  | Unit : val One
  | Lit (n:nat) : val Nat
  | Var : forall (A:vtyp), V A -> val A
  | Pair : forall (A1 A2:vtyp), val A1 -> val A2 -> val (Prod A1 A2)
  | Thunk : forall (B:ctyp), comp B -> val (U B)
  with comp : ctyp -> Type :=
  | Val : forall (A:vtyp), val A -> comp (F A)       (* aka return *)
  | Let : forall (A:vtyp) (B:ctyp) (m : comp (F A))  (* aka bind *)
                 (body : (V A -> comp B)), comp B
  | Abs : forall A B
                 (body : V A -> comp B), comp (Arr A B)
  | App : forall A B 
                 (m : comp (Arr A B)) (v : val A), comp B
  | Opr : forall (v1 : val Nat) (v2 : val Nat), comp (F Nat)
  | Split : forall (A1 A2:vtyp) (B:ctyp), 
      val (Prod A1 A2) -> (V A1 -> V A2 -> comp B) -> comp B
  | Tup : forall B1 B2, comp B1 -> comp B2 -> comp (Tensor B1 B2)
  | Fst : forall B1 B2, comp (Tensor B1 B2) -> comp B1
  | Snd : forall B1 B2, comp (Tensor B1 B2) -> comp B2
  | Force : forall (B:ctyp), val (U B) -> comp B
  .

  Fixpoint open_val (G : list vtyp) (A:vtyp) : Type :=
    match G with
    | [] => val A
    | A1::As =>  V A1 -> (open_val As A)
    end.
  Fixpoint open_comp (G : list vtyp) (B:ctyp) : Type :=
    match G with
    | [] => comp B
    | A::As =>  V A -> (open_comp As B)
    end.


End SYNTAX.

Definition ValTerm (G : list vtyp) (u:vtyp) := 
  forall (V : vtyp -> Type), open_val V G u.
Definition CompTerm (G : list vtyp) (u:ctyp) := 
  forall (V : vtyp -> Type), open_comp V G u.

Arguments Unit {V}.
Arguments Lit {V}.
Arguments Var {V A}.
Arguments App {V A B}.
Arguments Abs {V A B}.
Arguments Thunk {V B}.
Arguments Force {V B}.
Arguments Val {V A}.
Arguments Let {V A B}.
Arguments Opr {V}.
Arguments Pair {V A1 A2}.
Arguments Split {V A1 A2 B}.
Arguments Tup {V B1 B2}.
Arguments Fst {V B1 B2}.
Arguments Snd {V B1 B2}.

Section DENOTATION.

  Fixpoint denote_vtyp E (A:vtyp) : Type :=
    match A with
    | One => Datatypes.unit
    | Nat => nat
    | Prod A1 A2 => denote_vtyp E A1 * denote_vtyp E A2 
    | U B => denote_ctyp E B
    end
  with denote_ctyp E (B:ctyp) : Type :=
    match B with 
    | F A => itree E (denote_vtyp E A)
    | Arr A B => (denote_vtyp E A) -> (denote_ctyp E B)
    | Tensor B1 B2 => denote_ctyp E B1 * denote_ctyp E B2
    end.


  Fixpoint ctyp_bind {A} {B : ctyp}{ E }
    (m : denote_ctyp E (F A)) : (denote_vtyp E A -> denote_ctyp E B) -> denote_ctyp E B :=
    match B return (denote_vtyp E A -> denote_ctyp E B) -> denote_ctyp E B with 
    | F A2 => fun k => ITree.bind m k
    | Arr A2 B1 => fun k => let KK := @ctyp_bind A B1 E m in 
                            fun v => KK (fun x => (k x v))
    | Tensor B1 B2 => fun k => let K1 := @ctyp_bind A B1 E m in 
                               let K2 := @ctyp_bind A B2 E m in 
                               ( K1 (fun x => fst (k x)) , K2 (fun x => snd (k x)))
    end.

  Notation "x <- t1 ;; t2" := (ctyp_bind t1 (fun x => t2)).

  Fixpoint denote_closed_val {E} {A:vtyp} (v : val (denote_vtyp E) A)
    : denote_vtyp E A :=
    match v in val _ A return denote_vtyp E A with
    | Unit => tt
    | Lit n => n
    | Var x => x
    | Pair v1 v2 => (denote_closed_val v1, denote_closed_val v2)
    | Thunk m => denote_closed_comp m
    end with
  denote_closed_comp {E} {B:ctyp} 
    (m : comp (denote_vtyp E) B) : denote_ctyp E B :=
    match m in comp _ B return denote_ctyp E B with
    | Val v      => ret (denote_closed_val v)
    | Let m body => x <- (denote_closed_comp m) ;; denote_closed_comp (body x)
    | Force v    => denote_closed_val v
    | App m1 m2 => (denote_closed_comp m1) (denote_closed_val m2) 
    | Abs body  => fun x => denote_closed_comp (body x)
    | Opr v1 v2 => Ret (denote_closed_val v1 + denote_closed_val v2)
    | Split v m => let '(x1,x2) := denote_closed_val v in
                   denote_closed_comp (m x1 x2) 
    | Tup m1 m2 => (denote_closed_comp m1, denote_closed_comp m2)
    | Fst m => fst (denote_closed_comp m)
    | Snd m => snd (denote_closed_comp m)
   end.

  Fixpoint denotation_val_vtyp (V:vtyp -> Type) 
    (G : list vtyp) (A:vtyp) :=
    match G with
    | [] => V A
    | t::ts => (V t) -> denotation_val_vtyp V ts A
    end.

  Fixpoint denotation_comp_ctyp (V:vtyp -> Type)(C:ctyp -> Type) (G : list vtyp) (B:ctyp) :=
    match G with
    | [] => (C B)
    | t::ts => (V t) -> denotation_comp_ctyp V C ts B
    end.


Program Fixpoint denote_rec_val
          (V:vtyp -> Type) 
          (base : forall A (v : val V A), V A)
          (G: list vtyp) (u:vtyp) (m : open_val V G u) : denotation_val_vtyp V G u :=
    match G with
    | [] => base u _
    | t::ts => fun (x : V t) => denote_rec_val V base ts u _
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
          (V:vtyp -> Type) (C:ctyp -> Type) 
          (base : forall B (c : comp V B), (C B))
          (G: list vtyp) (B:ctyp) (m : open_comp V G B) : 
  denotation_comp_ctyp V C G B :=

    match G with
    | [] => base B _
    | t::ts => fun (x : V t) => denote_rec_comp V C base ts B _
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

  Program Definition denote_val E (G : list vtyp) (A:vtyp) 
    (m : ValTerm G A)
    : denotation_val_vtyp (denote_vtyp E) G A :=
    denote_rec_val (denote_vtyp E) (@denote_closed_val E) G A _.
  Next Obligation.
    unfold ValTerm in m.
    specialize (m (denote_vtyp E)).
    exact m.
  Defined.

  Program Definition denote_comp E (G : list vtyp) (B:ctyp) 
    (m : CompTerm G B)
    : denotation_comp_ctyp (denote_vtyp E) (denote_ctyp E) G B :=
    denote_rec_comp (denote_vtyp E) (denote_ctyp E) (@denote_closed_comp E) G B _.
  Next Obligation.
    unfold CompTerm in m.
    specialize (m (denote_vtyp E)).
    exact m.
  Defined.


End DENOTATION.


Definition id_tm : CompTerm [] (Arr Nat (F Nat)) :=
  fun V => Abs (fun x => Val (Var x)).

Definition example : CompTerm [] (F Nat) :=
  fun V => App (id_tm V) (Lit 3).

Lemma example_equiv E : (denote_comp E [] (F Nat) example) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

Definition twice : CompTerm [] (Arr (U (Arr Nat (F Nat))) (Arr Nat (F Nat))) :=
  fun V => Abs (fun f => 
                  Abs (fun x => 
                         Let (App (Force (Var f)) (Var x))
                           (fun v => App (Force (Var f)) (Var v)))).

Definition example2 : CompTerm [] (F Nat) :=
  fun V => App (App (twice V) (Thunk (id_tm V))) (Lit 3).

Lemma big_example_equiv E : (denote_comp E [] (F Nat) example2) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

Definition add_2_tm : CompTerm [] (Arr Nat (F Nat)) :=
  fun V => Abs (fun x => (Opr (Var x) (Lit 2))).

Definition example3 : CompTerm [] (F Nat) :=
  fun V => App (App (twice V) (Thunk (add_2_tm V))) (Lit 3).

Lemma big_example2_equiv E : (denote_comp E [] (F Nat) example3) ≈ Ret 7.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

