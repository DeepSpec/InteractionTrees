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

Section SYNTAX.

  Inductive vtyp :=
  | Base
  | U (B:ctyp)
  with ctyp :=
  | F (A:vtyp)
  | Arr (A:vtyp) (B:ctyp).

  Variable V : vtyp -> Type.  (* PHOAS variables *)

  Inductive val : vtyp -> Type :=
  | Lit (n:nat) : val Base
  | Var : forall (A:vtyp), V A -> val A
  | Thk : forall (B:ctyp), comp B -> val (U B)
  with comp : ctyp -> Type :=
  | Val : forall (A:vtyp), val A -> comp (F A)
  | Let : forall (A:vtyp) (B:ctyp) 
      (m : comp (F A)) (body : (V A -> comp B)), comp B
  | Frc : forall (B:ctyp),
      val (U B) -> comp B
  | App : forall A B 
                 (m : comp (Arr A B)) (v : val A), comp B
  | Abs : forall A B
                 (body : V A -> comp B), comp (Arr A B)
  | Opr : forall (v1 : val Base) (v2 : val Base), comp (F Base)
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

Arguments Lit {V}.
Arguments Var {V A}.
Arguments App {V A B}.
Arguments Abs {V A B}.
Arguments Thk {V B}.
Arguments Frc {V B}.
Arguments Val {V A}.
Arguments Let {V A B}.
Arguments Opr {V}.

Section DENOTATION.
  Fixpoint denote_vtyp E (A:vtyp) : Type :=
    match A with
    | Base => nat
    | U B => itree E (denote_ctyp E B)
    end
  with denote_ctyp E (B:ctyp) : Type :=
    match B with 
    | F A => denote_vtyp E A
    | Arr A B => (denote_vtyp E A) -> itree E (denote_ctyp E B)
    end.



  Fixpoint denote_closed_val {E} {A:vtyp} (v : val (denote_vtyp E) A) : denote_vtyp E A :=
    match v in val _ A return denote_vtyp E A with
    | Lit n => n
    | Var x => x
    | Thk m => denote_closed_comp m
    end with
  denote_closed_comp {E} {B:ctyp} 
    (m : comp (denote_vtyp E) B) : itree E (denote_ctyp E B) :=
    match m in comp _ B return itree E (denote_ctyp E B) with
    | Val v => ret (denote_closed_val v)
    | Let m body => x <- denote_closed_comp m ;;
                    denote_closed_comp (body x)
    | Frc v => denote_closed_val v
    | App m1 m2 => f <- (denote_closed_comp m1) ;;
                   ans <- f (denote_closed_val m2) ;;
                   ret ans
    | Abs body => ret (fun x => denote_closed_comp (body x))
    | Opr v1 v2 => Ret (denote_closed_val v1 + denote_closed_val v2)
    end.

  Fixpoint denotation_val_vtyp (V:vtyp -> Type) 
    (G : list vtyp) (A:vtyp) :=
    match G with
    | [] => V A
    | t::ts => (V t) -> denotation_val_vtyp V ts A
    end.

  Fixpoint denotation_comp_ctyp E (V:vtyp -> Type)(C:ctyp -> Type) (G : list vtyp) (B:ctyp) :=
    match G with
    | [] => itree E (C B)
    | t::ts => (V t) -> denotation_comp_ctyp E V C ts B
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
          (V:vtyp -> Type) (C:ctyp -> Type) E
          (base : forall B (c : comp V B), itree E (C B))
          (G: list vtyp) (B:ctyp) (m : open_comp V G B) : denotation_comp_ctyp E V C G B :=

    match G with
    | [] => base B _
    | t::ts => fun (x : V t) => denote_rec_comp V C E base ts B _
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
    : denotation_comp_ctyp E (denote_vtyp E) (denote_ctyp E) G B :=
    denote_rec_comp (denote_vtyp E) (denote_ctyp E) E (@denote_closed_comp E) G B _.
  Next Obligation.
    unfold CompTerm in m.
    specialize (m (denote_vtyp E)).
    exact m.
  Defined.


End DENOTATION.


Definition id_tm : CompTerm [] (Arr Base (F Base)) :=
  fun V => Abs (fun x => Val (Var x)).

Definition example : CompTerm [] (F Base) :=
  fun V => App (id_tm V) (Lit 3).

Lemma example_equiv E : (denote_comp E [] (F Base) example) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

Definition twice : CompTerm [] (Arr (U (Arr Base (F Base))) (Arr Base (F Base))) :=
  fun V => Abs (fun f => 
                  Abs (fun x => 
                         Let (App (Frc (Var f)) (Var x))
                           (fun v => App (Frc (Var f)) (Var v)))).

Definition example2 : CompTerm [] (F Base) :=
  fun V => App (App (twice V) (Thk (id_tm V))) (Lit 3).

Lemma big_example_equiv E : (denote_comp E [] (F Base) example2) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

Definition add_2_tm : CompTerm [] (Arr Base (F Base)) :=
  fun V => Abs (fun x => (Opr (Var x) (Lit 2))).

Definition example3 : CompTerm [] (F Base) :=
  fun V => App (App (twice V) (Thk (add_2_tm V))) (Lit 3).

Lemma big_example2_equiv E : (denote_comp E [] (F Base) example3) ≈ Ret 7.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

