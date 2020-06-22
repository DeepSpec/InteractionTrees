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
     Eq
     Eq.Eq
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts.

Import Basics.Basics.Monads.
Import ListNotations.
Import ITreeNotations.

Require Import List.
Import ListNotations.


Section SYNTAX.

  Inductive typ :=
  | Base
  | Arr (s:typ) (t:typ).

  Variable V : typ -> Type.  (* PHOAS variables *)
  Inductive tm : typ -> Type :=
  | Lit (n:nat) : tm Base
  | Var : forall (t:typ), V t -> tm t
  | App : forall t1 t2 (m1 : tm (Arr t1 t2)) (m2 : tm t1), tm t2
  | Lam : forall t1 t2 (body : V t1 -> tm t2), tm (Arr t1 t2)
  | Opr : forall (m1 : tm Base) (m2 : tm Base), tm Base
  .

  Fixpoint open_tm (G : list typ) (u:typ) : Type :=
    match G with
    | [] => tm u
    | t::ts =>  V t -> (open_tm ts u)
    end.
  
End SYNTAX.

Definition Term (G : list typ) (u:typ) := forall (V : typ -> Type), open_tm V G u.

Arguments Lit {V}.
Arguments Var {V t}.
Arguments App {V t1 t2}.
Arguments Lam {V t1 t2}.
Arguments Opr {V}.

Section DENOTATION.
  Fixpoint denote_typ E (t:typ) : Type :=
    match t with
    | Base => nat
    | Arr s t => (denote_typ E s) -> itree E (denote_typ E t)
    end.

  Fixpoint denotation_tm_typ E (V:typ -> Type) (G : list typ) (u:typ) :=
    match G with
    | [] => itree E (V u)
    | t::ts => (V t) -> denotation_tm_typ E V ts u
    end.

  Fixpoint denote_closed_term {E} {u:typ} (m : tm (denote_typ E) u) : itree E (denote_typ E u) :=
    match m with
    | Lit n => Ret n
    | Var x => Ret x
    | App m1 m2 => f <- (denote_closed_term m1) ;;
                  x <- (denote_closed_term m2) ;;
                  ans <- f x ;;
                  ret ans
    | Lam body => ret (fun x => denote_closed_term (body x))
    | Opr m1 m2 => x <- (denote_closed_term m1) ;;
                  y <- (denote_closed_term m2) ;;
                  Ret (x + y)  
    end.
  
  Program Fixpoint denote_rec
          (V:typ -> Type) E
          (base : forall u (m : tm V u), itree E (V u))
          (G: list typ) (u:typ) (m : open_tm V G u) : denotation_tm_typ E V G u :=
    match G with
    | [] => base u _
    | t::ts => fun (x : V t) => denote_rec V E base ts u _
    end.
  Next Obligation.
    simpl in m.
    exact m.
  Defined.
  Next Obligation.
    unfold Term in m.
    simpl in m.
    apply m in x.
    exact x.
  Defined.  
  
  Program Definition denote E (G : list typ) (u:typ) (m : Term G u)
    : denotation_tm_typ E (denote_typ E) G u :=
    denote_rec (denote_typ E) E (@denote_closed_term E) G u _.
  Next Obligation.
    unfold Term in m.
    specialize (m (denote_typ E)).
    exact m.
  Defined.

End DENOTATION.    

  
Definition id_tm : Term [] (Arr Base Base) :=
  fun V => Lam (fun x => Var x).

Definition example : Term [] Base :=
  fun V => App (id_tm V) (Lit 3).

Lemma example_equiv E : (denote E [] Base example) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

Definition twice : Term [] (Arr (Arr Base Base) (Arr Base Base)) :=
  fun V => Lam (fun f => Lam (fun x => App (Var f) (App (Var f) (Var x)))).

Definition example2 : Term [] Base :=
  fun V => App (App (twice V) (id_tm V)) (Lit 3).

Lemma big_example_equiv E : (denote E [] Base example2) ≈ Ret 3.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.  

Definition add_2_tm : Term [] (Arr Base Base) :=
  fun V => Lam (fun x => (Opr (Var x) (Lit 2))).

Definition example3 : Term [] Base :=
  fun V => App (App (twice V) (add_2_tm V)) (Lit 3).

Lemma big_example2_equiv E : (denote E [] Base example3) ≈ Ret 7.
Proof.
  cbn.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

