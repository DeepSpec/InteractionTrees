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


Inductive typ :=
| Base
| Arr (s:typ) (t:typ).

Fixpoint denote_typ E (t:typ) : Type :=
  match t with
  | Base => nat
  | Arr s t => (denote_typ E s) -> itree E (denote_typ E t)
  end.


Inductive tm (V : typ -> Type) : typ -> Type :=
  | Lit (n:nat) : tm V Base
  | Var : forall (t:typ), V t -> tm V t
  | App : forall t1 t2 (m1 : tm V (Arr t1 t2)) (m2 : tm V t1), tm V t2
  | Lam : forall t1 t2 (body : V t1 -> tm V t2), tm V (Arr t1 t2)
  | Opr : forall (m1 : tm V Base) (m2 : tm V Base), tm V Base
(*  | Fix : forall t1 t2 (body : V (Arr t1 t2) -> V t1 -> tm V t2), tm V (Arr t1 t2) *)
.
Arguments Lit {V}.
Arguments Var {V t}.
Arguments App {V t1 t2}.
Arguments Lam {V t1 t2}.
Arguments Opr {V}.
(* Arguments Fix {V t1 t2}. *)

Fixpoint open_tm (V:typ -> Type) (G : list typ) (u:typ) : Type :=
  match G with
  | [] => tm V u
  | t::ts =>  V t -> (open_tm V ts u)
  end.
Definition Term (G : list typ) (u:typ) := forall (V : typ -> Type), open_tm V G u.

Fixpoint denotation_tm_typ E (V:typ -> Type) (G : list typ) (u:typ) :=
  match G with
  | [] => itree E (V u)
  | t::ts => (V t) -> denotation_tm_typ E V ts u
  end.

CoFixpoint spin {E} {A} : itree E A := Tau spin.

(*
Section FIX.
  Variable A B :Type.
  Variable E : Type -> Type.
  Variable f : (A -> itree E B) -> (A -> itree E B).

CoFixpoint Y {E} {A B} (f : (A -> itree E B) -> (A -> itree E B)) (x:A) : itree E B :=
  g <- f (fun a => Tau (Y f a)) ;;
  g x.

End FIX.
*)  

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

