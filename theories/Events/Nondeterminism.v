(** * Nondeterminism *)

(** Actually, bounded nondeterminism. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import List.
Import ListNotations.

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition
     Indexed.Sum
     Core.Subevent
     Events.Exception.
(* end hide *)

(** Make nondeterministic choices. *)
Variant nondetE : Type -> Prop :=
| Or : nondetE bool.

(** Choose one of two computations. *)
Definition or {E} `{nondetE -< E} {R} (t1 t2 : itree E R)
  : itree E R :=
  vis Or (fun b : bool => if b then t1 else t2).

(** Choose an element from a nonempty list (with the head and tail
    as separate arguments), so it cannot fail. *)
Definition choose1 {E} `{nondetE -< E} {X}
  : X -> list X -> itree E X
  := fix choose1' x xs : itree E X :=
       match xs with
       | [] => Ret x
       | x' :: xs => or (Ret x) (choose1' x' xs)
       end.

(** Pick any element in a list apart from the others. *)
Definition remove_from {X} : list X -> list (X * list X) :=
  let fix remove_from_ pre xs :=
      match xs with
      | [] => []
      | x :: xs' => (x, pre ++ xs') :: remove_from_ (pre ++ [x]) xs'
      end in
  remove_from_ [].

(** ** Empty nondeterminism *)

(** We can use [exceptE] events to model nullary branching. *)

(** Exception thrown by [choose]. *)
Variant no_choice : Set := NoChoice.

(** Choose an element from a list.

    This can fail if the list is empty, using the [exceptE no_choice] event.
 *)
Definition choose {E} `{nondetE -< E} `{exceptE no_choice -< E} {X}
  : list X -> itree E X
  := fix choose' xs : itree E X :=
       match xs with
       | [] => throw NoChoice
       | x :: xs =>
         or (Ret x) (choose' xs)
       end.
