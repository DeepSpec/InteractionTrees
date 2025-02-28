(* Example demonstrating the core features of the library. *)

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.

(* Custom effects *)
Variant inputE : Type -> Prop :=
| Input : inputE nat.

(* Effectful programs *)
Definition echo : itree inputE nat
  := x <- trigger Input ;;
     Ret x.

(* Effect handlers *)
Definition handler {E} (n : nat)
  : inputE ~> itree E
  := fun _ e => match e with
                | Input => Ret n
                end.

(* Interpreters *)
Definition echoed (n : nat)
  : itree void1 nat
  := interp (handler n) echo.

(* Equational reasoning *)
Theorem echoed_id : forall n, echoed n ≈ Ret n.
Proof.
  intros n.              (*   echoed n *)
  unfold echoed, echo.   (* ≈ interp (handler n) (x <- trigger Input ;; Ret x) *)
  rewrite interp_bind.   (* ≈ x <- interp (handler n) Input ;; interp (handler n) (Ret x) *)
  rewrite interp_trigger.
                         (* ≈ x <- handler n _ Input ;; interp (handler n) (Ret x) *)
  cbn.                   (* ≈ x <- Ret n ;; interp (handler n) (Ret x) *)
  rewrite bind_ret_l.    (* ≈ interp (handler n) (Ret n) *)
  rewrite interp_ret.    (* ≈ Ret n *)
  reflexivity.
Qed.
