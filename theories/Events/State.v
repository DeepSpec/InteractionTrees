(** * State *)

(** Events to read and update global state. *)

(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Data.Monads.StateMonad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryKleisli
     Core.ITreeDefinition
     Indexed.Function
     Indexed.Sum
     Core.Subevent
     Interp.Interp.

Existing Instance Monad_stateT.

Local Open Scope itree_scope.
(* end hide *)

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

Definition interp_state {E M S}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M} (h : E ~> stateT S M) :
  itree E ~> stateT S M := interp h.

Arguments interp_state {E M S FM MM IM} h [T].
Arguments interp_state : simpl never.

Section State.

  Variable (S : Type).

  Variant stateE : Type -> Type :=
  | Get : stateE S
  | Put : S -> stateE unit.

  Definition get {E} `{stateE -< E} : itree E S := embed Get.
  Definition put {E} `{stateE -< E} : S -> itree E unit := embed Put.

  Definition h_state {E} : stateE ~> stateT S (itree E) :=
    fun _ e =>
      mkStateT (fun s =>
        match e with
        | Get => Ret (s, s)
        | Put s' => Ret (tt, s')
        end).

  (* SAZ: this is the instance for the hypothetical "Trigger E M" typeclass.
    Class Trigger E M := trigger : E ~> M 
  *)
  Definition pure_state {S E} : E ~> stateT S (itree E)
    := fun _ e => mkStateT (fun s => Vis e (fun x => Ret (x, s))).

  (* not sure why case_ requires the manual parameters *)
  Definition run_state {E}
    : itree (stateE +' E) ~> stateT S (itree E)
    := interp_state (case_ (bif := sum1) (c := stateT S (itree E))
                           h_state pure_state).

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {S E} [_] _.


(** An extensional stateful handler *)
Section eff_hom_e.
  Context {E F : Type -> Type}.

  (* note(gmm): you should be able to add events here
   * using a monad transformer. In that case, the type
   * of `eval` is:
   *
   *   forall t, E t -> m (itree F) (t * eff_hom_e)
   *
   * but you have the usual conditions on strictly positive uses
   *)
  CoInductive eff_hom_e : Type :=
  { eval : forall t, E t -> itree F (eff_hom_e * t) }.

  Definition interp_e (h : eff_hom_e) : itree E ~> itree F := fun R t =>
    ITree.iter (fun '(s, t) =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl (s, t))
      | VisF e k => ITree.map (fun '(s, x) => inl (s, k x)) (h.(eval) _ e)
      end) (h, t).

End eff_hom_e.
