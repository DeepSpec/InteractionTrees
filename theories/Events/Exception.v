(** * Exception event *)

(* begin hide *)

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.FunctionalExtensionality
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
.

(* end hide *)

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** Throw exceptions of type [Err]. *)
Variant exceptE (Err : Type) : Type -> Type :=
| Throw : Err -> exceptE Err void.

(** Since the output type of [Throw] is [void], we can make it an action
    with any return type. *)
Definition throw {Err : Type} {E : Type -> Type} `{exceptE Err -< E} {X}
           (e : Err)
  : itree E X
  := vis (Throw _ e) (fun v : void => match v with end).

(* translate *)

Definition try_catch {Err R : Type } {E : Type -> Type} 
            (ttry : itree (exceptE Err +' E) R) (kcatch : Err -> itree (exceptE Err +' E) R) : itree (exceptE Err +' E) R :=
  (* the problem is kcatch is actually not a handler, need basic iter?*)
  let catch_body (t : itree (exceptE Err +' E) R) : itree (exceptE Err +' E) ((itree (exceptE Err +' E) R) + R )  := 
       match observe t with
       | RetF r => Ret (inr r)
       | TauF t' => Ret (inl t')
       | VisF e k =>
         match e with
         | inl1 (Throw _ exc) => Functor.fmap inr (kcatch exc)
         | inr1 e' =>  Functor.fmap (fun x => inl (k x) ) (trigger e) end end

  in 
  ITree.iter catch_body ttry.


Definition throw_prefix {Err R : Type} {E : Type -> Type}
           (t : itree (exceptE Err +' E) R) : itree  (exceptE Err +' E) (R + Err) :=
  let prefix_body (t' : itree (exceptE Err +' E)  R ) : itree (exceptE Err +' E)  ((itree (exceptE Err +' E) R) + (R + Err) ) :=
      match observe t' with
      | RetF r => Ret (inr (inl r) )
      | TauF t' => Ret (inl t')
      | VisF e k =>
        match e with
        | inl1 (Throw _ exc) => Ret (inr (inr exc) )
        | inr1 e' =>  Functor.fmap (fun x => inl (k x) ) (trigger e)
        end
      end in
  ITree.iter prefix_body t.


Lemma try_catch_ret : forall E Err R r (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Ret r) kcatch ≅ Ret r.
Proof.
  intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
Qed.

Lemma try_catch_tau : forall E Err R t (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Tau t) kcatch ≅ Tau (try_catch t kcatch).
Proof.
  intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
Qed.

Lemma try_catch_exc : forall E Err R exc (k :void -> itree (exceptE Err +' E) R) 
                               (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Vis (inl1 (Throw _ exc)) k ) kcatch ≅ kcatch exc.
Proof.
   intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
   rewrite unfold_iter. cbn. unfold ITree.map.
   rewrite bind_bind. setoid_rewrite bind_ret_l. rewrite bind_ret_r.
   reflexivity.
Qed.

Lemma try_catch_ev : forall E A Err R (ev: E A) k (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Vis (inr1 ev) k ) kcatch ≅ Vis (inr1 ev) (fun x => Tau (try_catch (k x) kcatch) ).
Proof.
  intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  rewrite unfold_iter. cbn. unfold ITree.map at 3.
  setoid_rewrite bind_bind. rewrite bind_trigger. cbn.
  setoid_rewrite bind_ret_l. reflexivity.
Qed.
