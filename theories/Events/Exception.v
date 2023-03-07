(** * Exception event *)

(* begin hide *)
From ITree Require Import ITree.

Set Implicit Arguments.
(* end hide *)

(** Throw exceptions of type [Err]. *)
Variant exceptE (Err : Type) : Type -> Type :=
| Throw : Err -> exceptE Err void.

(** Since the output type of [Throw] is [void], we can make it an action
    with any return type. *)
Definition throw {Err : Type} {E : Type -> Type} `{exceptE Err -< E} {X}
           (e : Err)
  : itree E X
  := vis (Throw e) (fun v : void => match v with end).

Definition try_catch {Err R : Type } {E : Type -> Type} 
            (ttry : itree (exceptE Err +' E) R) (kcatch : Err -> itree (exceptE Err +' E) R) : itree (exceptE Err +' E) R :=
  (* the problem is kcatch is actually not a handler, need basic iter?*)
  let catch_body (t : itree (exceptE Err +' E) R) : itree (exceptE Err +' E) ((itree (exceptE Err +' E) R) + R )  := 
       match observe t with
       | RetF r => Ret (inr r)
       | TauF t' => Ret (inl t')
       | VisF e k =>
         match e with
         | inl1 (Throw exc) => fmap inr (kcatch exc)
         | inr1 e' =>  fmap (fun x => inl (k x) ) (trigger e) end end

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
        | inl1 (Throw exc) => Ret (inr (inr exc) )
        | inr1 e' =>  fmap (fun x => inl (k x) ) (trigger e)
        end
      end in
  ITree.iter prefix_body t.
