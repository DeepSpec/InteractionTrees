Require Import ITree.ITree.
Require Import ExtLib.Structures.Monads.

Import MonadNotation.

Section M.
  (* The effects interface *)
  Variable IO : Type -> Type.

  Variable M : Type -> Type.
  Variable m : Monad M.

  (* Monads are functors *)
  Variable fmap_M : forall A B, (A -> B) -> M A -> M B.

  (* We can write [join] in terms of [bind] *)
  Definition join {X} (e : M (M X)) : M X :=
    bind e (fun y => y).

  (* We can always "delay" monadic computations by suspending them
     under a lambda *)
  Definition coerce1 {A B} (f : M (A -> B)) : A -> M B :=
    fun (x:A) =>
      bind f (fun g => ret (g x)).


  (* Note: the other direction is BOGUS -- we can't "run" the effects
     of a function's body _before_ returning the function.  *)
  (* Definition coerce2 {A B} (f : A -> M B) : M (A -> B) := BOGUS *)



  (* Version 1 (bad!) --------------------------------------------------------- *)
  (* NOTE: This is the "Haskell" version of mfix, but it isn't what we want *)

  (* Some monads support a "fixpoint" combinator that should allow for the
     interpretation of recursion. In general, such monads will have to be pretty
     fancy.  But our itrees monad _does_ support mfix. *)
  (* Monadic fixpoint combinator. *)
  Variable mfix : forall A, (A -> M A) -> M A.

  (* What are the laws for mfix?? Note: they should probably not refer to fix,
     unlike the Haskell presentation. *)


  (* A monadic "handler" for some effects E is just a mapping from
     the actions to monadic computations that return values of the
     right type. *)
  Variable handler : forall {X} (e:IO X), M X.


  (* We can interpret an itree into any monad that supports mfix as follows: *)
  Definition run {X} (t : itree IO X) : M X :=
    join ((coerce1 (mfix (itree IO X -> M X)
                         ( fun (f : (itree IO X -> M X)) =>
                             (ret (fun (u : itree IO X) =>
                                     match u.(observe) with
                                     | RetF x => ret x
                                     | TauF w => f w
                                     | VisF e k =>
                                       bind (handler _ e) (fun a => f (k a))
                                     end)
                         ))

          )) t).


  (* Version 2: Correct version of MFix -------------------------------------- *)
  Variable mfix'' : forall A B, ((A -> M B) -> (A -> M B)) -> A -> M B.

  Definition run'' {X} (t : itree IO X) : M X :=
            mfix'' (itree IO X) X
                   ( fun (f : (itree IO X -> M X)) =>
                       (fun (u : itree IO X) =>
                          match u.(observe) with
                          | RetF x => ret x
                          | TauF w => f w
                          | VisF e k =>
                            bind (handler _ e) (fun a => f (k a))
                          end)
                     ) t.


(* below here is probably junk ---------------------------------------------- *)


  (* Note, can weaken the requirements on mfix for the purposes of our
  development because we only need to use mfix at a funnction type.  That is, we
  could specialize things to: *)
  Variable mfix' : forall A B, ((A -> B) -> M (A -> B)) -> M (A -> B).

  (* It might be "easier" to implement a monad that support mfix' than one that supports general mfix. *)

  Definition run' {X} (t : itree IO X) : M X :=
    join ((coerce1 (mfix' (itree IO X) (M X)
                         ( fun (f : (itree IO X -> M X)) =>
                             (ret (fun (u : itree IO X) =>
                                     match u.(observe) with
                                     | RetF x => ret x
                                     | TauF w => f w
                                     | VisF e k =>
                                       bind (handler _ e) (fun a => f (k a))
                                     end)
                         ))

          )) t).






(*
  CoFixpoint handle {X} (t : itree IO X) : itree MIO X :=
    match t with
    | Ret v => Ret v
    | Tau u => Tau (handle u)
    | Vis e k =>
      Vis (handler e)
          (fun (m : M (E_reaction io)) => _)
    end.
*)
(*
  CoInductive run {X} : itree IO X -> M X -> Prop :=
  | run_ret : forall v, run (Ret v) (ret v)
  | run_tau : forall u r, run u r -> run (Tau u) r
  | run_vis : forall e k r,
      exists t, run (fmap_M _ _ k (handler e)) = t.
      run (Vis e k) (bind r k)


  CoInductive run {X} : itree IO X -> M (itree IO X) -> Prop :=
  | run_ret : forall v, run (Ret v) (ret (Ret v))
  | run_tau : forall u r, run u r -> run (Tau u) (bind r (fun v => ret (Tau v)))
  | run_vis : forall e k r,
      run (handler e) r ->
      run (Vis e k) (bind r k)
 *)

End M.
