Require Import ITree.ITree.
Require Import ITree.Fix.
Require Import ExtLib.Structures.Monads.

Import MonadNotation.


Section M.
  (* The effects interface *)
  Variable IO : Type -> Type.

  Variable M : Type -> Type.
  Variable m : Monad M.

  (*
  (* Monads are functors *)
  Variable fmap_M : forall A B, (A -> B) -> M A -> M B.
  *)
  (*
  (* We can write [join] in terms of [bind] *)
  Definition join {X} (e : M (M X)) : M X :=
    bind e (fun y => y).
  
  (* We can always "delay" monadic computations by suspending them
     under a lambda *)
  Definition coerce1 {A B} (f : M (A -> B)) : A -> M B :=
    fun (x:A) =>
      bind f (fun g => ret (g x)).

*)
  (* A monadic "handler" for some effects E is just a mapping from
     the actions to monadic computations that return values of the 
     right type. *)
  Variable handler : forall {X} (e:IO X), M X.

  
(*
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

  
  

  (* We can interpret an itree into any monad that supports mfix as follows: *)
  Definition run {X} (t : itree IO X) : M X :=
    join ((coerce1 (mfix (itree IO X -> M X)
                         ( fun (f : (itree IO X -> M X)) =>
                             (ret (fun (u : itree IO X) =>
                                     match u with
                                     | Ret x => ret x
                                     | Tau w => f w
                                     | Vis e k =>
                                       bind (handler _ e) (fun a => f (k a))
                                     end)
                         )) 

          )) t).

*)
  (* Version 2: Correct version of MFix -------------------------------------- *)

  Definition mfix_weak := forall A B, ((A -> M B) -> (A -> M B)) -> A -> M B.

  
  Definition mfix_type := forall A B, (forall N `{Monad N} (inc:forall A, M A -> N A), ((A -> N B) -> (A -> N B))) -> A -> M B.
  Variable mfix_parametric : mfix_type.

  Definition run'' {X} (t : itree IO X) : M X :=
            mfix_parametric (itree IO X) X 
                   ( fun N _ inc (f : (itree IO X -> N X)) =>
                       (fun (u : itree IO X) =>
                          match u with
                          | Ret x => ret x
                          | Tau w => f w
                          | Vis e k =>
                            bind (inc _ (handler _ e)) (fun a => f (k a))
                          end)
                     ) t.

End M.

Require Import Paco.paco.

Check paco2.

Section P.
  
  Definition mfix_P {a b:Type} (f : ((a -> b -> Prop) -> (a -> b -> Prop))) : a -> b -> Prop :=
    @paco2 a (fun _ => b) f bot2.

  Lemma mfix_law1 : forall (a b : Type) f (x:a) (y:b), (@monotone2 a (fun _ => b) f) -> (mfix_P f x y) -> f (mfix_P f) x y.
  Proof.
    intros a b f x y Hm H. 
    punfold H. unfold mfix_P. unfold upaco2 in H. unfold monotone2 in Hm.
    eapply Hm. apply H.
    intros. inversion PR. exact H0. inversion H0.
  Qed.

  Lemma mfix_law2 : forall (a b : Type) f (x:a) (y:b), (@monotone2 a (fun _ => b) f) -> f (mfix_P f) x y -> (mfix_P f x y).
  Proof.
    intros a b f x y Hm H.
    unfold mfix_P.
    pfold. unfold mfix_P in H. unfold monotone2 in Hm. eapply Hm. apply H.
    intros x0 x1 PR.
    left. exact PR.
  Qed.

End P.
    

Variable E: Type -> Type.

Check Fix.FixImpl.mfix.
Locate MonadFix.
Set Printing Universes.
Print mfix_type.
Print Monad_itree.
Definition mfix_itree : mfix_type (itree E) :=
  fun A B f => Fix.FixImpl.mfix (fun _ => B) (fun E' inc rec => f (itree E') (Monad_itree) inc rec).

      
