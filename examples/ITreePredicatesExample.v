(* This file gives an elementary example of how to write a coinductive predicate
   over itrees and use it to do some simple proofs. This is a common use case
   when working with itrees. *)

(* TODO: this infrastructure should be generalized and integrated into
   the library. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     Classes.Morphisms
     ProofIrrelevance.

From ExtLib Require Import
     Monads.

From ITree Require Import
     ITree
     ITreeFacts.

From Paco Require Import paco.

Import ITreeNotations.


(* Defining an itree interpreter -------------------------------------------- *)

(* Suppose that we have an ITree whose event type admits certain kinds of
   operations.  For this example, we take a simplified version of the [stateE]
   event, which defines [get] and [put] operations on states.
 *)

Variant stateE (S:Type) : Type -> Type :=
| Get : stateE S S
| Put : S -> stateE S unit.

(* We can define an interpretation of [stateE] events into itrees with
   no events as follows. Note that we split out the "node functor", which is
   parameterized by the interpreter on the recursive calls, separating it from
   the CoFixpoint.  This structure mirrors the way that we define predicates
   below.

   The ITrees library defines more elaborate versions of these interpreters that
   work with multiple events types. *)

Definition stateT (S:Type) (M:Type -> Type) (R:Type) := S -> M (S * R)%type.

Definition interpret_stateF (S:Type) {R}
           (rec : itree (stateE S) R -> stateT S (itree void1) R)
           (t : itree (stateE S) R) : stateT S (itree void1) R :=
  fun s => match observe t with
        | RetF r => ret (s, r)
        | TauF t =>  Tau (rec t s)
        | VisF Get k => Tau (rec (k s) s)
        | VisF (Put s') k => Tau (rec (k tt) s')
        end.

CoFixpoint interpret_state {S R:Type} (t:itree (stateE S) R) : stateT S (itree void1) R :=
  interpret_stateF interpret_state t.

Lemma unfold_interpret_state : forall {S R} (t : itree (stateE S) R) (s:S),
    observe (interpret_state t s) =
    observe (interpret_stateF interpret_state t s).
Proof.
  reflexivity.
Qed.

(* Rewriting ---------------------------------------------------------------- *)

(* To enable rewriting under the [interpret_state] function, we need to show
   that it respects ≅.  In practice, this means instantiating the typeclass 
   [Proper] so that the setoid rewrite tactics recognize that interpret_state
   is such a morphism.  

   These proofs are pretty straightforward, but there are a few gotchas:

   - We use [red] to unfold the definitions of Proper and respectful.

   - We typically want to use [rewrite itree_eta] to change [t] into [(observe t)]
     but we don't want to do that before introducing the coinductive hypothesis
     because the extra "observes" get in the way of later using the CIH after
     we've made some progress in the proof.

   - We need to use [inj_pair2] to get equality of the projected components 
     of the VisF constructor, which means that we rely on ProofIrrelevance.
*)

Section Proper.
  Local Open Scope signature_scope.


  (* SAZ: This proof is a bit annoying.  We can only rewrite under the "upto" paco2 predicate
     (see the eq_itree_paco instance in Eq), which means we have to introduce names, start the upto proof,
     do the rewrite, and then regeneralize for the CIH.  It would be nicer if we could rewrite under (paco2 _ r).
   *)
  Instance proper_interpret_state {S R} : Proper ((@eq_itree (stateE S) R _ eq) ==> (@eq S) ==> (@eq_itree void1 (S * R) _ eq)) interpret_state.
  Proof.
    ginit. gcofix CIH.
    intros x y H0 x2 y0 H1. 
    rewrite (itree_eta (interpret_state x x2)).
    rewrite (itree_eta (interpret_state y y0)).
    rewrite !unfold_interpret_state. subst.
    punfold H0. repeat red in H0. unfold interpret_stateF.
    destruct (observe x); inv H0; try discriminate; pclearbot; simpl;
      try (gstep; constructor; eauto with paco; fail).
    apply inj_pair2 in H2. apply inj_pair2 in H3. subst.
    destruct e; gstep; econstructor; eauto with paco.
  Qed.

  End Proper.



(* Defining Predicates Over ITrees ------------------------------------------ *)

(* For the sake of example, let's prove that an itree that does not contain any
   Get events, when interpreted in the standard state monad, does not actually
   depend on the (initial) state.  *)

(* First, we define a predicate [NoGets], which characterizes the itrees that
   don't have [Get] events.

   There are basically two options for doing this: (1) write a "native" CoInductive
   predicate, or (2) write a paco-compatible predicate.  Since we advocate using
   paco for coinductive proofs, we'll follow option (2).
 *)

(* Paco requires that we state our predicate "functorially", which means that we
   specify a _predicate transformer_ (i.e. function from relations to relations)
   and then prove that it is monotonic.  Paco then constructs the greatest fixed
   point, which we can use with the paco tactics pcofix, etc.

   In this case, [NoGets] is a _unary_ predicate, so all of our "relation
   transformers" are "unary predicate transformers".  For more sophisticated
   examples of binary predicates, see the definitions of [eq_itree] and
   [eutt]. *)


(* Due to the separation of the [itree] definition into [itreeF] and [itree] proper,
   it is convenient to split up the [NoGets] predicate in an analogous way. *)

(* First, we define [NoGetsF]. It takes as input [rec], which will be instantiated to 
   the [NoGets] predicate for subtrees.  It yields a predicate on [itreeF] nodes. *)

Variant NoGetsF {S R} (rec : itree (stateE S) R -> Prop) : itreeF (stateE S) R (itree (stateE S) R) -> Prop :=
| isRet : forall (r:R), NoGetsF rec (RetF r)
| isTau : forall t, rec t -> NoGetsF rec (TauF t)
| isPut : forall (k : unit -> itree (stateE S) R), forall (s:S), rec (k tt) -> NoGetsF rec (VisF (Put s) k).
Hint Constructors NoGetsF.


(* Next, we lift the [NoGetsF] predicate through the [itree] [go] constructor
   to obtain a predicate transformer on [itree stateE R].  This is achieved
   just by asking composing NoGetsF with [observe].
 *)

(* SAZ: n.b. for some reason, we have adopted the [Foo_] notational convention
   for the predicate transformer whose greatest fixpoint is [Foo].  Is this good?

   SAZ: Actually, I see that we're inconsistent between [eq_itree] and [eutt] 
   with these naming conventions.
 *)

Definition NoGets_ {S R} (rec : itree (stateE S) R -> Prop) (t : itree (stateE S) R) : Prop :=
  NoGetsF rec (observe t).


(* Next, we need to prove that [NoGets_] is a monotone function on relations,
   which means that paco can take its greatest fixpoint.  Monotonicity of 
   [NoGets_] depends on monotonicity of [NoGetsF].

   Fortunately, paco provides the tactic [pmonauto] which almost always discharges
   these proofs.  It also provides the definitions monotone1, monotone2, etc. 
   for monotonicity at different arities of relations.
*)

(* SAZ: Arguably, the LE fact should be defined via some named property.  In 
   the Coq Relationclasses library, there is a definition of subrelation, which
   is the binary version of this.  It might be more uniform to have 
   subrelation1, subrelation2, subrelation3, etc. for different arities.

   SAZ: It's a bit of a wart that, due to NoGetsF transforming predicates on
   [itree (stateE S) R] to predicates on [itreeF (stateE S) (itree (stateE S) R)]
   that it isn't an instance of monotone1.
*)

Lemma monotone_NoGetsF : forall {S R} t (r r' : itree (stateE S) R -> Prop)
  (IN: NoGetsF r t) (LE: forall y, r y -> r' y), NoGetsF r' t.
Proof.
  pmonauto.
Qed.  

(* SAZ: we need to do a couple of reductions to expose the structure of 
   the lemma so that pmonauto can work.  Note that [cbn] and [simple]
   don't work here because they don't unfold the definitions.  *)
Lemma monotone_NoGets_ : forall {S R}, monotone1 (@NoGets_ S R).
Proof.
  do 2 red. pmonauto.
Qed.
Hint Resolve monotone_NoGets_ : paco.

(* Finally, we can define the [NoGets] predicate by simply applying paco1
   starting from bot1 (the least prediate).  We would use paco2 and bot2 for a
   binary relation, paco3 and bot3 for ternary, etc. *)

Definition NoGets {S R} : itree (stateE S) R -> Prop := paco1 NoGets_ bot1.


(* Using a coinductive predicate -------------------------------------------- *)

(* Now that we have defined [NoGets], we can use that predicate to do a
   coinductive proof.  Intuitively, if we interpret an itree of type 
   [itree (stateE S) R] that satisfies the [NoGets] predicate, it does
   not matter what initial state it runs in.

   To state this correctly, we have to "project away" the final state component
   that is produced by the monad, since the two final states might 
   differ.

   Some notes about this proof:

   - In general, rewriting up to ≅ or ≈ can take place only under the
     "up to" paco context.  This means that to do the [rewrite (itree_eta ...)]
     steps, we have to have done [pupto2_init] first.  
 *)

Lemma state_independent : forall {S R} (t:itree (stateE S) R) 
                            (H: NoGets t),
    forall s s', ('(s,x) <- interpret_state t s ;; ret x) ≅ ('(s,x) <- interpret_state t s' ;; ret x).
Proof.
  intros S R.
  ginit. gcofix CIH.
  intros t H0 s s'. 
  rewrite (itree_eta (interpret_state t s)).
  rewrite (itree_eta (interpret_state t s')).
  rewrite !unfold_interpret_state.
  unfold interpret_stateF.
  punfold H0. repeat red in H0.
  destruct (observe t); cbn.
  - rewrite !bind_ret_l. gstep. econstructor. eauto.
  - rewrite !bind_tau. gstep. econstructor.
    gbase. eapply CIH.
    inversion H0. subst. pclearbot. assumption.
  - destruct e; cbn.
    + (* e is Get, which is ruled out by the NoGets predicate *) inversion H0.
    + rewrite !bind_tau.
      gstep. econstructor. gbase. eapply CIH.
      inversion H0. apply inj_pair2 in H2. subst. pclearbot. assumption.
Qed.


(* More or less the same proof also works for any continuation [k] that ignores the state.
   This proof illustrates the use of paco2_mon -- monotonicity means that if we assume
   that [k (s, x) ≅ k (s', x))] then [k (s, x)] is related to [k (s', x)] at any "later"
   step of the cofixpoint.  e.g. in the proof below we need them related at [r].
*) 
Lemma state_independent_k : forall {S R U} (t:itree (stateE S) R) 
                            (H: NoGets t)
                            (k: (S * R) -> itree void1 U)
    (INV: forall s s' x, k (s, x) ≅ k (s', x)),
    forall s s', (sx <- interpret_state t s ;; (k sx)) ≅ (sx <- interpret_state t s' ;; (k sx)).
Proof.
  intros S R U.
  ginit. gcofix CIH.
  intros t H0 k INV s s'. 
  rewrite (itree_eta (interpret_state t s)).
  rewrite (itree_eta (interpret_state t s')).
  rewrite !unfold_interpret_state.
  unfold interpret_stateF.
  punfold H0. repeat red in H0.
  destruct (observe t); cbn.
  - rewrite !bind_ret_l. gfinal. right.
    eapply paco2_mon_bot; eauto with paco. apply INV.
  - rewrite !bind_tau. gstep. econstructor.
    gbase. eapply CIH; auto.
    inversion H0. subst. pclearbot. assumption.
  - destruct e; cbn.
    + (* e is Get, which is ruled out by the NoGets predicate *) inversion H0.
    + rewrite !bind_tau.
      gstep. econstructor. gbase. eapply CIH; auto.
      inversion H0. apply inj_pair2 in H2. subst. pclearbot. assumption.
Qed.



Theorem state_independent': forall {S R} (t:itree (stateE S) R) 
                            (H: NoGets t),
                             forall s s', ('(s,x) <- interpret_state t s ;; ret x) ≅ ('(s,x) <- interpret_state t s' ;; ret x).
Proof.
  intros S R t H s s'.
  eapply state_independent_k; eauto.
  intros.
  reflexivity.
Qed.  
