Set Implicit Arguments.
Set Contextual Implicit.

From ExtLib Require Import
     Monads.

From ITree Require Import
     ITree
     MorphismsFacts.

From Paco Require Import paco.

From Coq Require Import
     Setoid
     Classes.Morphisms
     Classes.RelationClasses.


(* SAZ: Question: should ext-lib define a notion of Monad Transformer and accompanying theory?
   Perhaps something like the following:
*)   

(* Monad Transformer *)
Class MonadTransformer (T:(Type -> Type) -> (Type -> Type)) := monad_transform : forall M `{Monad M}, Monad (T M).


(* SAZ: An example use of monad transformers is found in the ITree Monads module: *)
Section State.
  Variable (S: Type).

  Global Instance MonadState_state : MonadState S (Monads.state S) :=
    Build_MonadState S (Monads.state S) (fun s => (s, s)) (fun s _ => (s, tt)).

  
  Global Instance MT_stateT : MonadTransformer (Monads.stateT S) :=
    fun M monM =>
      Build_Monad _
                  (fun t x s => ret (s, x))
                  (fun t u (sm : S -> M (S * t)%type) k s => (bind (sm s) (fun '(s', t') => k t' s))).


  Global Instance MonadState_stateT M `{Monad M} : MonadState S (Monads.stateT S M) :=
    Build_MonadState S _ (fun s => ret (s, s)) _.
  exact (fun s _ => ret (s, tt)).
  Defined.

End State.


(* SAZ: We could change the ITrees library to use monad transformers and also 
   instantiate the ExtLib classes for MonadState, etc., something like this:
*)

  Variant stateE (S:Type) : Type -> Type :=
  | Get : stateE S S
  | Put : S -> stateE S unit.
  Arguments Get {S}.
  Arguments Put {S} _.

  Global Instance MS_itree {E S} : MonadState S (itree (stateE S +' E)) :=
    Build_MonadState S _ (ITree.lift (inl1 Get)) (fun s => ITree.lift (inl1 (Put s))).

  Definition eval_state' {E S} : stateE S ~> Monads.stateT S (itree E) :=
    fun _ e =>
      match e with
      | Get => get
      | Put s' => put s'
      end.

  Definition run_state {E S} :
    itree (stateE S +' E) ~> Monads.stateT S (itree E) :=
    interp1_state eval_state'.

  
Lemma eq_run_state {E S R} :
  Proper ( (@eq_itree (stateE S +' E) R) ==> (@eq S) ==> (@eq_itree E (S * R))) (@run_state _ _ R).
Proof.
  solve_proper.
Qed.  

  
(* The overloaded notation is quite nice for writing examples: *)
Definition example1 {E} : itree (stateE nat +' E) nat := 
  x <- get ;;
  put (x + x) ;;
  y <- get ;;
  ret y.

Definition example2 {E} : itree (stateE nat +' E) nat := 
  x1 <- get ;;
  x2 <- get ;;                                                           
  put (x1 + x2) ;;
  y <- get ;;
  ret y.


Lemma interp1_state_get : forall {E:Type -> Type} S s,
    interp1_state (eval_state' (S:=S)) S get s ≅ Tau (Ret (s, s) : itree E (S * S)).
Proof.
  intros E S s.
  unfold get. unfold MS_itree. 
  rewrite interp1_state_liftE1.
  simpl.
  reflexivity.
Qed.

Lemma interp1_state_put : forall {E :Type -> Type} S s s',
    interp1_state (eval_state' (S:=S)) unit (put s') s ≅ Tau (Ret (s', tt) : itree E (S * unit)).
Proof.
  intros E S s s'.
  unfold put. unfold MS_itree.
  rewrite interp1_state_liftE1.
  simpl.
  reflexivity.
Qed.

Lemma interp1_state_E : forall {E F:Type -> Type} S (s:S) (f : E ~> Monads.stateT S (itree F)) (X:Type) (e:F X),
    interp1_state f X (embed e) s ≅ (Vis e (fun x => ret (s, x))).
Proof.
  intros E F S s f X e.
  unfold embed. unfold Embeddable_itree. unfold lift. simpl.
  rewrite interp1_state_liftE2.
  reflexivity.
Qed.  


Lemma run_state_E_right : forall {E} S (s:S) (R T:Type) (e:E R) (k : R -> itree (stateE S +' E) T),
    run_state (x <- (ITree.lift (inr1 e)) ;; k x) s ≅ (x <- (ITree.lift e) ;; run_state (k x) s).
Proof.
  intros E S s R T e k. 
  unfold run_state.
  rewrite interp1_state_bind. cbn. rewrite interp1_state_liftE2.
  cbn.
  rewrite vis_bind. unfold ITree.lift. rewrite vis_bind.
  apply itree_eq_vis.
  intros.
  rewrite !ret_bind. cbn. reflexivity.
Qed.


Lemma run_state_E0_right : forall {E:Type -> Type} S (s:S) (T:Type) (e:E unit) (k : itree (stateE S +' E) T),
    run_state ((ITree.lift (inr1 e)) ;; k) s ≅ ((ITree.lift e) ;; run_state k s).
Proof.
  intros E S s T e k.
  apply run_state_E_right.
Qed.


Lemma run_state_tau : forall {E:Type -> Type} S {T : Type} (t:itree (stateE S +' E) T) (s:S),
    run_state (Tau t) s ≅ Tau (run_state t s).
Proof.
  intros E S T t s.
  unfold run_state. rewrite interp1_state_tau. reflexivity.
Qed.  

Lemma run_state_get : forall {E:Type -> Type} S {T : Type} (k : S -> itree (stateE S +' E) T) (s:S),
    run_state (x1 <- get ;; k x1) s ≅ Tau (run_state (k s) s).
Proof.
  intros E S T k s.
  unfold run_state.
  rewrite interp1_state_bind.
  rewrite interp1_state_get.
  cbn. rewrite tau_bind.
  rewrite ret_bind. cbn. reflexivity.
Qed.  

(* SAZ: this is the same exact proof as above -- think about automation. *)
Lemma run_state_put : forall {E:Type -> Type} S {T : Type} (k : itree (stateE S +' E) T) (s s':S),
    run_state (put s' ;; k) s ≅ Tau (run_state k s').
Proof.
  intros E S T k s s'.
  unfold run_state.
  rewrite interp1_state_bind.
  rewrite interp1_state_put.
  cbn. rewrite tau_bind.
  rewrite ret_bind. cbn. reflexivity.
Qed.  



Ltac run_state_tac :=
  repeat match goal with
         | [ |- context[run_state (Tau (?T)) ?S] ] => rewrite run_state_tau
         | [ |- context[run_state (x <- get ;; @?K x) ?S] ] => first [rewrite run_state_get | rewrite run_state_E_right]
         | [ |- context[run_state (put ?S1 ;; ?K) ?S] ]    => first [rewrite run_state_put | rewrite run_state_E0_right]
         end.

Ltac strip_taus :=
  repeat match goal with
         | [ |- ?T1 ≈ ?T1] => reflexivity
         | [ |- Tau ?T1 ≈ ?T2 ] => rewrite tau_eutt
         | [ |- ?T1 ≈ Tau ?T2 ] => rewrite tau_eutt
         end.

(* Delete the second [get] *)
Lemma get_law : forall {E:Type -> Type} S {T : Type} (k : S -> S -> itree (stateE S +' E) T) (s:S), 
    (run_state (x1 <- get ;; x2 <- get ;; k x2 x1) s) ≅ Tau (run_state (x1 <- get ;; k x1 x1) s).
Proof.
  intros E S T k s. 
  run_state_tac.
  reflexivity.
Qed.  

(* Delete the first [put] *)
Lemma put_law : forall {E:Type -> Type} S {T : Type} (k : itree (stateE S +' E) T) (s0 s1 s2 :S), 
    (run_state (put s1;; put s2 ;; k) s0) ≅ Tau (run_state (put s2;; k) s0).
Proof.
  intros E S T k s0 s1 s2.
  run_state_tac.
  reflexivity.
Qed.  

Lemma put_get_law :forall {E:Type -> Type} S {T : Type} (k : S -> itree (stateE S +' E) T) (s0 s1:S), 
    (run_state (put s1;; x <- get ;; k x) s0) ≅ Tau (Tau (run_state (k s1) s1)).
Proof.
  intros E S T k s0 s1.
  run_state_tac.
  reflexivity.
Qed.  
  

Lemma examples_equiv : forall s (E:Type->Type), run_state (@example1 E) s ≈ run_state example2 s.
Proof.
  intros s E.
  unfold example1.
  unfold example2.
  run_state_tac.
  strip_taus.
Qed.



(* Commuting Effects across different monads -------------------------------- *)
  
(* Two different instances of the state monad don't interfere in the sense that
   - get1 ;; get2 ≈ get2 ;; get1 
   - write1 ;; write1 ≈ write2 ;; write1 
 *)

Section TwoStates.

  Context (E : Type -> Type).
  Context {S1 S2 : Type}.
          
Definition state2E := ((stateE S1) +' ((stateE S2) +' E)).

(* First some definitions of the effects *)

Definition get1 : itree state2E S1 := get.
Definition put1 (s:S1) : itree state2E unit := (put s).
Definition get2 : itree state2E S2 := ITree.lift (inr1 (inl1 Get)).
Definition put2 (s:S2) : itree state2E unit := ITree.lift (inr1 (inl1 (Put s))).

End TwoStates.

Section RunTwoStates.
  Context {S1 S2:Type}.

  Definition runboth {E:Type -> Type} R (t : itree (state2E E) R) (s1:S1) (s2:S2) : itree E (S2 * (S1 * R))
    := run_state (run_state t s1) s2.

Lemma runboth_put1 : forall {E R} s1 s1' s2 (k : itree (state2E E) R),
    runboth (put1 s1' ;; k) s1 s2 ≅ Tau (runboth k s1' s2).
Proof.
  intros E R s1 s1' s2 k. 
  unfold runboth.
  unfold put1. rewrite run_state_put. rewrite run_state_tau. reflexivity.
Qed.


Lemma runboth_put2 : forall {E R} s1 s2 s2' (k : itree (state2E E) R),
    runboth (put2 s2' ;; k) s1 s2 ≅ Tau (runboth k s1 s2').
Proof.
  intros E R s1 s2 s2' k. 
  unfold runboth.
  unfold put2.
  rewrite run_state_E0_right.
  replace (ITree.lift (inl1 (Put s2'))) with (put s2') by reflexivity.
  rewrite run_state_put. reflexivity.
Qed.

Lemma runboth_get1 : forall {E:Type -> Type} {T : Type} (k : S1 -> itree (state2E E) T) (s1:S1) (s2:S2),
    runboth (x1 <- get1 ;; k x1) s1 s2 ≅ Tau (runboth (k s1) s1 s2).
Proof.
  intros E T k s1 s2.
  unfold runboth.
  unfold get1.
  rewrite run_state_get.
  rewrite run_state_tau.
  reflexivity.
Qed.  

Lemma runboth_get2 : forall {E:Type -> Type} {T : Type} (k : S2 -> itree (state2E E) T) (s1:S1) (s2:S2),
    runboth (x1 <- get2 ;; k x1) s1 s2 ≅ Tau (runboth (k s2) s1 s2).
Proof.
  intros E T k s1 s2.
  unfold runboth.
  unfold get2.
  rewrite run_state_E_right.
  replace (ITree.lift (inl1 Get)) with (get (T:=S2)) by reflexivity.
  rewrite run_state_get.
  reflexivity.
Qed.

End RunTwoStates.

Definition example3 {E} : itree (@state2E E nat nat) nat :=
  put1 3 ;;
  put2 4 ;;
  x <- get1 ;;
  y <- get2 ;;
  ret (x + y).

Definition example4 {E} : itree (@state2E E nat nat) nat :=
  put2 4 ;;
  put1 3 ;;
  y <- get2 ;;
  x <- get1 ;;
  ret (x + y).


Lemma examples_equiv2 : forall s1 s2 {E},
    runboth (@example3 E) s1 s2 ≈ runboth (@example4 E) s1 s2.
Proof.
  intros s1 s2 E.
  unfold example3. unfold example4.
  repeat match goal with
         | [ |- context[runboth (x <- get1 ;; @?K x) ?S] ] => rewrite runboth_get1
         | [ |- context[runboth (x <- get2 ;; @?K x) ?S] ] => rewrite runboth_get2
         | [ |- context[runboth (put1 ?S1 ;; ?K) ?S] ]    => rewrite runboth_put1
         | [ |- context[runboth (put2 ?S1 ;; ?K) ?S] ]    => rewrite runboth_put2
         end.
  strip_taus.
Qed.


  

