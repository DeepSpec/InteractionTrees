Require Import Imp. 
Require Import Paco.paco.
From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     StateFacts
     StateKleisli
     Eq.
From Coq Require Import
     String
     Setoid
     Morphisms
     Arith
     Logic.FunctionalExtensionality.
From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.

(**
   The chapter [Equiv] from _Programming Language Foundations_ introduced a
   notion of behavioral equivalence over _Imp_ programs.
   Two _com_ [c_1] and [c_2] were said to be equivalent if for any initial state,
   [c_1] reduced according to the language's big step semantics to a final state
   if and only if [c_2] reduced to the same final state.
   We investigate in this chapter how behavioral equivalence is phrased at the
   level of itrees, and how it can be proved on simple examples.
*)

(* Defining the notion at the itree level offers the benefit of uniformity:
   the notion is language independent.
   YZ: Not really though, depends on the interpretation obviously
 *)

Definition run_state {E A} (R : Monads.stateT env (itree E) A) (st: env) : itree E (env * A) :=     R st.

Definition aequiv_strong (a1 a2: aexp): Prop :=
  denote_aexp a1 ≈ denote_aexp a2.

Definition eval_aexp (a: aexp) :=
  @interp_imp void1 value (denote_aexp a).

Definition eval_bexp (b: bexp) :=
  @interp_imp void1 bool (denote_bexp b).

Definition aequiv (a1 a2: aexp): Prop :=
  forall s, run_state (eval_aexp a1) s ≈ run_state (eval_aexp a2) s.

Definition bequiv (b1 b2: bexp): Prop :=
  forall s, run_state (eval_bexp b1) s ≈ run_state (eval_bexp b2) s.

Definition cequiv (c1 c2: com): Prop :=
  forall s, run_state (@interp_imp void1 _ (denote_com c1)) s ≈ run_state (interp_imp (denote_com c2)) s.

Section Examples.

  Import ImpNotations.

  Definition W : string := "W".
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z".

  Lemma interp_imp_ret: forall {R} (v: R) (E: Type -> Type) (g : env),
     run_state (interp_imp (Ret v)) g ≅ (Ret (g, v) : itree E (env * R)).
  Proof.
    intros.
    unfold interp_imp, interp_map, run_state.
    rewrite interp_ret.
    rewrite interp_state_ret.
    reflexivity.
  Qed.

  (** [interp_imp] commutes with [bind]. *)
  Lemma interp_imp_bind: forall {R S E} (t : itree (ImpState +' E) R) (k: R -> itree (ImpState +' E) S) (g : env),
      run_state (interp_imp (ITree.bind t k)) g
    ≅ (ITree.bind (run_state (interp_imp t) g) (fun '(g',  x) => run_state (interp_imp (k x)) g')).
  Proof.
    intros.
    unfold interp_imp.
    unfold interp_map.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
  Admitted.

  Lemma interp_imp_iter: forall {E A B} (t : A -> itree (ImpState +' E) (A + B)) (a0 : A) (g: env),
    run_state (interp_imp (KTree.iter t a0)) g
                ≅ KTree.iter (fun '(g', a) =>
                                '(s,ab) <- run_state (interp_imp (t a)) g';;
                                 match ab with
                                 | inl a => ret (inl (s,a))
                                 | inr b => ret (inr (s,b))
                                 end
                             ) (g, a0).
  Proof.
    intros. unfold interp_imp, interp_map.
  Admitted.
  
  Instance run_state_proper {E A} : Proper (eqm ==> eq ==> eutt eq) (@run_state E A).
  Admitted.

  Instance run_state_proper_eqit {E A} : Proper (eqm ==> eq ==> eq_itree eq) (@run_state E A).
  Admitted.

  Instance interp_state_proper {T E F S} (h: forall T : Type, E T -> Monads.stateT S (itree F) T) : Proper (eutt eq ==> eqm) (State.interp_state h (T := T)).
  Admitted.

 (* Instance run_state_interp_interp *)

  Lemma interp_imp_trigger_get_var: forall (E: Type -> Type) (x: var) (g: env),
    run_state (interp_imp (trigger (GetVar x))) g ≈ (Ret (g, lookup_default x 0 g) : itree E (env * value)).
  Proof.
    intros. unfold interp_imp, interp_map. rewrite interp_trigger.
    (* rewrite tau_eutt. cbn. unfold cat, Cat_Handler, Handler.cat. *)
  Admitted.

  Theorem aequiv_example: aequiv (X - X) 0.
  Proof.
    unfold aequiv. intros s. unfold eval_aexp. simpl.
    rewrite interp_imp_ret.
    rewrite interp_imp_bind.
    rewrite interp_imp_trigger_get_var.
    rewrite bind_ret, interp_imp_bind, interp_imp_trigger_get_var, bind_ret, interp_imp_ret.
    rewrite Nat.sub_diag.
    reflexivity.
  Qed.

  Theorem bequiv_example: bequiv (X - X = 0) true.
  Proof.
    unfold bequiv, eval_bexp, denote_bexp.
    Local Opaque denote_aexp.
    cbn.
    intros.
    rewrite interp_imp_bind.
    rewrite (aequiv_example s).
    Local Transparent denote_aexp.
    unfold eval_aexp; cbn.
    rewrite interp_imp_ret, bind_ret.
    rewrite interp_imp_bind, interp_imp_ret, bind_ret.
    reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Simple Examples *)

  (** For examples of command equivalence, let's start by looking at
    some trivial program transformations involving [SKIP]: *)

  Theorem skip_left : forall c,
  cequiv
    (SKIP;;; c)%imp
    c.
  Proof.
    unfold cequiv. intros.
    cbn. rewrite interp_imp_bind. rewrite interp_imp_ret.
    rewrite bind_ret.
    reflexivity.
  Qed.

  Lemma bind_ret_unit_wildcard : forall {E} (t: itree E unit),
      ITree.bind t (fun _  => Ret tt) = ITree.bind t (fun x : unit => Ret x).
  Proof.
    intros.
    remember (fun _ : unit => Ret tt) eqn: lh_ret.
    remember (fun x : unit => Ret x) eqn: rh_ret.
    assert (i = i0). {
      rewrite lh_ret, rh_ret. apply functional_extensionality.
      destruct x. reflexivity.
    } rewrite H. reflexivity.
  Qed.


  Lemma interp_imp_bind_ret : forall {E R} (t: itree (ImpState +' E) R) (g: env),
    run_state (interp_imp (ITree.bind t (fun x : R => Ret x))) g ≅ run_state (interp_imp t) g.
  Proof.
    intros. unfold interp_imp. unfold interp_map.
    rewrite interp_bind. setoid_rewrite interp_state_bind.
    setoid_rewrite interp_ret. setoid_rewrite interp_state_ret.
    match goal with
      |- ITree.bind _ ?f ≅ _ => remember f as x
    end.                                      
    assert (x = fun st : env * R => Ret st).
    { apply functional_extensionality.
      intros. subst. destruct x0. reflexivity. }
    rewrite H. rewrite bind_ret2. reflexivity.  
   Qed. 
    
 
  Lemma interp_imp_bind_ret_unit : forall  {E} (t: itree (ImpState +' E) unit)  (g : env),
    run_state (interp_imp (ITree.bind t (fun _ : unit  => Ret tt))) g ≈ run_state (interp_imp t) g.
  Proof.
    intros.
    rewrite interp_imp_bind.
    rewrite <- (bind_ret2 (run_state _ _)).
    eapply eutt_clo_bind.
    rewrite bind_ret2.
    reflexivity.
    intros [? []] [? []] EQ; inversion EQ; subst.
    rewrite interp_imp_ret.
    reflexivity.
  Qed.

  (** **** Exercise: 2 stars, standard (skip_right)
    Prove that adding a [SKIP] after a command results in an
    equivalent program *)

  Theorem skip_right : forall c,
    cequiv
     (c ;;; SKIP)%imp
    c.
  Proof.
    (* TODO: Define LTac using eutt_clo_bind. *)
    unfold cequiv. intros. cbn.
     rewrite interp_imp_bind.
    rewrite <- (bind_ret2 (run_state _ _)).
    eapply eutt_clo_bind.
    rewrite bind_ret2.
    reflexivity.
    intros [? []] [? []] EQ; inversion EQ; subst.
    rewrite interp_imp_ret.
    reflexivity.
  Qed.

  
  Ltac simple_TEST H :=
    unfold cequiv; intros;
    unfold bequiv, eval_bexp in *; cbn in *;
    rewrite interp_imp_bind; try (rewrite H);
    rewrite interp_imp_ret, bind_ret;
    reflexivity.

  (** Similarly, here is a simple transformation that optimizes [TEST]
    commands: *)
  Theorem TEST_true_simple : forall c1 c2,
    cequiv
      (TEST BTrue THEN c1 ELSE c2 FI)%imp
      c1.
  Proof.
    simple_TEST H. 
  Qed.


  Theorem TEST_true: forall b c1 c2,
    bequiv b BTrue  ->
    cequiv
      (TEST b THEN c1 ELSE c2 FI)%imp
      c1.
  Proof.
    intros. simple_TEST H.
  Qed.
  
  Theorem TEST_false : forall b c1 c2,
    bequiv b BFalse ->
    cequiv
      (TEST b THEN c1 ELSE c2 FI)%imp
      c2.
  Proof.
    intros. simple_TEST H. 
  Qed. 

  (* IY: Uses eutt_clo_bind again.
     TODO: What's the best Ltac for eutt_clo_bind things? *)
  Theorem swap_if_branches : forall b e1 e2,
    cequiv
      (TEST b THEN e1 ELSE e2 FI)%imp
      (TEST BNot b THEN e2 ELSE e1 FI)%imp.
  Proof.
    unfold cequiv. intros. cbn.
    repeat rewrite interp_imp_bind.
    rewrite bind_bind. cbn.
    rewrite <- (bind_ret2 (run_state _ _)).
    eapply eutt_clo_bind. reflexivity.
    intros. subst. destruct u2. setoid_rewrite interp_imp_ret.
    rewrite bind_ret.
    destruct b0; cbn; reflexivity.
  Qed.

  Theorem WHILE_false : forall b c,
    bequiv b BFalse ->
    cequiv
      (WHILE b DO c END)%imp
      (SKIP)%imp.
  Proof.
    unfold cequiv. intros. unfold bequiv in H.
    unfold eval_bexp in H. cbn in H. cbn.
    rewrite interp_imp_ret. unfold while.
    rewrite interp_imp_iter.
    rewrite unfold_iter_ktree. cbn. 
    rewrite bind_bind. rewrite interp_imp_bind.
    rewrite bind_bind. cbn. rewrite H.
    repeat (rewrite interp_imp_ret, bind_ret).
    repeat rewrite bind_ret.
    reflexivity.
  Qed.          

  (* Up until now, we only had to think about behavioral equivalence
     of Imp programs. Now, we see an instance of reasoning about the 
     predicates of the program. Namely, we want to show the divergence
     of a program and characterize different types of divergent behaviors. 
   *)

  (* TODO: Define divergence *)
  (*
  Theorem WHILE_true_nonterm : forall b c st st',
      bequiv b BTrue ->
      ~ (st =[ WHILE b DO c END ]=> st'). 
  *)    

  Theorem WHILE_true : forall b c,
    bequiv b BTrue  ->
    cequiv
      (WHILE b DO c END)%imp
      (WHILE BTrue DO SKIP END)%imp.
  Proof.
    Admitted. 

  Theorem loop_unrolling : forall b c,
    cequiv
      (WHILE b DO c END)%imp
      (TEST b THEN (c ;;; WHILE b DO c END) ELSE SKIP FI)%imp.
  Proof.
    unfold cequiv. intros. cbn.
    unfold while. rewrite interp_imp_iter. cbn.
    rewrite interp_imp_bind.
    rewrite unfold_iter_ktree.
    repeat (rewrite bind_bind, interp_imp_bind).
    repeat rewrite bind_bind. cbn. eapply eutt_clo_bind.
    reflexivity.
    intros.
    destruct u1, u2. destruct b0.
    - repeat (rewrite interp_imp_bind, bind_bind).
      inversion H; subst.
      repeat (rewrite interp_imp_bind, bind_bind).
      rewrite interp_imp_bind. 
      eapply eutt_clo_bind. reflexivity.
      intros. subst. destruct u2.
      rewrite interp_imp_ret. repeat rewrite bind_ret.
      rewrite tau_eutt. rewrite unfold_iter_ktree.
      repeat (rewrite bind_bind, interp_imp_bind).
      rewrite bind_bind. rewrite interp_imp_iter.
      rewrite unfold_iter_ktree. cbn.
      repeat (rewrite bind_bind, interp_imp_bind).
      rewrite bind_bind. reflexivity.
    - rewrite interp_imp_ret. repeat rewrite bind_ret.
      inversion H; subst. rewrite interp_imp_ret.
      reflexivity.
  Qed. 
    
