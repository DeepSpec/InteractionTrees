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
     Program
     Logic.FunctionalExtensionality
     RelationClasses.
From ExtLib Require Import
     Structures.Monad
     Data.Map.FMapAList. 

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

  Instance run_state_proper {E A} : Proper (eqm ==> eq ==> eutt eq) (@run_state E A).
  Proof.
    cbv; intros; subst; auto.
  Qed.

  Instance interp_state_proper {T E F S} (h: forall T : Type, E T -> Monads.stateT S (itree F) T) : Proper (eutt eq ==> eqm) (State.interp_state h (T := T)).
  Proof.
    einit. ecofix CIH. intros.
    rewrite !unfold_interp_state. punfold H0. red in H0.
    induction H0; intros; subst; simpl; pclearbot.
    - eret.
    - etau.
    - ebind. econstructor; [reflexivity|].
      intros; subst.
      etau. ebase.
    - rewrite tau_eutt, unfold_interp_state; eauto.
    - rewrite tau_eutt, unfold_interp_state; eauto.
  Qed.

  (* This should move to the library *)
  Lemma eq_itree_clo_bind {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) {U1 U2 UU} t1 t2 k1 k2
        (EQT: @eq_itree E U1 U2 UU t1 t2)
        (EQK: forall u1 u2, UU u1 u2 -> eq_itree RR (k1 u1) (k2 u2)):
    eq_itree RR (x <- t1;; k1 x) (x <- t2;; k2 x).
  Proof.
    intros. ginit. guclo eqit_clo_bind.
    econstructor; eauto. intros; subst. gfinal. right. apply EQK. eauto.
  Qed.

  (** [interp_imp] commutes with [bind]. *)
  Lemma interp_imp_bind: forall {R S E} (t : itree (ImpState +' E) R) (k: R -> itree (ImpState +' E) S) (g : env),
      run_state (interp_imp (ITree.bind t k)) g
                ≈ (ITree.bind (run_state (interp_imp t) g) (fun '(g',  x) => run_state (interp_imp (k x)) g')).
  Proof.
    intros.
    unfold interp_imp.
    rewrite interp_bind.
    setoid_rewrite interp_state_bind.
    apply eutt_clo_bind with (UU := eq).
    reflexivity.
    intros [] [] EQ; inv EQ; reflexivity.
  Qed.
                               
  Lemma interp_imp_iter: forall {E A B} (t : A -> itree (ImpState +' E) (A + B)) (a0 : A) (g: env),
    run_state (interp_imp (KTree.iter t a0)) g
                ≈ KTree.iter (fun '(g', a) =>
                                '(s,ab) <- run_state (interp_imp (t a)) g';;
                                 match ab with
                                 | inl a => ret (inl (s,a))
                                 | inr b => ret (inr (s,b))
                                 end
                             ) (g, a0).
  Proof.
    intros.
    unfold interp_imp. cbn.
    rewrite interp_iter. unfold interp_map.
   
  Admitted. 

  Lemma interp_imp_trigger_get_var: forall (E: Type -> Type) (x: var) (g: env),
    run_state (interp_imp (trigger (GetVar x))) g ≈ (Ret (g, lookup_default x 0 g) : itree E (env * value)).
  Proof.
    intros. unfold interp_imp, interp_map. rewrite interp_trigger.
    setoid_rewrite unfold_interp_state.
    cbn. rewrite bind_ret. rewrite tau_eutt.
    rewrite 2 interp_state_bind. rewrite bind_bind.
    cbn. repeat rewrite interp_state_ret, bind_ret.
    cbn. rewrite tau_eutt. rewrite interp_ret.
    rewrite interp_state_ret. reflexivity. 
  Qed.     

  Lemma interp_imp_trigger_set_var: forall (E: Type -> Type) (g: env) (x: var) (v: value),
      run_state (interp_imp (trigger (SetVar x v))) g ≈ (Ret (alist_add RelDec_string x v g, tt) : itree E (env * unit)).
  Proof.
    intros. unfold interp_imp, interp_map. rewrite interp_trigger.
    setoid_rewrite unfold_interp_state.
    cbn. rewrite bind_ret. rewrite tau_eutt.
    rewrite 2 interp_state_bind. rewrite bind_bind.
    cbn. repeat rewrite interp_state_ret, bind_ret.
    cbn. rewrite tau_eutt. rewrite interp_ret.
    rewrite interp_state_ret. reflexivity.
  Qed. 

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
    run_state (interp_imp (ITree.bind t (fun x : R => Ret x))) g ≈ run_state (interp_imp t) g.
  Proof.
    intros. unfold interp_imp. unfold interp_map.
    rewrite interp_bind. setoid_rewrite interp_state_bind.
    setoid_rewrite interp_ret. setoid_rewrite interp_state_ret.
    match goal with
      |- ITree.bind _ ?f ≈ _ => remember f as x
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

  (** * Divergence of Imp programs *

     Up until now, we only had to think about behavioral equivalence
     of Imp programs. Now, we see an instance of reasoning about the
     predicates of the program. Namely, we want to show the divergence
     of a program and characterize different types of divergent behaviors.
   *)

  (* TODO: Define divergence *)

  (*Theorem WHILE_true_nonterm : forall b c st st',
      bequiv b BTrue ->
      ~ (st =[ WHILE b DO c END ]=> st'). *)


  Theorem WHILE_true : forall b c,
    bequiv b BTrue  ->
    cequiv
      (WHILE b DO c END)%imp
      (WHILE BTrue DO SKIP END)%imp.
  Proof.
    unfold cequiv. intros. cbn.
    unfold while. rewrite 2 interp_imp_iter. cbn.
    unfold KTree.iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
    rewrite 2 unfold_iter.
    repeat rewrite (bind_bind, interp_imp_bind). rewrite 2 bind_bind.
    rewrite 2 interp_imp_bind. rewrite 2 bind_bind.
    rewrite interp_imp_ret, bind_ret.
    rewrite interp_imp_bind, interp_imp_ret, bind_bind, bind_ret.
    rewrite interp_imp_ret, bind_ret, bind_ret. cbn.
    rewrite tau_eutt.
    rewrite unfold_iter.
    rewrite bind_bind, interp_imp_bind.
    (* This will go nowhere. *)
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
    destruct u1, u2. inversion H; subst.
    (* This is the first time we _needed_ to reason about the program structure! *)
    destruct b1.
    - (* Then, we go back to rewriting ITrees *)
      repeat (rewrite interp_imp_bind, bind_bind).
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
      rewrite interp_imp_ret.
      reflexivity.
  Qed.

  Theorem seq_assoc : forall c1 c2 c3,
    cequiv ((c1;;;c2);;;c3)%imp (c1;;;(c2;;;c3))%imp.
  Proof.
    unfold cequiv. intros. cbn.
    rewrite 3 interp_imp_bind. rewrite bind_bind.
    eapply eutt_clo_bind. reflexivity.
    intros.
    destruct u1, u2. inversion H; subst.
    rewrite interp_imp_bind. reflexivity.
  Qed.
  
  Theorem identity_assignment : forall x,
    cequiv
      (x ::= x)%imp
      (SKIP)%imp.
  Proof.
    unfold cequiv. intros. cbn.
    rewrite interp_imp_bind, interp_imp_ret.
    rewrite interp_imp_trigger_get_var, bind_ret.
    rewrite interp_imp_trigger_set_var. apply eqit_Ret.
    rewrite alist_add_lookup_eq. reflexivity. 
  Qed.

  Theorem assign_aequiv : forall (x : string) e,
    aequiv x e ->
    cequiv (SKIP)%imp (x ::= e)%imp.
  Proof.
    unfold cequiv. intros. cbn. unfold aequiv in H.
    rewrite interp_imp_ret, interp_imp_bind.
    unfold eval_aexp in H. setoid_rewrite <- H.
    simpl. rewrite interp_imp_trigger_get_var.
    rewrite bind_ret.
    rewrite -> interp_imp_trigger_set_var.
    reflexivity. constructor.
  Qed.


  (* ################################################################# *)
  (** * Properties of Behavioral Equivalence *)

  (** We next consider some fundamental properties of program
    equivalence. *)

  Lemma refl_aequiv : forall (a : aexp), aequiv a a.
  Proof.
    intros a st. reflexivity.  Qed.

  Lemma sym_aequiv : forall (a1 a2 : aexp),
    aequiv a1 a2 -> aequiv a2 a1.
  Proof.
    intros a1 a2 H. intros st. symmetry. apply H.  Qed.

  Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
    aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
  Proof.
    unfold aequiv. intros a1 a2 a3 H12 H23 st.
    rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

  Lemma refl_bequiv : forall (b : bexp), bequiv b b.
  Proof.
    unfold bequiv. intros b st. reflexivity.  Qed.

  Lemma sym_bequiv : forall (b1 b2 : bexp),
    bequiv b1 b2 -> bequiv b2 b1.
  Proof.
    unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

  Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
    bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
  Proof.
    unfold bequiv. intros b1 b2 b3 H12 H23 st.
    rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

  (* These next two lemmas are different from the original Imp_Equiv. *)
  Lemma refl_cequiv : forall (c : com), cequiv c c.
  Proof.
    unfold cequiv. intros. reflexivity. Qed.

  (* Slightly simpler proof here, because we don't need to reason
     about the states. *)
  Lemma sym_cequiv : forall (c1 c2 : com),
    cequiv c1 c2 -> cequiv c2 c1.
  Proof.
    unfold cequiv. intros. rewrite H.
    reflexivity.
  Qed.

  Lemma trans_cequiv : forall (c1 c2 c3 : com),
    cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
  Proof.
    unfold cequiv. intros.
    rewrite H, H0. reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Behavioral Equivalence Is a Congruence *)

  (** Less obviously, behavioral equivalence is also a _congruence_.
      That is, the equivalence of two subprograms implies the
      equivalence of the larger programs in which they are embedded:
                aequiv a1 a1'
        -----------------------------
        cequiv (x ::= a1) (x ::= a1')
                cequiv c1 c1'
                cequiv c2 c2'
           --------------------------
           cequiv (c1;;c2) (c1';;c2')
      ... and so on for the other forms of commands. *)

  (** (Note that we are using the inference rule notation here not
      as part of a definition, but simply to write down some valid
      implications in a readable format. We prove these implications
      below.) *)

  (** We will see a concrete example of why these congruence
      properties are important in the following section (in the proof of
      [fold_constants_com_sound]), but the main idea is that they allow
      us to replace a small part of a large program with an equivalent
      small part and know that the whole large programs are equivalent
      _without_ doing an explicit proof about the non-varying parts --
      i.e., the "proof burden" of a small change to a large program is
      proportional to the size of the change, not the program. *)

  Theorem CAss_congruence : forall x a1 a1',
    aequiv a1 a1' ->
    cequiv (CAss x a1) (CAss x a1').
  Proof.
    unfold cequiv. intros. unfold aequiv in H.
    cbn. rewrite 2 interp_imp_bind. rewrite H.
    eapply eutt_clo_bind. reflexivity.
    intros. rewrite H0. reflexivity.
  Qed.

  (* Needed to define this equivalence instance for CWhile_congruence. *)
  Global Instance sum_rel_refl {R S : Type} {RR : R -> R -> Prop} {SS : S -> S -> Prop} `{Reflexive _ RR} `{Reflexive _ SS}: Reflexive (sum_rel RR SS).
  Proof. red. destruct x; constructor; auto. Qed.


  Theorem CWhile_congruence : forall b1 b1' c1 c1',
    bequiv b1 b1' -> cequiv c1 c1' ->
    cequiv (WHILE b1 DO c1 END)%imp (WHILE b1' DO c1' END)%imp.
  Proof.
    unfold cequiv. intros. unfold bequiv in H. cbn.
    unfold while.
    rewrite 2 interp_imp_iter. cbn.
    unfold KTree.iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
    eapply eutt_iter'. intros.
    rewrite H1; clear H1. destruct j2.
    rewrite 2 interp_imp_bind. rewrite 2 bind_bind. rewrite H.
    2, 3 : reflexivity.
    eapply eutt_clo_bind. reflexivity.
    intros. rewrite H1; clear H1.
    eapply eutt_clo_bind. destruct u2. destruct b.
    rewrite 2 interp_imp_bind. rewrite H0. reflexivity.
    reflexivity.
    intros. rewrite H1; clear H1. destruct u3. destruct s0; reflexivity.
    Qed.



  (* CSeq_congruence, CIf_congruence are super clean. *)
  Theorem CSeq_congruence : forall c1 c1' c2 c2',
    cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1;;;c2)%imp (c1';;;c2')%imp.
  Proof.
    unfold cequiv. intros. simpl.
    rewrite 2 interp_imp_bind.
    eapply eutt_clo_bind. rewrite H. reflexivity.
    intros. rewrite H1; clear H1. destruct u2.
    rewrite H0. reflexivity.
  Qed.

  Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (TEST b THEN c1 ELSE c2 FI)%imp
           (TEST b' THEN c1' ELSE c2' FI)%imp.
  Proof.
    unfold bequiv, cequiv. intros. simpl.
    rewrite 2 interp_imp_bind.
    eapply eutt_clo_bind. rewrite H.
    reflexivity.
    intros. rewrite H2. clear H2. destruct u2.
    destruct b0; try rewrite H0; try rewrite H1; reflexivity.
  Qed.

  Example congruence_example:
    cequiv
      (* Program 1: *)
      (X ::= 0;;;
       TEST X = 0
       THEN
         Y ::= 0
       ELSE
         Y ::= 42
       FI)%imp
      (* Program 2: *)
      (X ::= 0;;;
       TEST X = 0
       THEN
         Y ::= X - X   (* <--- Changed here *)
       ELSE
         Y ::= 42
       FI)%imp.
  Proof.
    apply CSeq_congruence.
    - apply refl_cequiv.
    - apply CIf_congruence.
      + apply refl_bequiv.
      + apply CAss_congruence. unfold aequiv. simpl.
        * symmetry. apply aequiv_example.
      + apply refl_cequiv.
   Qed.

  (* ################################################################# *)
  (** * Program Transformations *)

  (** A _program transformation_ is a function that takes a program as
      input and produces some variant of the program as output.
      Compiler optimizations such as constant folding are a canonical
      example, but there are many others. *)

  (** A program transformation is _sound_ if it preserves the
      behavior of the original program. *)

  Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
    forall (a : aexp),
      aequiv a (atrans a).

  Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
    forall (b : bexp),
      bequiv b (btrans b).

  Definition ctrans_sound (ctrans : com -> com) : Prop :=
    forall (c : com),
      cequiv c (ctrans c).

  (* ================================================================= *)
  (** ** The Constant-Folding Transformation *)

  (** An expression is _constant_ when it contains no variable
      references.
      Constant folding is an optimization that finds constant
      expressions and replaces them by their values. *)

  Fixpoint fold_constants_aexp (a : aexp) : aexp :=
    match a with
    | ANum n       => ANum n
    | AId x        => AId x
    | APlus a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2)
      with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
    | AMinus a1 a2 =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2)
      with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
    | AMult a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2)
      with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
    end.

  Example fold_aexp_ex1 :
    fold_constants_aexp ((1 + 2) * X)
    = (3 * X)%imp.
  Proof. reflexivity. Qed.

  Example fold_aexp_ex2 :
    fold_constants_aexp (X - ((0 * 6) + Y))%imp = (X - (0 + Y))%imp.
  Proof. reflexivity. Qed.


  Fixpoint fold_constants_bexp (b : bexp) : bexp :=
    match b with
    | BTrue        => BTrue
    | BFalse       => BFalse
    | BEq a1 a2  =>
        match (fold_constants_aexp a1,
              fold_constants_aexp a2) with
        | (ANum n1, ANum n2) =>
            if n1 =? n2 then BTrue else BFalse
        | (a1', a2') =>
            BEq a1' a2'
        end
    | BLe a1 a2  =>
        match (fold_constants_aexp a1,
              fold_constants_aexp a2) with
        | (ANum n1, ANum n2) =>
            if n1 <=? n2 then BTrue else BFalse
        | (a1', a2') =>
            BLe a1' a2'
        end
    | BNot b1  =>
        match (fold_constants_bexp b1) with
        | BTrue => BFalse
        | BFalse => BTrue
        | b1' => BNot b1'
        end
    | BAnd b1 b2  =>
        match (fold_constants_bexp b1,
              fold_constants_bexp b2) with
        | (BTrue, BTrue) => BTrue
        | (BTrue, BFalse) => BFalse
        | (BFalse, BTrue) => BFalse
        | (BFalse, BFalse) => BFalse
        | (b1', b2') => BAnd b1' b2'
        end
    end.

  Example fold_bexp_ex1 :
    fold_constants_bexp (true && ~(false && true))%imp
    = true.
  Proof. reflexivity. Qed.

  Example fold_bexp_ex2 :
    fold_constants_bexp ((X = Y) && (0 = (2 - (1 + 1))))%imp
    = ((X = Y) && true)%imp.
  Proof. reflexivity. Qed.

  (** To fold constants in a command, we apply the appropriate folding
      functions on all embedded expressions. *)

  Open Scope imp.
  Fixpoint fold_constants_com (c : com) : com :=
    match c with
    | SKIP      =>
        SKIP
    | x ::= a   =>
        x ::= (fold_constants_aexp a)
    | c1 ;;; c2  =>
        (fold_constants_com c1) ;;; (fold_constants_com c2)
    | TEST b THEN c1 ELSE c2 FI =>
        match fold_constants_bexp b with
        | BTrue  => fold_constants_com c1
        | BFalse => fold_constants_com c2
        | b' => TEST b' THEN fold_constants_com c1
                      ELSE fold_constants_com c2 FI
        end
    | WHILE b DO c END =>
        match fold_constants_bexp b with
        | BTrue => WHILE BTrue DO SKIP END
        | BFalse => SKIP
        | b' => WHILE b' DO (fold_constants_com c) END
        end
    end.
  Close Scope imp.


  Example fold_com_ex1 :
    fold_constants_com
      (* Original program: *)
      (X ::= 4 + 5;;;
      Y ::= X - 3;;;
      TEST (X - Y) = (2 + 4) THEN SKIP
      ELSE Y ::= 0 FI;;;
      TEST 0 <= (4 - (2 + 1)) THEN Y ::= 0
      ELSE SKIP FI;;;
      WHILE Y = 0 DO
        X ::= X + 1
      END)%imp
    = (* After constant folding: *)
      (X ::= 9;;;
      Y ::= X - 3;;;
      TEST (X - Y) = 6 THEN SKIP
      ELSE Y ::= 0 FI;;;
      Y ::= 0;;;
      WHILE Y = 0 DO
        X ::= X + 1
      END)%imp.
  Proof. reflexivity. Qed.


  (* ================================================================= *)
  (** ** Soundness of Constant Folding *)

  (** Now we need to show that what we've done is correct. *)

  (** Here's the proof for arithmetic expressions: *)

  Theorem fold_constants_aexp_sound :
    atrans_sound fold_constants_aexp.
  Proof.
    unfold atrans_sound. intros a. unfold aequiv.
    unfold eval_aexp in *.
    induction a; simpl;
      (* ANum and AId follow immediately *)
      try reflexivity.
    - destruct (fold_constants_aexp a1); destruct (fold_constants_aexp a2);
      simpl; intros; try (rewrite interp_imp_bind, interp_imp_ret);
      try rewrite IHa1; try rewrite IHa2; cbn; repeat rewrite interp_imp_ret, bind_ret;
        rewrite interp_imp_bind.
      try rewrite IHa2. cbn. rewrite interp_imp_ret.
      rewrite bind_ret. rewrite interp_imp_ret. reflexivity.
      (* TODO: Very simple rewrites, should define Ltacs on these *)
  Admitted.
