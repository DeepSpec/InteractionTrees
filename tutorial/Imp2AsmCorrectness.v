(** * Functional correctness of the compiler *)

(** We finally turn to proving our compiler correct.

    We express the result as a (weak) bisimulation between
    the [itree] resulting from the denotation of the source
    _Imp_ statement and the denotation of the compiled _Asm_
    program. This weak bisimulation is a _up-to-tau_ bisimulation.
    More specifically, we relate the itrees after having
    interpreted the [Locals] events contained in the trees into
    the state monad, and run them.

    The proof is essentially structured as followed:
    - a simulation relation is defined to relate the local
    environments during the simulation. This relation is
    strengthened into a second one used during the simulation
    of expressions.
    - the desired bisimulation is defined to carry out the
    the simulation invariant into a up-to-tau after interpretation
    of [Locals] relation. Once again a slightly different
    bisimulation is defined when handling expressions.
    - Linking is proved in isolation: the "high level" control
    flow combinators for _Asm_ defined in [Imp2Asm.v] are
    proved correct in the same style as the elemntary ones
    from [AsmCombinators.v].
    - Finally, all the pieces are tied together to prove the
    correctness.

    We emphasize the following aspects of the proof:
    - Despite establishing a termination-sensitive correctness
    result over Turing-complete languages, we have not written
    a single [cofix]. All coinductive reasoning is internalized
    into the [itree] library.
    - We have separated the control-flow-related reasoning from
    the functional correctness one. In particular, the low-level
    [asm] combinators are entirely reusable, and the high-level
    ones are only very loosely tied to _Imp_.
    - All reasoning is equational. In particular, reasoning at the
    level of [ktree]s rather than introducing the entry label and
    trying to reason at the level of [itree]s ease sensibly the pain
    by reducing the amount of binders under which we need to work.
    - We transparently make use of the heterogenous bisimulation provided
    by the [itree] library to relate computations of _Asm_ expressions
    that return an environment and a [unit] value to ones of _Imp_
    that return an environment and an [Imp.value].
*)

(* begin hide *)
Require Import Imp Asm Utils_tutorial AsmCombinators Imp2Asm.

Require Import Psatz.

From Coq Require Import
     Strings.String
     Morphisms
     ZArith
     Setoid
     RelationClasses.

From ITree Require Import
     ITree
     Basics.Category
     Basics.Function
     Core.KTreeFacts
     Interp.MorphismsFacts
     Interp.RecursionFacts
     Effects.StateFacts
     Effects.Map.

Import ITreeNotations.

From ExtLib Require Import
     Core.RelDec
     Structures.Monad
     Structures.Maps
     Programming.Show
     Data.Map.FMapAList.

Import ListNotations.
Open Scope string_scope.

Import CatNotations.
Local Open Scope cat.

(* end hide *)

(* ================================================================= *)
(** ** Hiding mangling of variables. *)

(** [varOf] and [gen_tmp] are injective. *)
Section GEN_TMP.

  Lemma gen_tmp_inj: forall n m, m <> n -> gen_tmp m <> gen_tmp n.
  Proof.
    intros n m ineq; intros abs; apply ineq.
    apply string_of_nat_inj in ineq; inversion abs; easy.
  Qed.

  Lemma varOf_inj: forall n m, m <> n -> varOf m <> varOf n.
  Proof.
    intros n m ineq abs; inv abs; easy.
  Qed.

End GEN_TMP.

Opaque gen_tmp.
Opaque varOf.

(* ================================================================= *)
(** ** Simulation relations *)

(** The compiler is proved correct by constructing a (itree) bisimulation between
    the source program and its compilation.
    As is traditional, we define, to this end, a simulation relation [Renv]. Since the
    bisimulation will take place after handling of the local environment, [Renv]
    relates two [alist var value] environments.
 *)

Section Simulation_Relation.

  (** ** Definition of the simulation relations *)

  (** Relates a source variable to its mangled counterpart in _Asm_. *)
  Variant Rvar : var -> var -> Prop :=
  | Rvar_var v : Rvar (varOf v) v.

  (** The simulation relation for evaluation of statements.
      The relation relates two environments of type [alist var value].
      The source and target environments exactly agree on user variables.
   *)
  Definition Renv (g_asm g_imp : alist var value) : Prop :=
    forall k_asm k_imp, Rvar k_asm k_imp ->
                   forall v, alist_In k_imp g_imp v <-> alist_In k_asm g_asm v.

 (** The simulation relation for evaluation of expressions.
     The relation also relates two environments of type [alist var value],
     but additionally the returned value at the _Imp_ level. The _Asm_
     side does not carry a [value], but a [unit], since its denotation
     does not return any [value].
     The [sim_rel] relation is parameterized by the state of the [asm] environment
     before the step, and the name of the variable used to store
     the result.
     It enforces three conditions:
     - [Renv] on the environments, ensuring that evaluation of expressions
     does not corrupt user variables;
     - Agreement on the computed value, i.e. the returned value [v] is stored at
     the assembly level in the expected temporary;
     - The "stack" of temporaries used to compute intermediate results is left untouched.
  *) 
  Definition sim_rel g_asm n: alist var value * unit -> alist var value * value -> Prop :=
    fun '(g_asm', _) '(g_imp',v) =>
      Renv g_asm' g_imp' /\            (* we don't corrupt any of the imp variables *)
      alist_In (gen_tmp n) g_asm' v /\ (* we get the right value *)
      (forall m, m < n -> forall v,              (* we don't mess with anything on the "stack" *)
            alist_In (gen_tmp m) g_asm v <-> alist_In (gen_tmp m) g_asm' v).


  (** ** Facts on the simulation relations *)

  (** [Renv] is stable by updates to temporaries. *)
  Lemma Renv_add: forall g_asm g_imp n v,
      Renv g_asm g_imp -> Renv (alist_add (gen_tmp n) v g_asm) g_imp.
  Proof.
    repeat intro.
    destruct (k_asm ?[ eq ] (gen_tmp n)) eqn:EQ.
    rewrite rel_dec_correct in EQ; subst; inv H0.
    rewrite <- neg_rel_dec_correct in EQ.
    rewrite (H _ _ H0).
    apply In_add_ineq_iff; auto.
  Qed.

  (** [Renv] entails agreement of lookup of user variables. *)
  Lemma Renv_find:
    forall g_asm g_imp x,
      Renv g_asm g_imp ->
      alist_find x g_imp = alist_find (varOf x) g_asm.
  Proof.
    intros.
    destruct (alist_find x g_imp) eqn:LUL, (alist_find (varOf x) g_asm) eqn:LUR; auto.
    - eapply H in LUL; [| constructor].
      rewrite LUL in LUR; auto.
    - eapply H in LUL; [| constructor].
      rewrite LUL in LUR; auto.
    - erewrite <- (H (varOf x) x (Rvar_var x) v) in LUR.
      rewrite LUR in LUL; inv LUL.
  Qed.      

  (** [sim_rel] can be initialized from [Renv]. *)
  Lemma sim_rel_add: forall g_asm g_imp n v,
      Renv g_asm g_imp ->
      sim_rel g_asm n (alist_add (gen_tmp n) v g_asm, tt) (g_imp, v).
  Proof.
    intros.
    split; [| split].
    - apply Renv_add; assumption.
    - apply In_add_eq.
    - intros m LT v'.
      apply In_add_ineq_iff, gen_tmp_inj; lia.
  Qed.

  (** [Renv] can be recovered from [sim_rel]. *)
  Lemma sim_rel_Renv: forall g_asm n s1 v1 s2 v2,
      sim_rel g_asm n (s1,v1) (s2,v2) -> Renv s1 s2.
  Proof.
    intros ? ? ? ? ? ? H; apply H.
  Qed.

  Lemma sim_rel_find_tmp_n:
    forall g_asm n g_asm' g_imp' v,
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      alist_In (gen_tmp n) g_asm' v.
  Proof.
    intros ? ? ? ? ? [_ [H _]]; exact H. 
  Qed.

  (** [sim_rel] entails agreement of lookups in the "stack" between its argument
      and the current Asm environement *)
  Lemma sim_rel_find_tmp_lt_n:
    forall g_asm n m g_asm' g_imp' v,
      m < n ->
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      alist_find (gen_tmp m) g_asm = alist_find (gen_tmp m) g_asm'.
  Proof.
    intros ? ? ? ? ? ? ineq [_ [_ H]].
    match goal with
    | |- _ = ?x => destruct x eqn:EQ
    end.
    setoid_rewrite (H _ ineq); auto.
    match goal with
    | |- ?x = _ => destruct x eqn:EQ'
    end; [| reflexivity].
    setoid_rewrite (H _ ineq) in EQ'.
    rewrite EQ' in EQ; easy.
  Qed.

  Lemma sim_rel_find_tmp_n_trans:
    forall g_asm n g_asm' g_asm'' g_imp' g_imp'' v v',
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      sim_rel g_asm' (S n) (g_asm'', tt) (g_imp'',v') ->
      alist_In (gen_tmp n) g_asm'' v.
  Proof.
    intros.
    generalize H; intros LU; apply sim_rel_find_tmp_n in LU.
    unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto.
  Qed.

  (** [Renv] is preserved by assignment.
   *)
  Lemma Renv_write_local:
    forall (k : Imp.var) (g_asm g_imp : alist var value) v,
      Renv g_asm g_imp ->
      Renv (alist_add (varOf k) v g_asm) (alist_add k v g_imp).
  Proof.
    intros k m m' v HRel k_asm k_imp Hk v'.
    specialize (HRel _ _ Hk v').
    inv Hk.
    unfold alist_add, alist_In; simpl.
    do 2 flatten_goal;
      repeat match goal with
             | h: _ = true |- _ => rewrite rel_dec_correct in h
             | h: _ = false |- _ => rewrite <- neg_rel_dec_correct in h
             end; try subst.
    - tauto.
    - tauto.
    - apply varOf_inj in Heq; easy.
    - setoid_rewrite In_remove_In_ineq_iff; eauto using RelDec_string_Correct.
  Qed.

  (** [sim_rel] can be composed when proving binary arithmetic operators. *)
  Lemma sim_rel_binary_op:
    forall (g_asm g_asm' g_asm'' g_imp' g_imp'' : alist var value)
      (n v v' : nat)
      (Hsim : sim_rel g_asm n (g_asm', tt) (g_imp', v))
      (Hsim': sim_rel g_asm' (S n) (g_asm'', tt) (g_imp'', v'))
      (op: nat -> nat -> nat),
      sim_rel g_asm n (alist_add (gen_tmp n) (op v v') g_asm'', tt) (g_imp'', op v v').
  Proof.
    intros.
    split; [| split].
    {
      eapply Renv_add, sim_rel_Renv; eassumption.
    }
    {
      apply In_add_eq.
    }
    {
      intros m LT v''.
      rewrite <- In_add_ineq_iff; [| apply gen_tmp_inj; lia].
      destruct Hsim as [_ [_ Hsim]].
      destruct Hsim' as [_ [_ Hsim']].
      rewrite Hsim; [| auto with arith].
      rewrite Hsim'; [| auto with arith].
      reflexivity.
    }
  Qed.

End Simulation_Relation.

(* ================================================================= *)
(** ** Bisimulation *)

(** We now make precise the bisimulation established to show the correctness
    of the compiler.
    Naturally, we cannot establish a _strong bisimulation_ between the source
    program and the target program: the [asm] counterpart performs "more
    steps" when evaluating expressions.
    The appropriate notion is of course the _equivalence up to tau_. However,
    the [itree] structures put in evidence a very naturaly hierarchy of notions
    of correctness.
    Since the [asm] programs perform more manipulations of their local
    environment, we cannot hope to relate the trees containing [Locals] events,
    we first need to interpret them.
    However, since it does not introduce any manipulation of the heap, we
    _can_ prove the result without interpreting the [Memory] events.
    Of course this example is rather contrived, owing to the simplicity of the
    compiler. Nonetheless, it makes a lot of sense when considering optimization:
    one can see the handling of events as bits of the memory model, and 
    therefore have a framework to prove some optimizations correct with respect
    to any memory model, i.e. before handling, while others with respect to
    concrete memory model, i.e. after handling.
 *)

Section Eq_Locals.

  Context {E': Type -> Type}.
  Notation E := (Locals +' E').

  (** [interp_locals] handle [Locals] into the [envE] effects, and then
      run these effects into the state monad. *)
  Definition interp_locals {R: Type} (t: itree E R) (s: alist var value)
    : itree E' (alist var value * R) :=
    run_map (interp (bimap evalLocals (id_ _)) t) s.

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_locals {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (alist var value) R) (prod _ R) eq)
           interp_locals.
  Proof.
    repeat intro.
    unfold interp_locals.
    unfold run_map.
    rewrite H0. eapply eutt_interp_state; auto.
    rewrite H; reflexivity.
  Qed.

  (** [interp_locals] commutes with [bind]. *)
  Lemma interp_locals_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (s: alist var value),
      @eutt E' _ _ eq
            (interp_locals (ITree.bind t k) s)
            (ITree.bind (interp_locals t s) (fun s' => interp_locals (k (snd s')) (fst s'))).
  Proof.
    intros.
    unfold interp_locals.
    unfold run_map.
    rewrite interp_bind.
    rewrite interp_state_bind.
    reflexivity.
  Qed.

  (** Definition of our bisimulation relation.
      As previously explained, it relates up-to-tau two [itree]s after having
      interpreted their [Locals] event.
      We additionally bake into it a simulation relation taken in parameter:
      - Local events are interpreted from related states.
      - Returned values must contain related states, as well as computed datas
      related by another relation [RR] taken in parameter.
      In our case, we specialize [RR] to equality since both trees return [unit],
      and [Renv_] to [Renv].
   *)
  (* SAZ: TODO - rename some of the variables here to make it clear what are environemnts, etc. 
     maybe rename a and b to use pattern binding: a == '(src_env, src_res)
  *)
  Definition eq_locals {R1 R2} (RR : R1 -> R2 -> Prop)
             (Renv_ : _ -> _ -> Prop)
             (t1: itree E R1) (t2: itree E R2): Prop :=
    forall g1 g2,
      Renv_ g1 g2 ->
      eutt (fun a (b : alist var value * R2) => Renv_ (fst a) (fst b) /\ RR (snd a) (snd b))
           (interp_locals t1 g1)
           (interp_locals t2 g2).

  (** [eq_locals] is compatible with [eutt]. *)
  Global Instance eutt_eq_locals (Renv_ : _ -> _ -> Prop) {R} RR :
    Proper (eutt eq ==> eutt eq ==> iff) (@eq_locals R R RR Renv_).
  Proof.
    repeat intro.
    split; repeat intro.
    - rewrite <- H, <- H0; auto.
    - rewrite H, H0; auto.
  Qed.

  (** [eq_locals] commutes with [bind]  *)
  Definition eq_locals_bind_gen (Renv_ : _ -> _ -> Prop)
             {R1 R2 S1 S2} (RR : R1 -> R2 -> Prop)
             (RS : S1 -> S2 -> Prop) :
    forall t1 t2,
      eq_locals RR Renv_ t1 t2 ->
      forall k1 k2,
        (forall r1 r2, RR r1 r2 -> eq_locals RS Renv_ (k1 r1) (k2 r2)) ->
        eq_locals RS Renv_ (t1 >>= k1) (t2 >>= k2).
  Proof.
    repeat intro.
    rewrite 2 interp_locals_bind.
    eapply eutt_bind_gen.
    { eapply H; auto. }
    intros. eapply H0; destruct H2; auto.
  Qed.

  (** [eq_locals] is compatible with [loop]. *)
  Lemma eq_locals_loop {A B C} x (t1 t2 : C + A -> itree E (C + B)) :
    (forall l, eq_locals eq Renv (t1 l) (t2 l)) ->
    eq_locals eq Renv (loop t1 x) (loop t2 x).
  Proof.
    unfold eq_locals, interp_locals, run_map.
    intros. unfold loop.
    rewrite 2 interp_loop.
    eapply interp_state_loop; auto.
  Qed.

  (** [sim_rel] at [n] entails that [GetVar (gen_tmp n)] gets interpreted
      as returning the same value as the _Imp_ related one.
   *)
  Lemma sim_rel_get_tmp0:
    forall n g_asm0 g_asm g_imp v,
      sim_rel g_asm0 n (g_asm,tt) (g_imp,v) ->
      interp_locals (send (GetVar (gen_tmp n))) g_asm ≈ Ret (g_asm,v).
  Proof.
    intros.
    destruct H as [_ [eq _]].
    unfold interp_locals.
    unfold send.
    rewrite interp_send.
    rewrite tau_eutt.
    cbn.
    unfold run_map.
    unfold evalLocals, CategoryOps.cat, Cat_Handler, Handler.cat.
    unfold lookup_def; cbn.
    rewrite unfold_interp_state; cbn.
    rewrite tau_eutt.
    rewrite map_bind.
    setoid_rewrite bind_ret.
    setoid_rewrite interp_ret.
    unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.hsend.
    rewrite interp_state_bind.
    rewrite interp_state_send.
    cbn.
    rewrite eq.
    rewrite !tau_eutt.
    rewrite bind_ret; cbn.
    rewrite interp_state_ret.
    reflexivity.
  Qed.

End Eq_Locals.

(* ================================================================= *)
(** ** Linking *)

(** We first show that our "high level" [asm] combinators are correct.
    These proofs are mostly independent from the compiler, and therefore
    fairly reusable.
    Once again, these notion of correctness are expressed as equations
    commuting the denotation with the combinator.
 *)

Section Linking.

  Context {E': Type -> Type}.
  Context {HasMemory: Memory -< E'}.
  Context {HasExit: Exit -< E'}.
  Notation E := (Locals +' E').

  (** [seq_asm] is denoted as the (horizontal) composition of denotations. *)
  Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
      denote_asm (seq_asm ab bc)
    ⩯ denote_asm ab >>> denote_asm bc.
  Proof.
    unfold seq_asm. 
    rewrite link_asm_correct, relabel_asm_correct, app_asm_correct.
    rewrite <- lift_ktree_id, cat_assoc.
    rewrite cat_id_r.
    rewrite sym_ktree_unfold.
    apply cat_from_loop.
    all: typeclasses eauto.
  Qed.

  (** [if_asm] is denoted as the ktree first denoting the branching condition,
      then looking-up the appropriate variable and following with either denotation. *)
  Lemma if_asm_correct {A} (e : list instr) (tp fp : asm unit A) :
      denote_asm (if_asm e tp fp)
    ⩯ ((fun _ =>
         denote_list e ;;
         v <- send (GetVar tmp_if) ;;
         if v : value then denote_asm fp tt else denote_asm tp tt) : ktree _ _ _).
  Proof.
    unfold if_asm.
    rewrite seq_asm_correct.
    unfold cond_asm.
    rewrite raw_asm_block_correct_lifted.
    intros [].
    unfold CategoryOps.cat, Cat_ktree, ITree.cat; simpl.
    rewrite after_correct.
    simpl.
    repeat setoid_rewrite bind_bind.
    apply eutt_bind; try reflexivity. intros [].
    apply eutt_bind; try reflexivity. intros [].
    - rewrite bind_ret_.
      rewrite (relabel_asm_correct _ _ _ (inr tt)).
      unfold CategoryOps.cat, Cat_ktree, ITree.cat; simpl.
      rewrite bind_bind.
      unfold lift_ktree; rewrite bind_ret_.
      setoid_rewrite (app_asm_correct tp fp (inr tt)).
      setoid_rewrite bind_bind.
      rewrite <- (bind_ret2 (denote_asm fp tt)) at 2.
      eapply eutt_bind; try reflexivity. intros ?.
      unfold inr_, Inr_ktree, lift_ktree; rewrite bind_ret_; reflexivity.
    - rewrite bind_ret_.
      rewrite (relabel_asm_correct _ _ _ (inl tt)).
      unfold CategoryOps.cat, Cat_ktree, ITree.cat; simpl.
      rewrite bind_bind.
      unfold lift_ktree; rewrite bind_ret_.
      setoid_rewrite (app_asm_correct tp fp (inl tt)).
      setoid_rewrite bind_bind.
      rewrite <- (bind_ret2 (denote_asm tp tt)) at 2.
      eapply eutt_bind; try reflexivity. intros ?.
      unfold inl_, Inl_ktree, lift_ktree;
        rewrite bind_ret_; reflexivity.
  Qed.

  (** [while_asm] is denoted as the loop of the body with two entry point, the exit
      of the loop, and the body in which we have the same structure as for the conditional *)
   Lemma while_asm_correct (e : list instr) (p : asm unit unit) :
      denote_asm (while_asm e p)
    ⩯ loop (fun l : unit + unit =>
         match l with
         | inl tt =>
           denote_list e ;;
           v <- ITree.send (inl1 (GetVar tmp_if)) ;;
           if v : value then
             Ret (inr tt)
           else
             (denote_asm p tt;; Ret (inl tt))
         | inr tt => Ret (inl tt)
         end).
  Proof.
    unfold while_asm.
    rewrite link_asm_correct.
    apply eq_ktree_loop.
    rewrite relabel_asm_correct.
    rewrite <- lift_ktree_id, cat_id_l.
    rewrite app_asm_correct.
    rewrite if_asm_correct.
    all: try typeclasses eauto.
    intros [[] | []].
    - unfold ITree.cat. 
      simpl; setoid_rewrite bind_bind.
      rewrite bind_bind.
      apply eutt_bind; try reflexivity. intros [].
      rewrite bind_bind.
      apply eutt_bind; try reflexivity. intros [].
      + rewrite (pure_asm_correct _ tt).
        unfold inl_, Inl_ktree, lift_ktree.
        repeat rewrite bind_ret_.
        reflexivity.
      + rewrite (relabel_asm_correct _ _ _  tt).
        unfold CategoryOps.cat, Cat_ktree, ITree.cat.
        simpl; repeat setoid_rewrite bind_bind.
        unfold inl_, Inl_ktree, lift_ktree; rewrite bind_ret_.
        apply eutt_bind; try reflexivity. intros [].
        repeat rewrite bind_ret_; reflexivity.
    - rewrite itree_eta; cbn; reflexivity.
  Qed.

End Linking.

(* ================================================================= *)
(** ** Correctness *)

Section Correctness.

  Context {E': Type -> Type}.
  Context {HasMemory: Memory -< E'}.
  Context {HasExit: Exit -< E'}.
  Notation E := (Locals +' E').

  (** We use a couple of tactics to step through itrees by eta expansion followed by reduction *)
  Ltac force_left :=
    match goal with
    | |- eutt _ ?x _ => rewrite (itree_eta x); cbn
    end.

  Ltac force_right :=
    match goal with
    | |- eutt _ _ ?x => rewrite (itree_eta x); cbn
    end.

  (** Chain a reduction expected to exhibit a [Tau] step with its elimination *)
  Ltac untau_left := force_left; rewrite tau_eutt.
  Ltac untau_right := force_right; rewrite tau_eutt.

  (** Fully reduce both sides *)
  Ltac tau_steps :=
    repeat (untau_left); force_left;
    repeat (untau_right); force_right.

  (** Correctness of expressions.
      We strengthen [eq_locals]: initial environments are still related by [Renv],
      but intermediate ones must now satisfy [sim_rel].
      Note that by doing so, we use a _heterogeneous bisimulation_: the trees
      return values of different types ([alist var value * unit] for _Asm_,
      [alist var value * value] for _Imp_). The differeence is nonetheless mostly
      transparent for the user, except for the use of the more generale [eutt_bind_gen].
   *)
  
  Lemma compile_expr_correct : forall e g_imp g_asm n,
      Renv g_asm g_imp ->
      eutt (sim_rel g_asm n)
           (interp_locals (denote_list (compile_expr n e)) g_asm)
           (interp_locals (denoteExpr e) g_imp).
  Proof.
    induction e; simpl; intros.
    - (* Var case *)
      (* We first compute and eliminate taus on both sides. *)
      tau_steps.

      (* We are left with [Ret] constructs on both sides, that remains to be related *)
      apply eutt_ret.
      (* On the _Asm_ side, we bind to [gen_tmp n] a lookup to [varOf v] *)
      (* On the _Imp_ side, we return the value of a lookup to [varOf v] *)
      erewrite <- Renv_find; [| eassumption].
      apply sim_rel_add; assumption.

    - (* Literal case *)
      (* We reduce both sides to Ret constructs *)
      tau_steps.

      apply eutt_ret.
      (* _Asm_ bind the litteral to [gen_tmp n] while _Imp_ returns it *)
      apply sim_rel_add; assumption.

    (* The three binary operator cases are identical *)
    - (* Plus case *)
      (* We push [interp_locals] into the denotations *)
      do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_bind_gen.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [g_asm' []] [g_imp' v] HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      eapply eutt_bind_gen.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [g_asm'' []] [g_imp'' v'] HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps.
      simpl fst in *.
      apply eutt_ret.

      clear -HSIM HSIM'.
      erewrite sim_rel_find_tmp_n_trans; eauto. 
      erewrite sim_rel_find_tmp_n; eauto. 
      eapply sim_rel_binary_op; eauto.

    - (* Sub case *)
      (* We push [interp_locals] into the denotations *)
      do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_bind_gen.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [g_asm' []] [g_imp' v] HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      eapply eutt_bind_gen.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [g_asm'' []] [g_imp'' v'] HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps. 
      simpl fst in *.
      apply eutt_ret.

      clear -HSIM HSIM'.
      erewrite sim_rel_find_tmp_n_trans; eauto. 
      erewrite sim_rel_find_tmp_n; eauto. 
      eapply sim_rel_binary_op; eauto.

    - (* Mul case *)
      (* We push [interp_locals] into the denotations *)
      do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_bind_gen.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [g_asm' []] [g_imp' v] HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      eapply eutt_bind_gen.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [g_asm'' []] [g_imp'' v'] HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps.
      simpl fst in *.
      apply eutt_ret.

      clear -HSIM HSIM'.
      erewrite sim_rel_find_tmp_n_trans; eauto. 
      erewrite sim_rel_find_tmp_n; eauto. 
      eapply sim_rel_binary_op; eauto.
  Qed.

  (** Correctness of the assign statement.
      The resulting list of instruction is denoted as
      denoting the expression followed by setting the variable.
   *)
  Lemma compile_assign_correct : forall e x,
      eq_locals eq Renv
                (denote_list (compile_assign x e))
                (v <- denoteExpr e ;; send (SetVar x v)).
  Proof.
    red; intros.
    unfold compile_assign.
    (* We push interp_locals inside of the denotations *)
    rewrite denote_list_app.
    do 2 rewrite interp_locals_bind.

    (* By correctness of the compilation of expressions,
       we can match the head trees.
     *)
    eapply eutt_bind_gen.
    { eapply compile_expr_correct; eauto. }

    (* Once again, we get related environments *)
    intros [g_asm' []] [g_imp' v] HSIM.
    (* We can now reduce to Ret constructs *)
    tau_steps. 
    eapply eutt_ret; simpl.

    (* And remains to relate the results *)
    erewrite sim_rel_find_tmp_n; eauto; simpl.
    apply sim_rel_Renv in HSIM.
    split; auto.
    eapply Renv_write_local; eauto.
  Qed.

  (* Utility: slight rephrasing of [while] to facilitate rewriting
     in the main theorem.*)
  Lemma while_is_loop {E} (body : itree E bool) :
    while body
          ≈ loop (fun l : unit + unit =>
                    match l with
                    | inl _ => ITree.map (fun b => if b : bool then inl tt else inr tt) body
                    | inr _ => Ret (inl tt)   (* Enter loop *)
                    end) tt.
  Proof.
    unfold while.
    apply eutt_loop; [| reflexivity].
    intros [[]|[]]; simpl; [| reflexivity].
    unfold ITree.map.
    apply eutt_bind; try reflexivity.
    intros []; reflexivity.
  Qed.

  (** Correctness of the compiler.
      After interpretation of the [Locals], the source _Imp_ statement
      denoted as an [itree] and the compiled _Asm_ program denoted
      as an [itree] are equivalent up-to-taus.
      The correctness is termination sensitive, but nonetheless a simple
      induction on statements.
      We only are left with reasoning about the functional correctness of
      the compiler, all control-flow related reasoning having been handled
      in isolation.
   *)
  Theorem compile_correct (s : stmt) :
    eq_locals eq Renv
              (denote_asm (compile s) tt)
              (denoteStmt s).
  Proof.
    induction s.

    - (* Assign *)
      simpl.
      (* We push [denote_asm] inside of the combinators *)
      rewrite raw_asm_block_correct.
      rewrite after_correct.

      (* The head trees match by correctness of assign *)
      rewrite <- (bind_ret2 (ITree.bind (denoteExpr e) _)).
      eapply eq_locals_bind_gen.
      { eapply compile_assign_correct; auto. }

      (* And remains to trivially relate the results *)
      intros [] [] []; simpl.
      repeat intro.
      force_left; force_right.
      apply eutt_ret; auto.

    - (* Seq *)
      (* We commute [denote_asm] with [seq_asm] *)
      rewrite fold_to_itree; simpl.
      rewrite seq_asm_correct. unfold to_itree.

      (* And the result is immediate by indcution hypothesis *)
      eapply eq_locals_bind_gen.
      { eauto. }
      intros [] [] []; auto.

    - (* If *)
      (* We commute [denote_asm] with [if_asm] *)
      rewrite fold_to_itree. simpl.
      rewrite if_asm_correct.
      unfold to_itree.

      (* We now need to line up the evaluation of the test,
         and eliminate them by correctness of [compile_expr] *)
      repeat intro.
      rewrite 2 interp_locals_bind.
      eapply eutt_bind_gen.
      { apply compile_expr_correct; auto. }

      (* We get in return [sim_rel] related environments *)
      intros [g_asm []] [g_imp v] HSIM.
      rewrite interp_locals_bind.
      (* We know that interpreting [GetVar tmp_if] is eutt to [Ret (g_asm,v)] *)
      generalize HSIM; intros EQ; eapply sim_rel_get_tmp0 in EQ.
      setoid_rewrite EQ; clear EQ.
      rewrite bind_ret_; simpl.
      (* We can weaken [sim_rel] down to [Renv] *)
      apply sim_rel_Renv in HSIM.
      (* And finally conclude in both cases *)
      destruct v; simpl; auto. 

    - (* While *)
      (* We commute [denote_asm] with [while_asm], and restructure the
         _Imp_ [loop] with [while_is_loop] *)
      simpl; rewrite fold_to_itree.
      rewrite while_asm_correct.
      rewrite while_is_loop.
      unfold to_itree.

      (* We now have loops on both side, so we can just reason about their bodies *)
      apply eq_locals_loop.
      (* The two cases correspond to entering the loop, or exiting it*)
      intros [[]|[]].

      (* The exiting case is trivial *)
      2:{ repeat intro.
          force_left. force_right.
          apply eutt_ret; auto. }

      (* We now need to line up the evaluation of the test,
         and eliminate them by correctness of [compile_expr] *)
      unfold ITree.map. rewrite bind_bind.
      repeat intro.
      rewrite 2 interp_locals_bind.
      eapply eutt_bind_gen.
      { apply compile_expr_correct; auto. }

      (* We get in return [sim_rel] related environments *)
      intros [g_asm []] [g_imp v] HSIM.
      rewrite 2 interp_locals_bind.
      (* We know that interpreting [GetVar tmp_if] is eutt to [Ret (g_asm,v)] *)
      generalize HSIM; intros EQ. eapply sim_rel_get_tmp0 in EQ.
      setoid_rewrite EQ; clear EQ.
      rewrite bind_ret_; simpl.

      (* We can weaken [sim_rel] down to [Renv] *)
      apply sim_rel_Renv in HSIM.
      (* And now consider both cases *)
      destruct v; simpl; auto.
      + (* The false case is trivial *)
        force_left; force_right.
        apply eutt_ret; auto.
      + (* In the true case, we line up the body of the loop to use the induction hypothesis *)
        rewrite 2 interp_locals_bind, bind_bind.
        eapply eutt_bind_gen.
        { eapply IHs; auto. }
        intros [g_asm' []] [g_imp' v'] [HSIM' ?].
        intros.
        force_right; force_left.
        apply eutt_ret; simpl; split; auto. 

    - (* Skip *)
      repeat intro.
      force_right; force_left.
      apply eutt_ret; auto.
  Qed.

End Correctness.

(* ================================================================= *)
(** ** Closing word. *)

(** Through this medium-sized exemple, we have seen how to use [itree]s to
    denote two languages, how to run them and how to prove correct a compiler
    between them both.
    We have emphasized that the theory of [ktree]s allowed us to decouple
    all reasoning about the control-flow from the proof of the compiler itself.
    The resulting proof is entirely structurally inductive and equational. In
    particular, we obtain a final theorem relating potentially infinite computations
    without having to write any cofixpoint. 
    
    If this result is encouraging, one might always wonder how things scale.

    A first good sanity check is to extend the languages with a _Print_ instruction.
    It requires to add a new effect to the language and therefore makes the correctness
    theorem relate trees actually still containing events.
    This change, which a good exercise to try, turns out to be as straightforward as one
    would hope. The only new lemma needed is to show that [interp_locals] leaves the
    new [Print] effect untouched.
    This extension can be found in the _tutorial-print_ branch.

    More importantly, our compiler is fairly stupid and inefficient: it creates blocks
    for each compiled statement! One would hope to easily write and prove an optimization
    coalescing elementary blocks together.
    This however raises for now a difficulty: our representation of labels as binary trees
    encoded in [Type] is so unstructured that introspection on [asm] programs is difficult.
    We might therefore need to change our representation of labels, for instance to a [Fin] type.
    But this change turns out to be more interesting that it might seem: it moves [bks]
    from [fun (A B: Type) => A -> block B] to [fun (A B: nat) => Fin.t A -> block (Fin.t B)].
    Correspondingly, their denotation moves from [fun (A B: Type) => bks A B -> ktree E A B]
    to [fun (A B: nat) => ktree E (Fin.t A) (Fin.t B)].
    But our proof crucially rested on the categorie [(Type, ktree E)] being provided by
    the [itree] library with a traced monoidal structure. We would therefore here need
    to redo all the work to equip the category [(Nat, fun A B => ktree E (t A) (t B))] with
    the same strucutre, which is significant low level work.
    We might therefore want to investigate whether [ktree] should be generalized to 
    something along the lines of
    [ktree (i : Type) (F : i -> Type) (E : Type -> Type) (a b : i) : Type := F a -> itree E (F b).]
 *)

