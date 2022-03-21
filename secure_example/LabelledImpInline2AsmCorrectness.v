(** * Functional correctness of the compiler *)

(** We finally turn to proving our compiler correct.

SAZ: This needs to be updated.

    We express the result as a (weak) bisimulation between
    the [itree] resulting from the denotation of the source
    _Imp_ statement and the denotation of the compiled _Asm_
    program. This weak bisimulation is a _up-to-tau_ bisimulation.
    More specifically, we relate the itrees after having
    interpreted the events contained in the trees, and run
    the resulting computation from the state monad:
    [ImpState] on the _Imp_ side, [Reg] and [Memory] on the
    _Asm_ side.

    The proof is essentially structured as followed:
    - a simulation relation is defined to relate the _Imp_
    state to the _Asm_ memory during the simulation. This
    relation is strengthened into a second one additionally
    relating the result of the denotation of an expression to
    the _Asm_ set of registers, and used during the simulation
    of expressions.
    - the desired bisimulation is defined to carry out the
    the simulation invariant into a up-to-tau equivalence after
    interpretation of events. Once again a slightly different
    bisimulation is defined when handling expressions.
    - Linking is proved in isolation: the "high level" control
    flow combinators for _Asm_ defined in [Imp2Asm.v] are
    proved correct in the same style as the elementary ones
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
    - We transparently make use of the heterogeneous bisimulation provided
    by the [itree] library to relate computations of _Asm_ expressions that
    return a pair of environments (registers and memory) and a [unit] value to
    ones of _Imp_ that return a single environment and an [Imp.value].
 *)

(* begin hide *)

From Coq Require Import
     Arith
     String
     Morphisms
     Lia.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.CategorySub
     Basics.HeterogeneousRelations
     Events.StateFacts
     Events.MapDefault
     Events.Exception
     Events.ExceptionFacts
.

From SecureExample Require Import
     LabelledImpInline
     LabelledAsm
     LabelledAsmCombinators
     Utils_tutorial
     LabelledImpInline2Asm
     Fin
     KTreeFin
     LabelledImpHandler
.

Import ITreeNotations.

From ExtLib Require Import
     Structures.Monad
     Structures.Maps
     Data.Map.FMapAList.

Import CatNotations.
Local Open Scope cat.

Import Monads.
Open Scope monad_scope.
Open Scope itree_scope.

(* end hide *)

(* ================================================================= *)
(** ** Simulation relations and invariants *)

(** The compiler is proved correct by constructing a (itree) bisimulation
    between the source program and its compilation.  The compiler does two
    things that affect the state:

      - it translates source Imp variables to Asm global variables, which should
        match at each step of computation

      - it introduces temporary local variables that name intermediate values

    As is traditional, we define, to this end, a simulation relation [Renv] and
    invariants that relate the source Imp environment to the target Asm
    environment, following the description above.

    [Renv] relates two [alist var value] environments if they act as
    equivalent maps.  This is used to relate Imp's [ImpState] environment to
    Asm's [Memory].

*)
Notation update := LabelledImp.update.
Notation impExcE := LabelledImp.impExcE.
Notation IOE := LabelledImp.IOE.
Section Simulation_Relation.

  (*here is where differences start, because now imp programs have the same denotation,
    I think sim_rel just becomes Renv? mapped to the second argument? *)

  (** ** Definition of the simulation relations *)

  (** The simulation relation for evaluation of statements.
      The relation relates two environments of type [alist var value].
      The source and target environments exactly agree on user variables.
   *)
  Definition Renv (g_imp : map) (g_asm : memory) : Prop :=
    forall x, g_imp x = g_asm x.

  Global Instance Renv_refl : Reflexive Renv.
  Proof.
    red. intros. unfold Renv. auto.
  Qed.

 (** The simulation relation for evaluation of expressions.

     The relation connects

       - the global state at the Imp level

       - the memory and register states at the Asm level

     and, additionally the returned value at the _Imp_ level. The _Asm_ side
     does not carry a [value], but a [unit], since its denotation does not
     return any [value].

     The [sim_rel] relation is parameterized by the state of the local [asm]
     environment before the step, and the name of the variable used to store the
     result.


     It enforces three conditions:
     - [Renv] on the global environments, ensuring that evaluation of expressions does
     not change user variables;

     - Agreement on the computed value, i.e. the returned value [v] is stored at
     the assembly level in the expected temporary;

     - The "stack" of temporaries used to compute intermediate results is left
       untouched.
  *)
  (*need to edit this *)
  Definition sim_rel l_asm n: (registers * map * value) -> (registers * memory * unit) -> Prop :=
    fun '(_, g_imp', v) '(l_asm',g_asm', _)  =>
      Renv g_imp' g_asm' /\            (* we don't corrupt any of the imp variables *)
      l_asm' n = v /\          (* we get the right value *)
      (forall m, m < n -> forall v,              (* we don't mess with anything on the "stack" *)
            l_asm m = v <-> l_asm' m = v).

  Lemma sim_rel_find : forall g_asm g_imp l_imp l_asm l_asm' n  v,
    sim_rel l_asm n (l_imp, g_imp, v) (l_asm', g_asm, tt) ->
    l_asm' n = v.
  Proof.
    intros. red in H. tauto.
  Qed.

  (** ** Facts on the simulation relations *)

  (** [Renv] entails agreement of lookup of user variables. *)
  Lemma Renv_find:
    forall g_asm g_imp x,
      Renv g_imp g_asm ->
      g_imp x = g_asm x.
  Proof.
    intros. auto.
  Qed.

  (** [sim_rel] can be initialized from [Renv]. *)
  Lemma sim_rel_add: forall g_asm l_asm g_imp l_imp n v,
      Renv g_imp g_asm ->
      sim_rel l_asm n  (l_imp, g_imp, v) ((update_reg n v l_asm, g_asm, tt)).
  Proof.
    intros. red. split; auto. split; auto.
    - unfold update_reg. rewrite Nat.eqb_refl. auto.
    - intros. assert (n <> m). lia.
      unfold update_reg. apply Nat.eqb_neq in H1. rewrite H1. split; auto.
  Qed.

  (** [Renv] can be recovered from [sim_rel]. *)
  Lemma sim_rel_Renv: forall l_asm n s1 l1 l2 v1 s2 v2,
      sim_rel l_asm n (l2, s2,v2) (l1,s1,v1) -> Renv s2 s1 .
  Proof.
    intros ? ? ? ? ? ? ? ? H; apply H.
  Qed.

  Lemma sim_rel_find_tmp_n:
    forall l_asm g_asm' n l_imp l_asm' g_imp' v,
      sim_rel l_asm n  (l_imp, g_imp',v) (l_asm', g_asm', tt) ->
      l_asm' n = v.
  Proof.
    intros ? ? ? ? ? ? ? [_ [H _]]; exact H.
  Qed.

  (** [sim_rel] entails agreement of lookups in the "stack" between its argument
      and the current Asm environement *)
  Lemma sim_rel_find_tmp_lt_n:
    forall l_asm g_asm' n m l_asm' l_imp' g_imp' v,
      m < n ->
      sim_rel l_asm n (l_imp', g_imp',v) (l_asm', g_asm', tt) ->
      l_asm m = l_asm' m.
  Proof.
    intros ? ? ? ? ? ? ? ? ineq [_ [_ H]].
    match goal with
    | |- _ = ?x => destruct x eqn:EQ
    end.
    setoid_rewrite (H _ ineq); auto.
    apply H; auto.
  Qed.

  Lemma sim_rel_find_tmp_n_trans:
    forall l_asm n l_asm' l_asm'' g_asm' g_asm'' l_imp' g_imp' l_imp'' g_imp'' v v',
      sim_rel l_asm n (l_imp', g_imp',v) (l_asm', g_asm', tt)  ->
      sim_rel l_asm' (S n) (l_imp'', g_imp'',v') (l_asm'', g_asm'', tt)  ->
      l_asm'' n = v.
  Proof.
    intros.
    generalize H; intros LU; apply sim_rel_find_tmp_n in LU.
    unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto.
  Qed.

  (** [Renv] is preserved by assignment.
   *)

  Lemma Renv_write_local:
    forall (k : var) (g_asm g_imp : map) v,
      Renv g_imp g_asm ->
      Renv (update k v g_imp) (update k v g_asm).
  Proof.
    unfold Renv. intros. unfold update.
    destruct (k =? x)%string; auto.
  Qed.

  (** [sim_rel] can be composed when proving binary arithmetic operators. *)
  Lemma sim_rel_binary_op:
    forall (l_asm l_asm' l_asm'' l_imp' l_imp'': registers) (g_asm' g_asm'' : memory) (g_imp' g_imp'' : map)
      (n v v' : nat)
      (Hsim : sim_rel l_asm n (l_imp', g_imp', v) (l_asm', g_asm', tt))
      (Hsim': sim_rel l_asm' (S n) (l_imp'', g_imp'', v') (l_asm'', g_asm'', tt))
      (op: nat -> nat -> nat),
      sim_rel l_asm n (l_imp'', g_imp'', op v v') (update_reg n (op v v') l_asm'', g_asm'', tt).
  Proof.
    intros.
    split; [| split].
    - eapply sim_rel_Renv; eassumption.
    - unfold update_reg. rewrite Nat.eqb_refl; auto.
    - intros m LT v''. assert (n <> m). lia.
      destruct Hsim as [_ [_ Hsim]].
      destruct Hsim' as [_ [_ Hsim']].
      rewrite Hsim; [| auto with arith].
      rewrite Hsim'; [| auto with arith].
      unfold update_reg. apply Nat.eqb_neq in H. rewrite H. reflexivity.
  Qed.

End Simulation_Relation.

(* ================================================================= *)
(** ** Bisimulation *)

(** We now make precise the bisimulation established to show the correctness of
    the compiler.  Naturally, we cannot establish a _strong bisimulation_
    between the source program and the target program: the [asm] counterpart
    performs "more steps" when evaluating expressions.  The appropriate notion
    is of course the _equivalence up to tau_. However, the [itree] structures
    are also quite different.  [asm] programs manipulate two state
    components. The simulation will establish that the [imp] global state
    corresponds to the [asm] memory, but to be able to  establish this
    correspondence, we also need to interpret the [asm] register effects.  *)

(*
Goal forall E1 E2 R, @interp_imp_inline E1 E2 R = interp_asm.
  auto.
Qed.
*)
Section Bisimulation.


  (** Definition of our bisimulation relation.

      As previously explained, the bisimulation relates (up-to-tau)
      two [itree]s after having interpreted their events.

      We additionally bake into it a simulation invariant:
      - Events are interpreted from states related by [Renv]
      - Returned values must contain related states, as well as computed datas
        related by another relation [RAB] taken in parameter.
      In our case, we will specialize [RAB] to the total relation since the trees return
      respectively [unit] and the unique top-level label [F0: fin 1].
   *)

  Section RAB.

    Context {A B : Type}.
    Context (RAB : A -> B -> Prop).  (* relation on Imp / Asm values *)

    Definition state_invariant (a : registers * memory * A) (b : registers * memory * B)  :=
      Renv (snd (fst a)) (snd (fst b)) /\ (RAB (snd a) (snd  b)).

    Definition bisimilar  (t1 : itree ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) A) (t2 : itree ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) B)  :=
    forall g_asm g_imp l1 l2,
      Renv g_imp g_asm ->
      eutt state_invariant
           (interp_imp_inline t1 (l1, g_imp))
           (interp_asm t2 (l2, g_asm) ).
  End RAB.


  (** [bisimilar] is compatible with [eutt]. *)

  Global Instance eutt_bisimilar  {A B}  (RAB : A -> B -> Prop):
    Proper (eutt eq ==> eutt eq ==> iff) (@bisimilar A B RAB).
  Proof.
    repeat intro.
    unfold bisimilar. split.
    - intros. unfold interp_imp_inline, interp_asm. rewrite <- H, <-H0.
      apply H1; auto.
    - intros. unfold interp_imp_inline, interp_asm.
      rewrite H, H0. apply H1; auto.
  Qed.

  Lemma bisimilar_bind' {A A' B C} (RAA' : A -> A' -> Prop) (RBC: B -> C -> Prop):
    forall (t1 : itree _ A) (t2 : itree _ A') ,
      bisimilar RAA' t1 t2 ->
      forall (k1 : A -> itree _ B) (k2 : A' -> itree _ C)
        (H: forall (a:A) (a':A'), RAA' a a' -> bisimilar RBC (k1 a) (k2 a')),
        bisimilar RBC (t1 >>= k1) (t2 >>= k2).
  Proof.
    repeat intro. unfold interp_imp_inline, interp_asm.
    repeat rewrite interp_state_bind.
    eapply eutt_clo_bind.
    { eapply H; auto. }
    intros [[regs1 mem1] a] [ [regs2 mem2] a'].
    intros Hs. destruct Hs.
    cbn in *. eapply H0; eauto.
  Qed.

  Lemma bisimilar_iter {A A' B B'}
        (R : A -> A' -> Prop)
        (S : B -> B' -> Prop)
        (t1 : A -> itree (_) (A + B))
        (t2 : A' -> itree (_) (A' + B')) :
    (forall l l', R l l' -> bisimilar (sum_rel R S) (t1 l) (t2 l')) ->
    forall x x', R x x' ->
    bisimilar S (iter (C := ktree _) t1 x) (iter (C := ktree _) t2 x').
  Proof.

    unfold bisimilar, interp_imp_inline, interp_asm, interp_imp.
    intros.
    pose proof @interp_state_iter'. unfold state_eq in H2.
    repeat setoid_rewrite H2.
    eapply (eutt_iter' (state_invariant R)); intros.
    2 : { split; auto. }
    destruct H3. destruct j1 as [ [regs1 mem1] a].
    destruct j2 as [ [regs2 mem2] a']. cbn in *.
    eapply eutt_clo_bind; eauto. intros [ [regs3 mem3] r1] [ [regs4 mem4 ] r2 ] Hs.
    red in Hs. cbn in *. destruct Hs as [Hs Hr].
    inv Hr;
    apply eqit_Ret; constructor; split; auto.
  Qed.

  (** [sim_rel] at [n] entails that [GetVar (gen_tmp n)] gets interpreted
      as returning the same value as the _Imp_ related one.
   *)
  Lemma sim_rel_get_tmp0:
    forall n l l' g_asm l_imp g_imp v,
      sim_rel l' n (l_imp, g_imp,v) (l, g_asm,tt) ->
      (interp_asm ((trigger (GetReg n)) : itree ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) value)
                                       (l, g_asm))
      ≈     (Ret (l, g_asm, v)).
  Proof.
    intros.
    unfold interp_asm.
    rewrite interp_state_trigger.
    cbn. apply eqit_Ret.
    destruct H. destruct H0. cbv. rewrite H0. auto.
  Qed.


End Bisimulation.

(* ================================================================= *)
(** ** Linking *)

(** We first show that our "high level" [asm] combinators are correct.  These
    proofs are mostly independent from the compiler, and therefore fairly
    reusable.  Once again, these notion of correctness are expressed as
    equations commuting the denotation with the combinator.  *)

Section Linking.

  Import KTreeFin.

  (** [seq_asm] is denoted as the (horizontal) composition of denotations. *)
  Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
      denote_asm (seq_asm ab bc)
    ⩯ denote_asm ab >>> denote_asm bc.
  Proof.
    unfold seq_asm.
    rewrite loop_asm_correct, relabel_asm_correct, app_asm_correct.

    rewrite fmap_id0, cat_id_r, fmap_swap.
    apply cat_from_loop.
  Qed.
(*
  Check fun (E : Type -> Type) Case (ktree_fin ) *)

  Definition reassoc_seq_asm_exc {B C D : nat} : fin ((B + C) + (D + C) ) -> fin (B + (D + C) ) :=
    ((assoc_r >>> bimap (id_ B) (bimap (id_ C) swap >>> assoc_l >>>
                                                          bimap merge (id_ D) >>> swap))).
(* we can compute this functions behavior on each of all parts of its element space with like 4 equations *)

  Lemma reassoc_seq_asm_exc_B (B C D : nat) (b : fin B) (bc : fin (B + C) ) :
     split_fin_sum B C  bc = inl b -> reassoc_seq_asm_exc (L (D + C) bc) = L (D + C) b.
  Proof.
    intros. unfold reassoc_seq_asm_exc. cbn.
    unfold cat, Cat_sub, cat, Cat_Fun.
    unfold assoc_r, AssocR_Coproduct, case_, Case_sub, case_, Case_Kleisli, case_sum.
    cbn. unfold to_bif, ToBifunctor_Fun_fin. unfold swap, Swap_Coproduct, case_.
    unfold bimap, Bimap_Coproduct, case_, cat. cbn. rewrite split_fin_sum_L. rewrite H.
    repeat rewrite split_fin_sum_L. auto.
  Qed.

  Lemma reassoc_seq_asm_exc_C_ab (B C D : nat ) (c : fin C) (bc : fin (B + C) ) :
    split_fin_sum B C bc = inr c -> @reassoc_seq_asm_exc B C D (L _ bc ) = R _ (R _ c).
  Proof.
    intros. unfold reassoc_seq_asm_exc. cbn.
    unfold cat, Cat_sub, cat, Cat_Fun.
    unfold assoc_r, AssocR_Coproduct, case_, Case_sub, case_, Case_Kleisli, case_sum.
    cbn. unfold to_bif, ToBifunctor_Fun_fin. unfold swap, Swap_Coproduct, case_.
    unfold bimap, Bimap_Coproduct, case_, cat. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. rewrite H. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn.
    unfold assoc_l, AssocL_Coproduct. cbn. unfold case_.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn.
    unfold merge, case_. repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn.
    auto.
  Qed.

  Lemma reassoc_seq_asm_exc_D (B C D : nat ) (d : fin D) (dc : fin (D + C) ) :
    split_fin_sum D C dc = inl d -> @reassoc_seq_asm_exc B C D (R _ dc ) = R _ (L _ d).
  Proof.
    intros. unfold reassoc_seq_asm_exc. cbn.
    unfold cat, Cat_sub, cat, Cat_Fun.
    unfold assoc_r, AssocR_Coproduct, case_, Case_sub, case_, Case_Kleisli, case_sum.
    cbn. unfold to_bif, ToBifunctor_Fun_fin. unfold swap, Swap_Coproduct, case_.
    unfold bimap, Bimap_Coproduct, case_, cat. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn. rewrite H.
    unfold assoc_l, AssocL_Coproduct. cbn. unfold case_. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn. auto.
  Qed.

  Lemma reassoc_seq_asm_exc_C_bd (B C D : nat ) (c : fin C) (dc : fin (D + C) ) :
    split_fin_sum D C dc = inr c -> @reassoc_seq_asm_exc B C D (R _ dc ) = R _ (R _ c).
  Proof.
    intros. unfold reassoc_seq_asm_exc. cbn.
    unfold cat, Cat_sub, cat, Cat_Fun.
    unfold assoc_r, AssocR_Coproduct, case_, Case_sub, case_, Case_Kleisli, case_sum.
    cbn. unfold to_bif, ToBifunctor_Fun_fin. unfold swap, Swap_Coproduct, case_.
    unfold bimap, Bimap_Coproduct, case_, cat. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn. rewrite H.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R. cbn.
    unfold assoc_l, AssocL_Coproduct. cbn. unfold case_. cbn.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R.
    repeat rewrite split_fin_sum_L. repeat rewrite split_fin_sum_R.
    unfold merge. unfold case_. rewrite split_fin_sum_R. auto.
  Qed.

  Lemma seq_asm_exc_correct {A B C D} (ab : asm A (B + C)) (bd : asm B (D + C)) :
     denote_asm (seq_asm_exc ab bd)
   ⩯ denote_asm ab  >>> case_ (denote_asm bd) inr_.
  Proof.
    unfold seq_asm_exc, expose_linking_labels, swap_and_merge, comb.
    rewrite loop_asm_correct, relabel_asm_correct, app_asm_correct. rewrite cat_id_r.
    repeat rewrite fmap_swap.
    match goal with |- loop ?b ⩯ _ =>  set b as body end.
    assert (forall a : fin A, body (merge_fin_sum _ _ (inr a)) ≈
                              r <- denote_asm ab a;;
                         Ret
                           (reassoc_seq_asm_exc (L _ r) )).

    {
      intros. match goal with |- _ ≈ ?t => remember t as t' end.
      unfold body. cbn. repeat setoid_rewrite bind_ret_l.
      rewrite bind_bind. rewrite split_fin_sum_R. cbn.
      repeat rewrite bind_ret_l. Local Opaque denote_asm. unfold from_bif, FromBifunctor_ktree_fin.
      rewrite bind_ret_l. rewrite split_merge. cbn.
      setoid_rewrite bind_ret_l. rewrite bind_bind.
      unfold from_bif, FromBifunctor_ktree_fin. setoid_rewrite bind_ret_l.
      cbn. unfold unsubm. subst. unfold reassoc_seq_asm_exc. reflexivity.
    } (* this unfolding basically shows that you only need to unfold the top level loop twice*)
    assert (forall b : fin B, body (merge_fin_sum _ _ (inl b) ) ≈
                              r <- denote_asm bd b;;
                         Ret (reassoc_seq_asm_exc (R _ r) )).
    {
      intros. unfold body. cbn. repeat setoid_rewrite bind_ret_l.
      rewrite split_fin_sum_L. cbn. repeat setoid_rewrite bind_ret_l.
      rewrite split_merge. cbn. rewrite bind_bind. setoid_rewrite bind_ret_l.
      unfold from_bif, FromBifunctor_ktree_fin. setoid_rewrite bind_ret_l.
      cbn. unfold unsubm. unfold reassoc_seq_asm_exc. reflexivity.
    }
    assert (body ⩯ case_
                 (denote_asm bd >>> (fun r => Ret (reassoc_seq_asm_exc (R _ r) ) ))
                 (denote_asm ab >>> (fun r => Ret (reassoc_seq_asm_exc (L _ r)) ))).
    { do 5 red. unfold case_, Case_sub. unfold to_bif, ToBifunctor_ktree_fin.
      cbn.
      intros. destruct (split_fin_sum B A a) eqn : Heq.
      - rewrite bind_ret_l. cbn. rewrite <- H0. rewrite <- Heq. rewrite merge_split. reflexivity.
      - rewrite bind_ret_l. cbn. rewrite <- H. rewrite <- Heq. rewrite merge_split. reflexivity.
    }
    rewrite H1.
    do 5 red. intros. Local Opaque denote_asm. unfold loop. cbn.
    rewrite bind_bind. rewrite bind_ret_l. unfold from_bif, FromBifunctor_ktree_fin.
    rewrite bind_ret_l. cbn.
    setoid_rewrite unfold_iter_ktree. cbn. unfold to_bif, ToBifunctor_ktree_fin.
    repeat rewrite split_fin_sum_R. repeat rewrite bind_bind. rewrite bind_ret_l.
    cbn. rewrite bind_bind. eapply eqit_bind'; try reflexivity. intros; subst.
    repeat setoid_rewrite bind_ret_l.
    destruct (split_fin_sum _ _ r2) as [b | c] eqn : Heq.
    - erewrite reassoc_seq_asm_exc_B; eauto. rewrite split_fin_sum_L. cbn.
      repeat setoid_rewrite bind_ret_l. rewrite split_merge. rewrite tau_eutt.
      setoid_rewrite unfold_iter_ktree. cbn. repeat rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l. cbn. rewrite split_fin_sum_L. cbn.
      rewrite bind_bind. setoid_rewrite bind_ret_l. cbn.
      match goal with |- eqit eq true true (ITree.bind _ ?k ) _ => remember k as k_id  end.
      assert (forall r, k_id r ≈ Ret r ).
      {
        subst. intros. destruct (split_fin_sum _ _ r) as [d | c] eqn : Heqr .
        - erewrite  reassoc_seq_asm_exc_D; eauto. rewrite split_fin_sum_R. cbn.
          repeat rewrite bind_ret_l. unfold from_bif, FromBifunctor_ktree_fin.
          cbn. rewrite bind_ret_l. rewrite split_fin_sum_R. cbn.
          unfold id. apply eqit_Ret.
          apply unique_fin.
          unfold split_fin_sum in Heqr.
          destruct (lt_dec (proj1_sig r) D ); try discriminate.
          injection Heqr as Heqr. rewrite <- Heqr. cbn. auto.
        - erewrite reassoc_seq_asm_exc_C_bd; eauto. rewrite split_fin_sum_R.
          cbn. repeat setoid_rewrite bind_ret_l. rewrite split_merge.
          unfold split_fin_sum in Heqr. destruct r. cbn in Heqr.
          destruct (lt_dec x D); try discriminate. injection Heqr as Heqr.
          subst. cbn. apply eqit_Ret. apply unique_fin. cbn.
          lia.
      }
      setoid_rewrite <- bind_ret_r at 3.
      eapply eqit_bind'; try reflexivity. clear Heqk_id. intros; subst.
      rewrite H2. reflexivity.
    - erewrite reassoc_seq_asm_exc_C_ab; eauto. rewrite split_fin_sum_R.
      cbn. repeat setoid_rewrite bind_ret_l. rewrite split_merge.
      cbn. unfold from_bif, FromBifunctor_ktree_fin. cbn. reflexivity.
  Qed.

    (* remaining goals in this lemma could all be solved with proof irrelavance *)

  (** [if_asm] is denoted as the ktree first denoting the branching condition,
      then looking-up the appropriate variable and following with either denotation. *)
  Lemma if_asm_correct {A} (e : list instr) (tp fp : asm 1 A) :
      denote_asm (if_asm e tp fp)
    ⩯ ((fun _ =>
         denote_list e ;;
         v <- trigger (GetReg tmp_if) ;;
         if v : value then denote_asm fp f0 else denote_asm tp f0)).
  Proof.
    unfold if_asm.
    rewrite seq_asm_correct.
    unfold cond_asm.
    rewrite raw_asm_block_correct_lifted.
    rewrite relabel_asm_correct.

    intros ?.
    Local Opaque denote_asm.

    unfold CategoryOps.cat, Cat_sub, CategoryOps.cat, Cat_Kleisli; simpl.
    rewrite denote_after.
    cbn.
    repeat setoid_rewrite bind_bind.
    apply eqit_bind; try reflexivity. intros _.
    apply eqit_bind; try reflexivity. intros [].

    - rewrite !bind_ret_l.
      setoid_rewrite (app_asm_correct tp fp _).
      setoid_rewrite bind_bind.
      match goal with
      | [ |- _ (?t >>= _) _ ] => let y := eval compute in t in change t with y
      end.
      rewrite bind_ret_l. cbn.
      setoid_rewrite bind_ret_l.
      rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      unfold from_bif, FromBifunctor_ktree_fin; cbn.
      rewrite bind_ret_r'.
      { rewrite (unique_f0 (fi' 0)). reflexivity. }
      { intros. cbv - [split_fin_sum R]. rewrite split_fin_sum_R. reflexivity. }

    - rewrite !bind_ret_l.
      setoid_rewrite (app_asm_correct tp fp _).
      repeat setoid_rewrite bind_bind.
      match goal with
      | [ |- _ (?t >>= _) _ ] => let y := eval compute in t in change t with y
      end.
      rewrite bind_ret_l. cbn. rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      unfold from_bif, FromBifunctor_ktree_fin.
      setoid_rewrite bind_ret_l.
      rewrite bind_ret_r'.
      { rewrite (unique_f0 (fi' 0)). reflexivity. }
      { intros. cbv - [split_fin_sum L]. rewrite split_fin_sum_L. reflexivity. }
  Qed.

  (** [while_asm] is denoted as the loop of the body with two entry point, the exit
      of the loop, and the body in which we have the same structure as for the conditional *)
  Notation label_case := (split_fin_sum _ _).

  Lemma while_asm_correct (e : list instr) (p : asm 1 1) :
      denote_asm (while_asm e p)
    ⩯ (loop (C := sub (ktree _) fin) (fun l : fin (1 + 1) =>
         match label_case l with
         | inl _ =>
           denote_list e ;;
           v <- trigger (GetReg tmp_if) ;;
           if (v:value) then Ret (fS f0) else (denote_asm p f0;; Ret f0)
         | inr _ => Ret f0
         end)).
  Proof.
    unfold while_asm.
    rewrite loop_asm_correct.
    apply Proper_loop.
    rewrite relabel_asm_correct.
    rewrite fmap_id0, cat_id_l.
    rewrite app_asm_correct.
    rewrite if_asm_correct.
    intros x.
    cbn.
    unfold to_bif, ToBifunctor_ktree_fin.
    rewrite bind_ret_l.
    destruct (label_case x); cbn.
    - rewrite !bind_bind. setoid_rewrite bind_ret_l. setoid_rewrite bind_bind.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      repeat rewrite bind_bind.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      unfold from_bif, FromBifunctor_ktree_fin; cbn.
      repeat rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.
      destruct u0.
      + rewrite (pure_asm_correct _ _); cbn.
        rewrite !bind_ret_l.
        apply eqit_Ret.
        apply unique_fin; reflexivity.

      + rewrite (relabel_asm_correct _ _ _ _). cbn.
        rewrite bind_ret_l.
        setoid_rewrite bind_bind.
        eapply eutt_clo_bind; try reflexivity.
        intros ? ? [].
        repeat rewrite bind_ret_l.
        apply eqit_Ret.
        rewrite (unique_f0 u1).
        apply unique_fin; reflexivity.

    - cbn.
      rewrite (pure_asm_correct _ _).
      rewrite bind_bind. cbn.
      unfold from_bif, FromBifunctor_ktree_fin.
      rewrite !bind_ret_l.
      apply eqit_Ret.
      rewrite (unique_f0 f).
      apply unique_fin; reflexivity.
Qed.

Definition relabel_output  : fin (1 + 2) -> fin (1 + (1 + 2)) :=
  bimap (id_ _) inr_.

Opaque L.

Lemma while_asm_exc_correct (e : list instr) (p : asm 1 (1 + 2 )) :
   denote_asm (while_asm_exc e p)
 ⩯ (loop (C := sub (ktree _) fin) (fun l : fin (1 + 1) =>
         match label_case l with
         | inl _ =>
           denote_list e;;
           v <- trigger (GetReg tmp_if) ;;
           if (v:value)
           then Ret (fS f0)
           else (l' <- denote_asm p f0;; Ret (relabel_output l')  )
         | inr _ => Ret (f0)
         end)) .
Proof.
  unfold while_asm_exc. rewrite loop_asm_correct. apply Proper_loop.
  rewrite relabel_asm_correct. rewrite app_asm_correct. rewrite pure_asm_correct.
  rewrite if_asm_correct. cbn.  rewrite fmap_id0. rewrite cat_id_l.
  unfold relabel_output.
  do 5 red. intros. unfold cat, Cat_sub, cat, Cat_Kleisli.
  cbn. rewrite bind_bind. setoid_rewrite bind_ret_l. cbn.
  destruct (label_case (a : fin (1 + 1) )); cbn.
  - repeat setoid_rewrite bind_bind. eapply eqit_bind'; try reflexivity. intros [] [] _ ; subst.
    eapply eqit_bind'; try reflexivity. intros; subst.
    destruct r2.
    + specialize @pure_asm_correct as Hpac. do 5 red in Hpac. setoid_rewrite Hpac.
      clear Hpac. cbn. repeat setoid_rewrite bind_ret_l.
      apply eqit_Ret. cbn. unfold unsubm. apply unique_fin. auto.
    + unfold direct_output_while_exc. specialize @relabel_asm_correct as Hrac.
      do 5 red in Hrac. rewrite Hrac. cbn. repeat rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l. cbn. unfold unsubm, id_, Id_sub, id_, Id_Fun.
      eapply eqit_bind'; try reflexivity. intros; subst. apply eqit_Ret. apply unique_fin.
      destruct r0 as [n Hn].
      do 3 (destruct n; auto). lia.
  - unfold cat, Cat_sub, cat, Cat_Kleisli. cbn. rewrite bind_bind.
    rewrite bind_ret_l. unfold inr_, Inr_sub, inr_, Inr_Kleisli, lift_ktree_. cbn.
    unfold cat. rewrite bind_bind. rewrite bind_ret_l. unfold from_bif, FromBifunctor_ktree_fin.
    rewrite bind_ret_l.
    setoid_rewrite unique_f0. cbn.
    unfold unsubm.  unfold merge, case_, Case_sub, to_bif, ToBifunctor_Fun_fin.
    cbn. unfold cat, Cat_Fun. rewrite split_fin_sum_R. apply eqit_Ret.
    cbn. unfold id_, Id_sub, id_, Id_Fun. cbn. apply unique_fin. cbn. Local Transparent L.
    auto.
Qed.

Lemma trycatch_asm_correct (p : asm 1 (1 + (1 + 1) )) (c : asm 1 3) :
  denote_asm (trycatch_asm p c)
⩯ denote_asm p >>> case_ inl_ (merge >>> denote_asm c ).
Proof.
 unfold trycatch_asm. rewrite seq_asm_correct. repeat rewrite relabel_asm_correct.
 rewrite app_asm_correct.  do 5 red. intros. cbn.
 repeat rewrite bind_bind. repeat setoid_rewrite bind_ret_l.
 unfold unsubm, id_, Id_sub, id_, Id_Fun. eapply eqit_bind'; try reflexivity.
 intros; subst. cbn. destruct r2 as [l Hl].
 do 3 (try destruct l as [ | l]; auto); try lia; cbn; repeat rewrite bind_bind.
 - repeat setoid_rewrite bind_ret_l. cbn. unfold pure_ret_asm.
   specialize (@pure_asm_correct) as Hpac. do 5 red in Hpac. rewrite Hpac.
   setoid_rewrite bind_ret_l. apply eqit_Ret. cbn. apply unique_fin. auto.
 - repeat setoid_rewrite bind_ret_l. cbn. unfold id.
   unfold merge, case_, Case_sub, case_, Case_Kleisli, case_sum, to_bif, ToBifunctor_Fun_fin.
   cbn. setoid_rewrite <- bind_ret_r at 4. eapply eqit_bind' with (RR := eq).
   + match goal with |- eqit eq true true (denote_asm c ?f1) (denote_asm c (?f2) ) => assert (f1 = f2) end.
   { apply unique_fin. auto. }
   timeout 5 rewrite H. reflexivity.
   + intros; subst. destruct r2. cbn. apply eqit_Ret. apply unique_fin. cbn. lia.
 - repeat setoid_rewrite bind_ret_l. cbn. setoid_rewrite <- bind_ret_r at 4.
   eapply eqit_bind' with (RR := eq).
   + match goal with |- eqit eq true true (denote_asm c ?f1) (denote_asm c (?f2) ) => assert (f1 = f2) end.
     { apply unique_fin. auto. }
     rewrite H. reflexivity.
   + intros; subst. apply eqit_Ret. apply unique_fin. destruct r2. cbn. lia.
Qed.


  Definition link_with_exc : ktree_fin ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) (1 + 2) 1  :=
    case_ (id_ _)
    (case_ (C := ktree_fin _ )
            (fun _ : fin 1 => v <- trigger (Throw Public);; match v : void with end )
            (fun _ : fin 1 => v <- trigger (Throw Private);; match v : void with end )).

  Lemma compile_compile_stmt_correct (s : stmt) :
    denote_asm (compile s)
  ⩯ denote_asm (compile_stmt s) >>> link_with_exc .
  Proof.
    unfold compile, link_with_exc.
    cbn in *. rewrite seq_asm_correct. rewrite relabel_asm_correct. remember (app_asm (raise_asm Public) (raise_asm Private) ) as app.
    assert (denote_asm (app_asm (@id_asm 1) app) ⩯ bimap (denote_asm id_asm) (denote_asm app) ).
    { rewrite app_asm_correct. reflexivity. }
    rewrite H. unfold id_asm. rewrite pure_asm_correct. rewrite Heqapp.
    rewrite app_asm_correct.
    do 5 red. intros. cbn. eapply eqit_bind'; try reflexivity. intros; subst.
    repeat setoid_rewrite bind_bind. repeat setoid_rewrite bind_ret_l. cbn.
    destruct r2 as [l Hl].
Transparent denote_asm.
    do 3 (try destruct l as [ | l]; cbn ); try lia; repeat setoid_rewrite bind_ret_l.
    - apply eqit_Ret. apply unique_fin. auto.
    - cbn. rewrite bind_bind. setoid_rewrite bind_ret_l. cbn.
      rewrite bind_bind. tau_steps.  apply eqit_Vis. intros [].
    - cbn. rewrite bind_bind. setoid_rewrite bind_ret_l. cbn.
      rewrite bind_bind. tau_steps.  apply eqit_Vis. intros [].
  Qed.

  Lemma early_link_with_exc (p1 p2: ktree_fin ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) 1 (1 + 2) ) :
    p1 >>> case_ p2 inr_ >>> link_with_exc ⩯ p1 >>> link_with_exc >>> p2 >>> link_with_exc.
  Proof.
    unfold cat, Cat_sub, cat, Cat_Kleisli. cbn. repeat setoid_rewrite bind_bind.
    do 5 red. intros. eapply eqit_bind'; try reflexivity. intros; subst.
    destruct r2 as [l Hl]. do 3 (try destruct l as [ | l]; cbn ); try lia;
                             repeat setoid_rewrite bind_ret_l.
    - cbn. reflexivity.
    - cbn. repeat rewrite bind_bind. eapply eqit_bind'; try reflexivity. intros [].
    - cbn. repeat rewrite bind_bind. eapply eqit_bind'; try reflexivity. intros [].
  Qed.



(* where *)
End Linking.

(* ================================================================= *)
(** ** Correctness *)

Section Correctness.

(*
  Arguments interp_imp {Labels} {R}.
  Arguments denote_expr {Labels}.
  Arguments denote_stmt {Labels}.
*)
  (** Correctness of expressions.
      We strengthen [bisimilar]: initial environments are still related by [Renv],
      but intermediate ones must now satisfy [sim_rel].
      Note that by doing so, we use a _heterogeneous bisimulation_: the trees
      return values of different types ([alist var value * unit] for _Asm_,
      [alist var value * value] for _Imp_). The difference is nonetheless mostly
      transparent for the user, except for the use of the more general lemma [eqit_bind'].
   *)
  (* here we need to codify in some way that denote_expr cannot call any asm inlined code,
     which is to say that that interp (denote_expr e) (regs, heap) ≈ Ret (regs, ...) leaving the regs unchanged
     this brings up an interesting point which is that this compiler is correct if you don't care about final register states
     and does this cause other problems down the line?

     ultimately we need to take the program compile it and relate the two programs with the same starting heap and
     possibly different registers,

     suppose we inline the following asm code


     a :=
     START
     BRZ 0 l1 l2

     l1
     Istore (Oimm 0) X
     JMP Exit

     l2
     Istore (Oimm 1) X
     JMP Exit



     c := (if X + X + X = 0 then skip else skip); a

     interp (denote c) = fun (regs, heap) => Ret (regs, if regs 0 = 0 then update heap X 0 else update heap X 1 )

     interp (denote (compile c)) = fun (regs, heap) => let regs' := ... in Ret (if regs' 0 = 0 then update heap X 0 else update heap X 1)

     these denotations are not the same even if we ignore the effects on the registers because a is "bad",
     it makes changes to the heap based on the registers

     for the compiler to be correct, we need to know that no inlined asm code ever does that

     It is not enough to just nuke the registers on the imp side before running inlined code, because I could still write code that
     looks for differences in the registers, and those differences might be there based on expression computations

     If I added a nuke registers instruction to asm that could work, but I think the restriction of imp programs is a better/easier solution

   *)


  (*maybe should be strengthened to requiring too state equivalent memories *)
  Definition valid_asm {T} m : Prop := forall (l1 l2 : registers) (g_asm1 g_asm2 : memory),
    Renv g_asm1 g_asm2 ->
    @eutt ((impExcE sensitivity_lat) +' (IOE sensitivity_lat)) _ _ (state_invariant (@eq T ))
          (m (l1, g_asm1)) (m (l2, g_asm2)).

  Inductive valid_stmt : stmt -> Prop :=
    | validSkip : valid_stmt Skip
    | validAssign x e : valid_stmt (Assign x e)
    | validOuptut l e : valid_stmt (Output l e)
    | validRaise l : valid_stmt (Raise l)
    | validSeq c1 c2 : valid_stmt c1 -> valid_stmt c2 -> valid_stmt (Seq c1 c2)
    | validIf b c1 c2 : valid_stmt c1 -> valid_stmt c2 -> valid_stmt (If b c1 c2)
    | validWhile b c : valid_stmt c -> valid_stmt (While b c)
    | validTryCatch c1 c2 : valid_stmt c1 -> valid_stmt c2 -> valid_stmt (TryCatch c1 c2)
    | validAsmInline (a : asm 1 1) : valid_asm (interp_asm (throw_prefix (denote_asm a f0)))  -> valid_stmt (AsmInline a)
  .

  Lemma compile_expr_correct : forall e g_imp g_asm l1 l2 n,
      Renv g_imp g_asm ->
      eutt (sim_rel l2 n)
            (interp_imp_inline (denote_expr e) (l1,g_imp))
            (interp_asm (denote_list (compile_expr n e)) (l2, g_asm) ).
  Proof.
    induction e; simpl; intros.
    - (* Var case *)
      (* We first compute and eliminate taus on both sides. *)
      force_left.
      rewrite tau_eutt.

      tau_steps.

      (* We are left with [Ret] constructs on both sides, that remains to be related *)
      red; rewrite <-eqit_Ret.
      unfold lookup_default, lookup, Map_alist, LabelledImp.get.

      (* On the _Asm_ side, we bind to [gen_tmp n] a lookup to [varOf v] *)
      (* On the _Imp_ side, we return the value of a lookup to [varOf v] *)
      erewrite Renv_find; [| eassumption].
      apply sim_rel_add; assumption.

    - (* Literal case *)
      (* We reduce both sides to Ret constructs *)
      tau_steps.

      red; rewrite <-eqit_Ret.
      (* _Asm_ bind the litteral to [gen_tmp n] while _Imp_ returns it *)
      apply sim_rel_add; assumption.

    (* The three binary operator cases are identical *)
    - (* Plus case *)
      (* We push [interp_locals] into the denotations *)

      do 2 setoid_rewrite denote_list_app.
      repeat setoid_rewrite interp_state_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_clo_bind.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [ [l_imp' g_imp'] v] [ [g_asm' l'] [] ]    HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      eapply eutt_clo_bind.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [ [l_imp'' g_imp''] v'] [ [g_asm'' l''] []] HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps.
      red. rewrite <- eqit_Ret. clear -HSIM HSIM'.
      red. unfold get_reg, update_reg. cbn. split; try split; try tauto.
      eapply sim_rel_Renv; eauto.
      eapply sim_rel_find_tmp_n_trans in HSIM' as Hn; eauto. apply sim_rel_find in HSIM' as Hsn.
      rewrite Hn. rewrite Hsn. unfold update_reg. rewrite Nat.eqb_refl. auto.
      intros. assert (n <> m). lia. unfold update_reg.
      apply Nat.eqb_neq in H0. rewrite H0.
      red in HSIM'. destruct HSIM' as [_ [? ?] ]. rewrite<-  H2; eauto.
      red in HSIM. destruct HSIM as [ ? [?  ?] ].
      apply H5; eauto.
    - (* Sub case *)
      (* We push [interp_locals] into the denotations *)

      do 2 setoid_rewrite denote_list_app.
      repeat setoid_rewrite interp_state_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_clo_bind.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [ [l_imp' g_imp'] v] [ [g_asm' l'] [] ]    HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      eapply eutt_clo_bind.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [ [l_imp'' g_imp''] v'] [ [g_asm'' l''] []] HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps.
      red. rewrite <- eqit_Ret. clear -HSIM HSIM'.
      red. unfold get_reg. split; try split; try tauto.
      eapply sim_rel_Renv; eauto.
      eapply sim_rel_find_tmp_n_trans in HSIM' as Hn; eauto. apply sim_rel_find in HSIM' as Hsn.
      rewrite Hn. rewrite Hsn. unfold update_reg. rewrite Nat.eqb_refl. auto.
      intros. assert (n <> m). lia. unfold update_reg.
      apply Nat.eqb_neq in H0. rewrite H0.
      red in HSIM'. destruct HSIM' as [_ [? ?] ]. rewrite<-  H2; eauto.
      red in HSIM. destruct HSIM as [ ? [?  ?] ].
      apply H5; eauto.
    - (* Mul case *)
      (* We push [interp_locals] into the denotations *)

      do 2 setoid_rewrite denote_list_app.
      repeat setoid_rewrite interp_state_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_clo_bind.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [ [l_imp' g_imp'] v] [ [g_asm' l'] [] ]    HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      eapply eutt_clo_bind.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [ [l_imp'' g_imp''] v'] [ [g_asm'' l''] []] HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps.
      red. rewrite <- eqit_Ret. clear -HSIM HSIM'.
      red. unfold get_reg. split; try split; try tauto.
      eapply sim_rel_Renv; eauto.
      eapply sim_rel_find_tmp_n_trans in HSIM' as Hn; eauto. apply sim_rel_find in HSIM' as Hsn.
      rewrite Hn. rewrite Hsn. unfold update_reg. rewrite Nat.eqb_refl. auto.
      intros. assert (n <> m). lia. unfold update_reg.
      apply Nat.eqb_neq in H0. rewrite H0.
      red in HSIM'. destruct HSIM' as [_ [? ?] ]. rewrite<-  H2; eauto.
      red in HSIM. destruct HSIM as [ ? [?  ?] ].
      apply H5; eauto.
  Qed.

  (** Correctness of the assign statement.
      The resulting list of instructions is denoted as
      denoting the expression followed by setting the variable.
   *)
  Lemma compile_assign_correct : forall e x,
      bisimilar eq
        ((v <- denote_expr e ;; trigger (Store x v)) : itree ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) unit)
        ((denote_list (compile_assign x e)) : itree ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) unit).
  Proof.
    red; intros.
    unfold compile_assign.
    (* We push interpreters inside of the denotations *)
    unfold interp_imp_inline, interp_asm.
    rewrite denote_list_app.
    do 2 rewrite interp_state_bind.
    (* By correctness of the compilation of expressions,
       we can match the head trees.
     *)
    eapply eutt_clo_bind.
    { eapply compile_expr_correct; eauto. }

    (* Once again, we get related environments *)
    intros [ [l_imp' g_imp'] v]  [ [g_asm' l'] y] HSIM.
    simpl in HSIM.

    (* We can now reduce to Ret constructs *)
    tau_steps.
    red. rewrite <- eqit_Ret.

    (* And remains to relate the results *)
    unfold state_invariant. cbn. split; auto.
    unfold get_reg. destruct HSIM as [ ? [? ?] ].
    rewrite H1. apply Renv_write_local; auto.
  Qed.

  Lemma compile_output_correct : forall s e,
      bisimilar eq
        ((v <- denote_expr e ;; trigger (LabelledImp.LabelledPrint _ s v)) : itree ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) unit)
        ((@denote_list  ((impExcE sensitivity_lat) +' Reg +' Memory +' (IOE sensitivity_lat)) _ _ _ (compile_output s e))).
  Proof.
    red. intros. unfold compile_output. unfold interp_imp_inline, interp_asm.
    rewrite denote_list_app.
    do 2 rewrite interp_state_bind.
    eapply eutt_clo_bind.
    { eapply compile_expr_correct; eauto. }
    intros [ [l_imp' g_imp'] v]  [ [g_asm' l'] y] HSIM.
    simpl in HSIM. cbn.
    do 2 setoid_rewrite interp_state_bind. setoid_rewrite bind_bind. repeat setoid_rewrite interp_state_trigger.
    setoid_rewrite interp_state_ret. cbn. tau_steps.
    unfold get_reg. destruct HSIM as [? [? ?] ]. rewrite H1.
    apply eqit_Vis. intros []. repeat setoid_rewrite bind_ret_l.
    apply eqit_Ret. cbn. split; auto.
  Qed.

  (* The first parameter of [bisimilar] is unnecessary for this development.
     The return type is heterogeneous, the singleton type [F 1] on one side
     and [unit] on the other, hence we instantiate the parameter with the trivial
     relation.
   *)
  Definition TT {A B}: A -> B -> Prop  := fun _ _ => True.
  Hint Unfold TT: core.

  Definition equivalent (s:stmt ) (t:asm 1 1) : Prop :=
    bisimilar TT (denote_stmt s) (denote_asm t f0).

  Inductive RI : (unit + unit) -> (unit + unit + unit) -> Prop :=
  | RI_inl : RI (inl tt) (inl (inl tt))
  | RI_inr : RI (inr tt) (inr tt).

  (* Utility: slight rephrasing of [while] to facilitate rewriting
     in the main theorem.*)
  Lemma while_is_loop {E} (body : itree E (unit+unit)) :
    while body
          ≈ iter (C := ktree _) (fun l : unit + unit =>
                    match l with
                    | inl _ => x <- body;; match x with inl _ => Ret (inl (inl tt)) | inr _ => Ret (inr tt) end
                    | inr _ => Ret (inl (inl tt))   (* Enter loop *)
                    end) (inr tt).
  Proof.
    unfold while.
    rewrite! unfold_iter_ktree.
    rewrite bind_ret_l, tau_eutt.
    rewrite unfold_iter_ktree.
    rewrite unfold_iter.
    rewrite !bind_bind.
    eapply eutt_clo_bind. reflexivity.
    intros. subst.
    destruct u2 as [[]|[]].
    2 : { force_right. reflexivity. }
    rewrite bind_ret_l, !tau_eutt.
    unfold iter, Iter_Kleisli.
    apply eutt_iter' with (RI := fun _ r => inl tt = r).
    - intros _ _ [].
      rewrite <- bind_ret_r at 1.
      eapply eutt_clo_bind; try reflexivity.
      intros [|[]] _ []; apply eqit_Ret; auto; constructor; auto.
    - constructor.
  Qed.

  Definition to_itree' {E A} (f : ktree_fin E 1 A) : itree E (fin A) := f f0.
  Lemma fold_to_itree' {E A} (f : ktree_fin E 1 A) : f f0 = to_itree' f.
  Proof. reflexivity. Qed.

  Global Instance Proper_to_itree' {E A} :
    Proper (eq2 ==> eutt eq) (@to_itree' E A).
  Proof.
    repeat intro.
    apply H.
  Qed.
(*
  Notation Inr_Kleisli := Inr_Kleisli.
  *)

  Definition label_rel {U} (r : U + sensitivity) (l : fin 3) :=
             match r with
             | inl _ => proj1_sig l = 0
             | inr Public => proj1_sig l = 1
             | inr Private => proj1_sig l = 2 end.

  Lemma throw_prefix_denote_expr (e : expr) :
     @throw_prefix sensitivity value (Reg +' Memory +' IOE sensitivity_lat) (denote_expr e) ≈ r <- denote_expr e;; Ret (inl r).
  Proof.
    induction e.
    - cbn. setoid_rewrite throw_prefix_ev. rewrite bind_trigger.
      apply eqit_Vis. intros. rewrite tau_eutt. rewrite throw_prefix_ret.
      reflexivity.
    - cbn. rewrite throw_prefix_ret. rewrite bind_ret_l.
      reflexivity.
    - simpl. rewrite bind_bind. setoid_rewrite bind_bind. rewrite throw_prefix_bind.
      rewrite IHe1. rewrite bind_bind. setoid_rewrite bind_ret_l.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      rewrite throw_prefix_bind. rewrite IHe2. rewrite bind_bind.
      setoid_rewrite bind_ret_l. setoid_rewrite throw_prefix_ret.
      reflexivity.
    - simpl. rewrite bind_bind. setoid_rewrite bind_bind. rewrite throw_prefix_bind.
      rewrite IHe1. rewrite bind_bind. setoid_rewrite bind_ret_l.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      rewrite throw_prefix_bind. rewrite IHe2. rewrite bind_bind.
      setoid_rewrite bind_ret_l. setoid_rewrite throw_prefix_ret.
      reflexivity.
    -  simpl. rewrite bind_bind. setoid_rewrite bind_bind. rewrite throw_prefix_bind.
      rewrite IHe1. rewrite bind_bind. setoid_rewrite bind_ret_l.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      rewrite throw_prefix_bind. rewrite IHe2. rewrite bind_bind.
      setoid_rewrite bind_ret_l. setoid_rewrite throw_prefix_ret.
      reflexivity.
  Qed.

  Ltac adv := match goal with
        | u : unit |- _ => destruct u
        | o : operand |- _ => destruct o
        | |- context G [denote_operand (Oimm _) ] => cbn
        | |- context G [denote_operand (Oreg _) ] => cbn
        | |- forall x, ?P => intro
        | |- context G [Tau _] => setoid_rewrite tau_eutt
        | |- context G [throw_prefix (Ret _)] => setoid_rewrite throw_prefix_ret
        | |- context G [throw_prefix (trigger (SetReg _ _) ) ] => setoid_rewrite throw_prefix_ev
        | |- context G [throw_prefix (trigger (GetReg _) ) ] => setoid_rewrite throw_prefix_ev
        | |- context G [throw_prefix (trigger (Store _ _) ) ] => setoid_rewrite throw_prefix_ev
        | |- context G [throw_prefix (trigger (LabelledImp.LabelledPrint _ _ _) ) ] =>
          setoid_rewrite throw_prefix_ev
        | |- context G [throw_prefix (vis (Throw _) _) ] => setoid_rewrite throw_prefix_exc
        | |- context G [throw_prefix (vis _ _) ] => setoid_rewrite throw_prefix_ev
        | |- context G [x <- (Vis _ _);; _ ] => setoid_rewrite bind_vis
        | |- context G [x <- (trigger _ );; _] => setoid_rewrite bind_vis
        | |- eqit _ _ _ (Vis _ _) (Vis _ _ ) => apply eqit_Vis
        | |- eutt _ (Vis _ _) (vis _ _ ) => apply eqit_Vis
        | |- eqit _ _ _ (Vis _ _) (trigger _ ) => apply eqit_Vis
        | |- eqit _ _ _ (Ret _) (Ret _) => apply eqit_Ret
        | |- context G [x <- (Ret _);; _ ] => setoid_rewrite bind_ret_l
        | |- context G [x <- (from_bif _);; _ ] => setoid_rewrite bind_ret_l
        | |- context G [throw_prefix (y <- _;; _)] => setoid_rewrite throw_prefix_bind
        | |- context G [throw_prefix (to_bif _)] => setoid_rewrite throw_prefix_ret
        | |- context G [split_fin_sum _ _ (merge_fin_sum _ _ _)] => rewrite split_merge
        | |- context G [split_fin_sum _ _ (L _ _ ) ] => rewrite split_fin_sum_L
        | |- context G [split_fin_sum _ _ (R _ _ ) ] => rewrite split_fin_sum_R
        | |- eutt _ (Ret _) (to_bif _) => apply eqit_Ret
        | |- eutt _ (Ret _) (from_bif _) => apply eqit_Ret
      end.

  Lemma exception_to_sum_correct_instr_aux:
    forall i : instr,
      eqit (fun (x : unit + sensitivity) (_ : unit) => x = inl tt) true true
           (throw_prefix (denote_instr i)) (denote_instr i).
  Proof.
    intros i. destruct i; cbn; repeat setoid_rewrite throw_prefix_bind;
      repeat rewrite bind_bind; try destruct src; cbn; repeat adv; auto.
  Qed.



  Lemma exception_to_sum_correct (p : asm 1 1) : eutt label_rel (throw_prefix (denote_asm p f0))
                                                      (denote_asm (exception_to_sum p) f0).
  Proof.
    unfold denote_asm. cbn. repeat setoid_rewrite bind_ret_l.  cbn.
    setoid_rewrite throw_prefix_iter. cbn. eapply eutt_iter' with (RI := eq); auto.
    intros; subst. cbn. repeat setoid_rewrite throw_prefix_bind. repeat rewrite bind_bind.
    destruct p. cbn.
    induction (code j2).
    - cbn. rewrite throw_prefix_bind. repeat rewrite bind_bind.
      set (fun (x : unit + sensitivity) (_ : unit) => x = inl tt) as RR.
      eapply (eqit_bind' RR); try apply exception_to_sum_correct_instr_aux. unfold RR.
      intros; subst. auto.
    - destruct b; cbn; repeat adv.
      + unfold exception_to_sum_branch_reassoc.
        destruct (split_fin_sum internal 1 f); cbn; repeat adv; cbn; repeat adv.
        constructor. cbn. auto. constructor. cbn. destruct f0. cbn. lia.
      + unfold exception_to_sum_branch_reassoc.
        repeat adv. destruct u; repeat adv.
        * destruct (split_fin_sum internal 1 yes); cbn; repeat adv;
          cbn; repeat adv.
          apply eqit_Ret. adv. constructor. auto. apply eqit_Ret. adv. constructor.
          red. destruct f; cbn. lia.
        * destruct (split_fin_sum internal 1 no); cbn; repeat adv;
          cbn; repeat adv.
          apply eqit_Ret. adv. constructor. auto. apply eqit_Ret. adv. constructor.
          red. destruct f; cbn. lia.
     + repeat adv. destruct s; cbn; repeat adv.
       * unfold split_fin_sum. cbn. destruct (lt_dec (internal + 1) internal); try lia.
         cbn. repeat adv. constructor. red. cbn. lia.
       * unfold split_fin_sum. cbn. destruct (lt_dec (internal + 2) internal); try lia.
         cbn. repeat adv. constructor. red. cbn. lia.
  Qed.

  Definition fin3tosum (f : fin 3) : (fin 1) + sensitivity :=
    match proj1_sig f with
    | 0 => inl f0
    | 1 => inr Public
    | 2 => inr Private
    | _ => inl f0 end.

  Definition sumtofin3 (x : fin 1 + sensitivity) : fin 3 :=
    match x with
    | inl _ => f0
    | inr Public => fS f0
    | inr Private => fS (fS f0) end.

  Lemma eutt_label_rel_to_eutt : forall E (t1 : itree E (fin 1 + sensitivity) ) (t2 : itree E (fin 3)),
      eutt label_rel t1 t2 -> t1 ≈ (t2 >>= (fun x => Ret (fin3tosum x))).
  Proof.
    intros. rewrite <- bind_ret_r. eapply eqit_bind'; eauto.
    intros. red in H0. destruct r1 as [ ? | [ | ] ]; unfold fin3tosum; rewrite H0; try reflexivity.
    setoid_rewrite unique_f0. reflexivity.
  Qed.


  (*eq might be too strong without proof irrelevance *)
  Lemma eutt_label_rel_to_eutt' : forall E (t1 : itree E (fin 1 + sensitivity) ) (t2 : itree E (fin 3)),
      eutt label_rel t1 t2 -> t2 ≈ (t1 >>= (fun x => Ret (sumtofin3 x))).
  Proof.
    intros. rewrite <- bind_ret_r. apply eqit_flip in H. eapply eqit_bind'; eauto.
    intros. red in H0. destruct r2 as [ ? | [ | ] ]; cbn.
    - setoid_rewrite (unique_fin _ r1 f0); auto. reflexivity.
    - setoid_rewrite (unique_fin _ r1 (fS f0)); auto. reflexivity.
    - setoid_rewrite (unique_fin _ r1 (fS (fS f0))); auto. reflexivity.
  Qed.


  Lemma exception_to_sum_correct_eutt_eq (p : asm 1 1) : eutt eq (throw_prefix (denote_asm p f0))
                                                      ((denote_asm (exception_to_sum p) f0) >>= (fun x : fin 3 => Ret (fin3tosum x) )).
  Proof.
    apply eutt_label_rel_to_eutt. apply exception_to_sum_correct.
  Qed.

  Lemma exception_to_sum_correct_eutt_eq' (p : asm 1 1) : eutt eq (denote_asm (exception_to_sum p) f0)
                                                               (throw_prefix (denote_asm p f0) >>= fun x => Ret (sumtofin3 x)).
  Proof.
    apply eutt_label_rel_to_eutt'. apply exception_to_sum_correct.
  Qed.

  Lemma compile_stmt_correct (s : stmt) : valid_stmt s ->
        bisimilar label_rel (throw_prefix (denote_stmt s)) (denote_asm (compile_stmt s) f0).
  Proof.
    induction s; intros Hs.
    - (* Assign *)
     simpl. rewrite raw_asm_block_correct. rewrite denote_after.
     rewrite throw_prefix_bind. rewrite throw_prefix_denote_expr.
     rewrite bind_bind. setoid_rewrite bind_ret_l.
     assert (forall r, throw_prefix (Err := sensitivity) (E := (Reg +' Memory +' (IOE _))) (trigger (Store x r) ) ≈ trigger (Store x r);; Ret (inl tt)  ).
     {
       intros. rewrite bind_trigger. setoid_rewrite throw_prefix_ev.
       apply eqit_Vis. setoid_rewrite tau_eutt. intros []. rewrite throw_prefix_ret. reflexivity.
     }
     setoid_rewrite H.
     setoid_rewrite <- bind_ret_r at 6.
     rewrite <- bind_bind.
     setoid_rewrite bind_bind at 2.
     eapply bisimilar_bind'.
     { eapply compile_assign_correct; eauto. }
     intros [] [] _. cbn. rewrite bind_ret_l.
     red. intros. unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret.
     apply eqit_Ret; split; cbn; auto.
    - (* Seq *)
      inversion Hs. subst.
      simpl. Opaque denote_asm. cbn.
      assert (denote_asm (seq_asm_exc (compile_stmt s1) (compile_stmt s2)) f0 ≈
              (denote_asm (compile_stmt s1) >>> case_ (denote_asm (compile_stmt s2)) inr_) f0).
      { specialize (@seq_asm_exc_correct) as Hsaec.
      do 5 red in Hsaec. rewrite Hsaec.  reflexivity. }
      rewrite H. rewrite throw_prefix_bind.
      cbn. eapply bisimilar_bind'; eauto.
      intros. destruct a; cbn in H0; try destruct s.
      + destruct u. assert (a' = f0). { apply unique_fin; auto. }
        subst. setoid_rewrite bind_ret_l. cbn. setoid_rewrite unique_f0.
        auto.
      + assert (a' = fS f0). { apply unique_fin; auto. }
        subst. setoid_rewrite bind_ret_l. cbn. rewrite bind_ret_l.
        unfold from_bif, FromBifunctor_ktree_fin . cbn.
        red. intros. unfold interp_imp_inline, interp_asm.
        repeat rewrite interp_state_ret. apply eqit_Ret.
        split; auto.
      + assert (a' = fS (fS f0)). { apply unique_fin; auto. }
        subst. setoid_rewrite bind_ret_l. cbn. rewrite bind_ret_l.
        unfold from_bif, FromBifunctor_ktree_fin . cbn.
        red. intros. unfold interp_imp_inline, interp_asm.
        repeat rewrite interp_state_ret. apply eqit_Ret.
        split; auto.
    - (* If *)
      inversion Hs. subst.
      simpl.  rewrite fold_to_itree'. rewrite if_asm_correct.
      cbn. rewrite throw_prefix_bind. rewrite <- fold_to_itree'.
      rewrite throw_prefix_denote_expr. rewrite bind_bind. setoid_rewrite bind_ret_l.
      red. intros. unfold interp_imp_inline, interp_asm. do 2 rewrite interp_state_bind.
      eapply eutt_clo_bind.
      { eapply compile_expr_correct; eauto. }
      intros. destruct u1 as [ [reg0 mem0] v]. destruct u2 as [ [reg mem] ?  ]. destruct u.
      cbn. assert (Htmp : reg 0 = v).
      { cbn in H0. tauto. }
      apply sim_rel_Renv in H0.
      rewrite interp_state_bind. rewrite interp_state_trigger. cbn.
      rewrite bind_ret_l. cbn. setoid_rewrite Htmp.
      destruct v.
      + apply IHs2; auto.
      + apply IHs1; auto.
    - (* While *) (* throw_prefix_bind proof should be the main thing I need *)
                  (* maybe a throw_prefix_iter as well *)
      inversion Hs. subst.
      simpl. rewrite while_is_loop. rewrite fold_to_itree'. rewrite while_asm_exc_correct. rewrite <- fold_to_itree'.
      setoid_rewrite throw_prefix_iter.
      unfold loop.
      (* might have written while_asm_exc wrong *)
      unfold loop. cbn. setoid_rewrite bind_bind. rewrite bind_ret_l.
      setoid_rewrite bind_ret_l.
      eapply bisimilar_iter with (R := fun a l => match a with inl _ => proj1_sig l = 0 | inr _ => proj1_sig l = 1 end);
      auto.
      intros [ | ] l Hl.
      + cbn. assert (l = f0). { apply unique_fin; auto. } rewrite H. cbn.
        setoid_rewrite bind_bind.
        setoid_rewrite throw_prefix_bind. rewrite throw_prefix_denote_expr.
        repeat rewrite bind_bind. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
        red. intros.
        unfold interp_imp_inline, interp_asm.
        do 2 rewrite interp_state_bind. eapply eutt_clo_bind.
        {  eapply compile_expr_correct; auto. }
        intros [ [reg0 mem0] v] [ [reg mem] [] ]. cbn.
        intros [HRenv [ Hreg0  ? ] ].
        destruct v.
        * setoid_rewrite bind_ret_l. setoid_rewrite throw_prefix_ret. setoid_rewrite bind_ret_l.
          rewrite bind_trigger. rewrite interp_state_vis. cbn.
          setoid_rewrite bind_ret_l. rewrite tau_eutt. cbn. unfold get_reg, tmp_if.
          rewrite Hreg0. repeat setoid_rewrite bind_ret_l. cbn.
          unfold to_bif, ToBifunctor_ktree_fin. cbn. repeat rewrite interp_state_ret.
          apply eqit_Ret. split; auto. cbn. constructor. red. auto.
        * repeat setoid_rewrite bind_bind. setoid_rewrite throw_prefix_bind.
          setoid_rewrite bind_bind. rewrite bind_trigger. rewrite interp_state_vis.
          cbn. setoid_rewrite bind_ret_l. rewrite tau_eutt. cbn. unfold get_reg, tmp_if. rewrite Hreg0.
          setoid_rewrite bind_bind. do 2 rewrite interp_state_bind. eapply eutt_clo_bind.
          { apply IHs; auto. }
          intros [ [reg'0 mem'0 ] [ [] | [ | ] ] ] [ [reg' mem' ] l' ] Hst.
          -- cbn. setoid_rewrite bind_ret_l. setoid_rewrite throw_prefix_ret.
             setoid_rewrite bind_ret_l. cbn. red in Hst. cbn in Hst. assert (l' = f0).
             apply unique_fin. cbn; tauto. subst. cbn. repeat setoid_rewrite bind_ret_l.
             cbn. unfold to_bif, ToBifunctor_ktree_fin. cbn. repeat rewrite interp_state_ret.
             apply eqit_Ret.  split; try tauto. cbn. constructor. auto.
          -- destruct Hst. red in H3. cbn in H3. cbn. setoid_rewrite bind_ret_l.
             assert (l' = fS f0). apply unique_fin. cbn; tauto. subst.
             cbn. repeat setoid_rewrite bind_ret_l. cbn. unfold to_bif, ToBifunctor_ktree_fin. cbn.
             repeat rewrite interp_state_ret. apply eqit_Ret. split; auto. constructor. red. auto.
          -- destruct Hst. red in H3. cbn in H3. cbn. setoid_rewrite bind_ret_l.
             assert (l' = fS (fS f0)). apply unique_fin. cbn; tauto. subst.
             cbn. repeat setoid_rewrite bind_ret_l. cbn. unfold to_bif, ToBifunctor_ktree_fin. cbn.
             repeat rewrite interp_state_ret. apply eqit_Ret. split; auto. constructor. red. auto.
      + cbn. assert (l = fS f0). { apply unique_fin; auto. } subst. cbn.
        setoid_rewrite throw_prefix_ret. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
        cbn. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l. cbn. repeat rewrite bind_bind.
        rewrite bind_ret_l. repeat setoid_rewrite bind_ret_l. cbn.
        unfold to_bif, ToBifunctor_ktree_fin. cbn. red. intros.
        unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret. apply eqit_Ret.
        split; auto. cbn. constructor. auto.
    - (* Skip *)
      simpl. unfold pure_ret_asm. rewrite fold_to_itree'.
      rewrite pure_asm_correct. rewrite throw_prefix_ret. cbn.
      red. intros. unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret. apply eqit_Ret.
      split; cbn; auto.
    - (* Output *)
      simpl. rewrite raw_asm_block_correct. rewrite denote_after.
      rewrite throw_prefix_bind. rewrite throw_prefix_denote_expr.
      rewrite bind_bind. setoid_rewrite bind_ret_l. cbn.
      setoid_rewrite throw_prefix_ev. setoid_rewrite tau_eutt. setoid_rewrite throw_prefix_ret.
      setoid_rewrite <- bind_trigger.

      setoid_rewrite <- bind_ret_r at 6.
     rewrite <- bind_bind.
     setoid_rewrite bind_bind at 2.
     eapply bisimilar_bind'.
     { eapply compile_output_correct; eauto. }
     intros [] [] _. cbn. rewrite bind_ret_l.
     red. intros. unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret.
     apply eqit_Ret; split; cbn; auto.
    - (* Raise *)
      simpl. unfold pure_exc_asm. rewrite fold_to_itree'. rewrite pure_asm_correct.
      cbn. unfold trigger.
      setoid_rewrite unfold_iter_ktree. cbn. rewrite bind_ret_l.
      red. intros. unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret.
      apply eqit_Ret. split; cbn; destruct s; auto.
    - (* TryCatch *)
      inversion Hs. subst.
      simpl. rewrite fold_to_itree'. rewrite trycatch_asm_correct.
      cbn. rewrite throw_prefix_of_try_catch. rewrite try_catch_to_throw_prefix.
      set (fun (r : unit + sensitivity + sensitivity) (l :fin 3) =>
             match r with
             | inl (inl _ ) => label_rel (inl tt) l
             | inl (inr s) => False
             | inr s => @label_rel unit (inr s) l end
          ) as R .
      eapply bisimilar_bind' with (RAA' := R).
      + cbn. rewrite throw_prefix_bind. setoid_rewrite <- bind_ret_r at 5.
        eapply bisimilar_bind'; eauto. intros.
        destruct a.
        * rewrite throw_prefix_ret. red. intros.
          unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret.
          apply eqit_Ret. split; auto.
        * red. intros.
          unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret.
          apply eqit_Ret. split; auto.
      + intros.  destruct a as [ [ | ] | ]; try destruct s; cbn in H; try contradiction.
        * cbn in H. assert (a' = f0).
          { apply unique_fin. auto. }
          subst. repeat setoid_rewrite bind_ret_l. cbn.
          unfold from_bif, FromBifunctor_ktree_fin.
          red; intros.
          unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret.
          apply eqit_Ret. split; auto.
        *  assert (a' = fS f0).
          { apply unique_fin. auto. }
          subst. repeat setoid_rewrite bind_ret_l. cbn.
          repeat setoid_rewrite bind_ret_l. cbn. unfold id.
          setoid_rewrite unique_f0. auto.
        * assert (a' = fS (fS f0)).
          { apply unique_fin. auto. }
          subst. repeat setoid_rewrite bind_ret_l. cbn.
          repeat setoid_rewrite bind_ret_l. cbn. unfold id.
          setoid_rewrite unique_f0. auto.
    - (* AsmInline *)
      inversion Hs. subst. rename H0 into Hp. red in Hp.
      cbn. unfold denote_asm_inline. rewrite throw_prefix_bind. setoid_rewrite exception_to_sum_correct_eutt_eq'.
      eapply bisimilar_bind'. Unshelve. 3 : { cbn. apply eq. }
      + red. intros. eauto.
      + intros; subst. cbn in a. destruct a; destruct a'; inv H; try setoid_rewrite throw_prefix_ret; cbn.
        * repeat intro. setoid_rewrite interp_state_ret. apply eqit_Ret; constructor; cbn; auto.
        * repeat intro; setoid_rewrite interp_state_ret. apply eqit_Ret. constructor; cbn; auto.
          destruct s0; auto.
  Qed.

(** Correctness of the compiler.
      After interpretation of the [Locals], the source _Imp_ statement
      denoted as an [itree] and the compiled _Asm_ program denoted
      as an [itree] are equivalent up-to-taus.
      The correctness is termination sensitive, but nonetheless a simple
      induction on statements.
      We are only left with reasoning about the functional correctness of
      the compiler, all control-flow related reasoning having been handled
      in isolation.
   *)
  Theorem compile_correct (s : stmt) : valid_stmt s ->
    equivalent s (compile s).
  Proof.
    unfold equivalent. intro Hs.  unfold compile. rewrite throw_prefix_bind_decomp.
    rewrite fold_to_itree'. rewrite seq_asm_correct. rewrite relabel_asm_correct.
    do 2 rewrite app_asm_correct.  rewrite <- fold_to_itree'. cbn.
    eapply bisimilar_bind'. eapply compile_stmt_correct; auto.
    specialize (@pure_asm_correct ) as Hpac. do 5 red in Hpac.
    intros [ [] | [ | ] ] l Hl; repeat setoid_rewrite bind_ret_l; cbn.
    - assert (l = f0). { red in Hl. apply unique_fin. auto. } subst.
      cbn. setoid_rewrite Hpac. repeat setoid_rewrite bind_ret_l.
      red. intros. unfold interp_imp_inline, interp_asm. repeat rewrite interp_state_ret.  apply eqit_Ret.
      split; auto.
    - assert (l = fS f0). { red in Hl. apply unique_fin. auto. } subst.
      cbn. repeat setoid_rewrite bind_ret_l.
      red. intros. unfold interp_imp_inline, interp_asm. rewrite bind_bind. rewrite bind_trigger.
      rewrite interp_state_vis. cbn. setoid_rewrite bind_bind. unfold raise_asm. cbn.
      Transparent denote_asm. cbn. repeat setoid_rewrite bind_ret_l.
      setoid_rewrite unfold_iter_ktree at 3. cbn. repeat setoid_rewrite bind_bind.
      rewrite bind_trigger. rewrite interp_state_bind. rewrite interp_state_trigger.
      cbn. rewrite bind_bind. rewrite bind_trigger. apply eqit_Vis. intros [].
    - assert (l = fS (fS f0)). { red in Hl. apply unique_fin. auto. } subst.
      cbn. repeat setoid_rewrite bind_ret_l.
      red. intros. unfold interp_imp_inline, interp_asm. rewrite bind_bind. rewrite bind_trigger.
      rewrite interp_state_vis. cbn. setoid_rewrite bind_bind. unfold raise_asm. cbn.
      Transparent denote_asm. cbn. repeat setoid_rewrite bind_ret_l.
      setoid_rewrite unfold_iter_ktree at 3. cbn. repeat setoid_rewrite bind_bind.
      rewrite bind_trigger. rewrite interp_state_bind. rewrite interp_state_trigger.
      cbn. rewrite bind_bind. rewrite bind_trigger. apply eqit_Vis. intros [].
  Qed.

End Correctness.

(*
c:=
START
BJMP [0] l1 l2

l1
STORE X <- 0
JMP EXIT

l2
STORE X <- 1
JMP EXIT



if X = 0 then skip else skip; Nuke regs; Inline c


*)


(* ================================================================= *)
(** ** Closing word. *)

(** Through this medium-sized example, we have seen how to use [itree]s to
    denote two languages, how to run them and how to prove correct a compiler
    between them.
    We have emphasized that the theory of [ktree]s allowed us to decouple
    all reasoning about the control-flow from the proof of the compiler itself.
    The resulting proof is entirely structurally inductive and equational. In
    particular, we obtain a final theorem relating potentially infinite
    computations without having to write any cofixed-point.

    If this result is encouraging, one might always wonder how things scale.

    A first good sanity check is to extend the languages with a _Print_
    instruction.
    It requires to add a new event to the language and therefore makes the
    correctness theorem relate trees actually still containing events.
    This change, which a good exercise to try, turns out to be as
    straightforward as one would hope. The only new lemma needed is to show
    that [interp_locals] leaves the new [Print] event untouched.
    This extension can be found in the _tutorial-print_ branch.

    More importantly, our compiler is fairly stupid and inefficient: it creates
    blocks for each compiled statement! One would hope to easily write and
    prove an optimization coalescing elementary blocks together.

    A first example of optimization at the [asm] level proved correct is
    demonstrated in the _AsmOptimization.v_ file.
 *)
