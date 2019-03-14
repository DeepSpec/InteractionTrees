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
     Effects.Env
     Interp.MorphismsFacts
     Interp.RecursionFacts
     Effects.StateFacts.

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

Section EUTT.

  Context {E: Type -> Type}.

  Instance eq_itree_run_env {E R} {K V map} {Mmap: Maps.Map K V map}:
    Proper (@eutt (envE K V +' E) R R eq ==> eq ==> @eutt E (prod map R) (prod map R) eq)
           (run_env R).
  Proof.
    eapply eutt_interp_state.
  Qed.

End EUTT.

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

Section Simulation_Relation.

  Variable E: Type -> Type.
  Context {HasLocals: Locals -< E} {HasMemory: Memory -< E}.

  Variant Rvar : var -> var -> Prop :=
  | Rvar_var v : Rvar (varOf v) v.

  Definition Renv (g_asm g_imp : alist var value) : Prop :=
    forall k_asm k_imp, Rvar k_asm k_imp ->
                   forall v, alist_In k_imp g_imp v <-> alist_In k_asm g_asm v.

  Definition sim_rel g_asm n: alist var value * unit -> alist var value * value -> Prop :=
    fun '(g_asm', _) '(g_imp',v) =>
      Renv g_asm' g_imp' /\            (* we don't corrupt any of the imp variables *)
      alist_In (gen_tmp n) g_asm' v /\ (* we get the right value *)
      (forall m, m < n -> forall v,              (* we don't mess with anything on the "stack" *)
            alist_In (gen_tmp m) g_asm v <-> alist_In (gen_tmp m) g_asm' v).

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

  Lemma Renv_write_local:
    forall (x : Imp.var) (a a0 : alist var value) (v : Imp.value),
      Renv a a0 -> Renv (alist_add (varOf x) v a) (alist_add x v a0).
  Proof.
    intros k m m' v.
    repeat intro.
    red in H.
    specialize (H k_asm k_imp H0 v0).
    inv H0.
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

End Simulation_Relation.

Section Correctness.

  Context {E': Type -> Type}.
  Context {HasMemory: Memory -< E'}.
  Context {HasExit: Exit -< E'}.
  Notation E := (Locals +' E').

  Definition interp_locals {R: Type} (t: itree E R) (s: alist var value)
    : itree E' (alist var value * R) :=
    run_env _ (interp (bimap evalLocals (id_ _)) _ t) s.

  Instance eutt_interp_locals {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (alist var value) R) (prod _ R) eq)
           interp_locals.
  Proof.
    repeat intro.
    unfold interp_locals.
    unfold run_env.
    rewrite H0. eapply eutt_interp_state; auto.
    rewrite H; reflexivity.
  Qed.

  Lemma interp_locals_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (s: alist var value),
      @eutt E' _ _ eq
            (interp_locals (ITree.bind t k) s)
            (ITree.bind (interp_locals t s) (fun s' => interp_locals (k (snd s')) (fst s'))).
  Proof.
    intros.
    unfold interp_locals.
    unfold run_env.
    rewrite interp_bind.
    rewrite interp_state_bind.
    reflexivity.
  Qed.

  Definition eq_locals {R1 R2} (RR : R1 -> R2 -> Prop)
             (Renv_ : _ -> _ -> Prop)
             t1 t2 :=
    forall g1 g2,
      Renv_ g1 g2 ->
      eutt (fun a (b : alist var value * R2) => Renv_ (fst a) (fst b) /\ RR (snd a) (snd b))
           (interp_locals t1 g1)
           (interp_locals t2 g2).

  Instance eutt_eq_locals (Renv_ : _ -> _ -> Prop) {R} RR :
    Proper (eutt eq ==> eutt eq ==> iff) (@eq_locals R R RR Renv_).
  Proof.
    repeat intro.
    split; repeat intro.
    - rewrite <- H, <- H0; auto.
    - rewrite H, H0; auto.
  Qed.

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

  Lemma eq_locals_loop {A B C} x (t1 t2 : C + A -> itree E (C + B)) :
    (forall l, eq_locals eq Renv (t1 l) (t2 l)) ->
    eq_locals eq Renv (loop t1 x) (loop t2 x).
  Proof.
    unfold eq_locals, interp_locals, run_env.
    intros. unfold loop.
    rewrite 2 interp_loop.
    eapply interp_state_loop; auto.
  Qed.

  Ltac force_left :=
    match goal with
    | |- eutt _ ?x _ => rewrite (itree_eta x); cbn
    end.

  Ltac force_right :=
    match goal with
    | |- eutt _ _ ?x => rewrite (itree_eta x); cbn
    end.

  Ltac untau_left := force_left; rewrite tau_eutt.
  Ltac untau_right := force_right; rewrite tau_eutt.


  Notation "(% x )" := (gen_tmp x) (at level 1).

  Lemma compile_expr_correct : forall e g_imp g_asm n,
      Renv g_asm g_imp ->
      eutt (sim_rel g_asm n)
           (interp_locals (denote_list (compile_expr n e)) g_asm)
           (interp_locals (denoteExpr e) g_imp).
  Proof.
    induction e; simpl; intros.
    - repeat untau_left.
      repeat untau_right.
      force_left; force_right.
      apply eutt_ret.
      erewrite <- Renv_find; [| eassumption].
      apply sim_rel_add; assumption.
    - repeat untau_left.
      force_left.
      force_right.
      apply eutt_ret.
      apply sim_rel_add; assumption.
    - do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      + eapply IHe1; assumption.
      + intros [g_asm' []] [g_imp' v] HSIM.
        eapply eutt_bind_gen.
        eapply IHe2.
        eapply sim_rel_Renv; eassumption.
        intros [g_asm'' []] [g_imp'' v'] HSIM'.
        repeat untau_left.
        force_left; force_right.
        simpl fst in *.
        (* TODO: Simplify this *)
        apply eutt_ret.
        {
          generalize HSIM; intros LU; apply sim_rel_find_tmp_n in LU.
          unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto; fold (alist_In (%n) g_asm'' v) in LU.
          generalize HSIM'; intros LU'; apply sim_rel_find_tmp_n in LU'.
          rewrite LU,LU'.
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
            destruct HSIM as [_ [_ HSIM]].
            destruct HSIM' as [_ [_ HSIM']].
            rewrite HSIM; [| auto with arith].
            rewrite HSIM'; [| auto with arith].
            reflexivity.
          }
        }
    - do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      + eapply IHe1; assumption.
      + intros [g_asm' []] [g_imp' v] HSIM.
        eapply eutt_bind_gen.
        eapply IHe2.
        eapply sim_rel_Renv; eassumption.
        intros [g_asm'' []] [g_imp'' v'] HSIM'.
        repeat untau_left.
        force_left; force_right.
        simpl fst in *.
        (* TODO: Simplify this *)
        apply eutt_ret.
        {
          generalize HSIM; intros LU; apply sim_rel_find_tmp_n in LU.
          unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto; fold (alist_In (%n) g_asm'' v) in LU.
          generalize HSIM'; intros LU'; apply sim_rel_find_tmp_n in LU'.
          rewrite LU,LU'.
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
            destruct HSIM as [_ [_ HSIM]].
            destruct HSIM' as [_ [_ HSIM']].
            rewrite HSIM; [| auto with arith].
            rewrite HSIM'; [| auto with arith].
            reflexivity.
          }
        }
    - do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      + eapply IHe1; assumption.
      + intros [g_asm' []] [g_imp' v] HSIM.
        eapply eutt_bind_gen.
        eapply IHe2.
        eapply sim_rel_Renv; eassumption.
        intros [g_asm'' []] [g_imp'' v'] HSIM'.
        repeat untau_left.
        force_left; force_right.
        simpl fst in *.
        (* TODO: Simplify this *)
        apply eutt_ret.
        {
          generalize HSIM; intros LU; apply sim_rel_find_tmp_n in LU.
          unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto; fold (alist_In (%n) g_asm'' v) in LU.
          generalize HSIM'; intros LU'; apply sim_rel_find_tmp_n in LU'.
          rewrite LU,LU'.
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
            destruct HSIM as [_ [_ HSIM]].
            destruct HSIM' as [_ [_ HSIM']].
            rewrite HSIM; [| auto with arith].
            rewrite HSIM'; [| auto with arith].
            reflexivity.
          }
        }
  Qed.

  Lemma compile_assign_correct : forall e x,
      eq_locals eq Renv
                (denote_list (compile_assign x e))
                (v <- denoteExpr e ;; lift (SetVar x v)).
  Proof.
    red; intros.
    unfold compile_assign.
    rewrite denote_list_app.
    do 2 rewrite interp_locals_bind.
    eapply eutt_bind_gen.
    eapply compile_expr_correct; eauto.
    intros.
    repeat untau_left.
    force_left.
    repeat untau_right; force_right.
    eapply eutt_ret; simpl.
    destruct r1, r2.
    erewrite sim_rel_find_tmp_n; eauto; simpl.
    destruct H0.
    split; auto.
    eapply Renv_write_local; eauto.
  Qed.

  Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
      denote_asm (seq_asm ab bc)
    ⩯ denote_asm ab >=> denote_asm bc.
  Proof.
    unfold seq_asm. 
    rewrite link_asm_correct, relabel_asm_correct, app_asm_correct.
    rewrite <- lift_ktree_id, cat_assoc.
    rewrite cat_id_r.
    rewrite sym_ktree_unfold.
    apply cat_from_loop.
    all: typeclasses eauto.
  Qed.

  Lemma if_asm_correct {A} (e : list instr) (tp fp : asm unit A) :
      denote_asm (if_asm e tp fp)
    ⩯ ((fun _ =>
         denote_list e ;;
                     v <- lift (GetVar tmp_if) ;;
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
    - rewrite ret_bind_.
      rewrite (relabel_asm_correct _ _ _ (inr tt)).
      unfold CategoryOps.cat, Cat_ktree, ITree.cat; simpl.
      rewrite bind_bind.
      unfold lift_ktree; rewrite ret_bind_.
      setoid_rewrite (app_asm_correct tp fp (inr tt)).
      setoid_rewrite bind_bind.
      rewrite <- (bind_ret (denote_asm fp tt)) at 2.
      eapply eutt_bind; try reflexivity. intros ?.
      unfold inr_, Inr_ktree, lift_ktree; rewrite ret_bind_; reflexivity.
    - rewrite ret_bind_.
      rewrite (relabel_asm_correct _ _ _ (inl tt)).
      unfold CategoryOps.cat, Cat_ktree, ITree.cat; simpl.
      rewrite bind_bind.
      unfold lift_ktree; rewrite ret_bind_.
      setoid_rewrite (app_asm_correct tp fp (inl tt)).
      setoid_rewrite bind_bind.
      rewrite <- (bind_ret (denote_asm tp tt)) at 2.
      eapply eutt_bind; try reflexivity. intros ?.
      unfold inl_, Inl_ktree, lift_ktree;
        rewrite ret_bind_; reflexivity.
  Qed.

  Lemma while_asm_correct (e : list instr) (p : asm unit unit) :
      denote_asm (while_asm e p)
    ⩯ loop (fun l : unit + unit =>
         match l with
         | inl tt =>
           denote_list e ;;
           v <- ITree.lift (inl1 (GetVar tmp_if)) ;;
           if v : value then
             Ret (inr tt)
           else
             (denote_asm p tt;; Ret (inl tt))
         | inr tt => Ret (inl tt)
         end).
  Proof.
    unfold while_asm.
    rewrite link_asm_correct.
    (* TODO: this is a hack it should just be
     apply eq_ktree_loop. *)
    match goal with
    | [ |- _ (loop ?x) (loop ?y) ] => apply (eq_ktree_loop x y)
    end.
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
        repeat rewrite ret_bind_.
        reflexivity.
      + rewrite (relabel_asm_correct _ _ _  tt).
        unfold CategoryOps.cat, Cat_ktree, ITree.cat.
        simpl; repeat setoid_rewrite bind_bind.
        unfold inl_, Inl_ktree, lift_ktree; rewrite ret_bind_.
        apply eutt_bind; try reflexivity. intros [].
        repeat rewrite ret_bind_; reflexivity.
    - rewrite itree_eta; cbn; reflexivity.
  Qed.

  Lemma while_is_loop {E} (body : itree E bool) :
    while body
          ≈ loop (fun l : unit + unit =>
                    match l with
                    | inl _ => ITree.map (fun b => if b : bool then inl tt else inr tt)
                                        body
                    | inr _ => Ret (inl tt)   (* Enter loop *)
                    end) tt.
  Proof.
    unfold while.
    (* another hack, should be [apply eutt_loop]. *)
    match goal with
    | [ |- _ (loop ?x _) (loop ?y _) ] =>
    apply (eutt_loop x y)
    end;
      [intros [[]|[]]; simpl |]; try reflexivity.
    unfold ITree.map.
    apply eutt_bind; try reflexivity.
    intros []; reflexivity.
  Qed.

  Definition env_lookupDefault_is_lift {K V : Type} {E: Type -> Type} `{envE K V -< E} (x: K) (v: V):
    env_lookupDefault x v = lift (lookupDefaultE x v).
  Proof.
    reflexivity.
  Qed.

  Lemma sim_rel_get_tmp0:
    forall g_asm0 g_asm g_imp v,
      sim_rel g_asm0 0 (g_asm,tt) (g_imp,v) ->
      interp_locals (lift (GetVar (%0))) g_asm ≈ Ret (g_asm,v).
  Proof.
    intros.
    destruct H as [_ [eq _]].
    unfold interp_locals.
    unfold lift.
    rewrite interp_lift.
    rewrite tau_eutt.
    cbn.
    unfold run_env.
    unfold evalLocals, CategoryOps.cat, Cat_Handler.
    rewrite env_lookupDefault_is_lift.
    unfold lift.
    rewrite unfold_interp_state; cbn.
    rewrite tau_eutt.
    rewrite map_bind.
    setoid_rewrite ret_interp.
    setoid_rewrite bind_ret.
    unfold inl_, Inl_sum1_Handler, eh_lift.
    rewrite interp_state_lift.
    rewrite bind_ret.
    cbn.
    rewrite eq.
    rewrite !tau_eutt.
    reflexivity.
  Qed.

  Lemma compile_correct (s : stmt) :
    eq_locals eq Renv
              (denote_asm (compile s) tt)
              (denoteStmt s).
  Proof.
    induction s.

    - (* Assign *)
      simpl.
      rewrite raw_asm_block_correct.
      rewrite after_correct.
      rewrite <- (bind_ret (ITree.bind (denoteExpr e) _)).
      eapply eq_locals_bind_gen.
      { eapply compile_assign_correct; auto. }
      intros [] [] []. simpl.
      repeat intro.
      rewrite itree_eta, (itree_eta (_ _ g2)); cbn.
      apply eutt_ret; auto.

    - (* Seq *)
      rewrite fold_to_itree; simpl.
      rewrite seq_asm_correct. unfold to_itree.
      unfold ITree.cat.
      eapply eq_locals_bind_gen.
      { eauto. }
      intros [] [] []; auto.

    - (* If *)
      repeat intro.
      rewrite fold_to_itree. simpl.
      rewrite if_asm_correct.
      unfold to_itree.
      rewrite 2 interp_locals_bind.
      eapply eutt_bind_gen.
      { apply compile_expr_correct; auto. }
      intros.
      destruct r2 as [g_imp' v]; simpl.
      rewrite interp_locals_bind.
      destruct r1 as [g_asm' []].
      generalize H0; intros EQ. apply sim_rel_get_tmp0 in EQ.
      setoid_rewrite EQ; clear EQ.
      rewrite ret_bind_.
      simpl.
      apply sim_rel_Renv in H0.
      destruct v; simpl; auto. 

    - (* While *)
      simpl; rewrite fold_to_itree.
      rewrite while_asm_correct.
      rewrite while_is_loop.
      unfold to_itree.
      (* TODO: [apply eq_locals_loop] *)
      match goal with
      | [ |- _ (loop ?x _) (loop ?y _) ] =>
        apply (eq_locals_loop _ x y)
      end.
      intros [[]|[]].
      2:{ repeat intro.
          rewrite itree_eta, (itree_eta (_ _ g2)); cbn.
          apply eutt_ret; auto. }
      unfold ITree.map. rewrite bind_bind.

      repeat intro.
      rewrite 2 interp_locals_bind.
      eapply eutt_bind_gen.
      { apply compile_expr_correct; auto. }
      intros.
      destruct r2 as [g_imp' v]; simpl.
      rewrite interp_locals_bind.
      destruct r1 as [g_asm' []].
      generalize H0; intros EQ. apply sim_rel_get_tmp0 in EQ.
      rewrite interp_locals_bind.
      setoid_rewrite EQ; clear EQ.
      rewrite ret_bind_.
      simpl.
      apply sim_rel_Renv in H0.
      destruct v; simpl; auto.
      + rewrite itree_eta, (itree_eta (_ >>= _)); cbn.
        apply eutt_ret. auto.
      + rewrite 2 interp_locals_bind, bind_bind.
        eapply eutt_bind_gen.
        { eapply IHs; auto. }
        intros.
        rewrite itree_eta, (itree_eta (_ >>= _)); cbn.
        apply eutt_ret. destruct H1; auto.

    - (* Skip *)
      repeat intro.
      rewrite (itree_eta (_ (denote_asm _ _) _)),
      (itree_eta (_ (denoteStmt _) _));
        cbn.
      apply eutt_ret; auto.
  Qed.

End Correctness.
