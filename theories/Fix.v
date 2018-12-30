(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)

From ITree Require Import
     paco2_respectful Core Morphisms MorphismsFacts OpenSum Eq.Eq Eq.UpToTaus.

From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

Require Import Paco.paco.

Module Type FixSig.
  Section Fix.
    (* the ambient effects *)
    Context {E : Type -> Type}.

    Context {dom : Type}.
    Variable codom : dom -> Type.

    Definition fix_body : Type :=
      forall E',
        (forall t, itree E t -> itree E' t) ->
        (forall x : dom, itree E' (codom x)) ->
        forall x : dom, itree E' (codom x).

    Parameter mfix : fix_body -> forall x : dom, itree E (codom x).

    Axiom mfix_unfold : forall (body : fix_body) (x : dom),
        mfix body x = body E (fun t => id) (mfix body) x.

  End Fix.
End FixSig.

Module FixImpl <: FixSig.
  Section Fix.
    (* the ambient effects *)
    Variable E : Type -> Type.

    Variable dom : Type.
    Variable codom : dom -> Type.

    (* the fixpoint effect, used for representing recursive calls *)
    Variant fixpoint : Type -> Type :=
    | call : forall x : dom, fixpoint (codom x).

    Section mfix.
      (* this is the body of the fixpoint. *)
      Variable f : forall x : dom, itree (sum1 E fixpoint) (codom x).

      Local CoFixpoint homFix {T : Type}
            (c : itree (sum1 E fixpoint) T)
      : itree E T :=
        match c.(observe) with
        | RetF x => Ret x
        | @VisF _ _ _ u ee k =>
          match ee with
          | inlE e' =>
            Vis e' (fun x => homFix (k x))
          | inrE e =>
            match e in fixpoint u return (u -> _) -> _ with
            | call x => fun k =>
              Tau (homFix (ITree.bind (f x) k))
            end k
          end
        | TauF x => Tau (homFix x)
        end.

      Definition _mfix (x : dom) : itree E (codom x) :=
        homFix (f x).

      Definition eval_fixpoint T (X : sum1 E fixpoint T) : itree E T :=
        match X with
        | inlE e => ITree.liftE e
        | inrE f0 =>
          match f0 with
          | call x => _mfix x
          end
        end.
      
      Instance eq_itree_homfix {T} :
        Proper (@eq_itree _ T ==>
                @eq_itree _ T) (@homFix T).
      Proof.
        pcofix CIH. intros.
        rewrite (itree_eta (homFix x)), (itree_eta (homFix y)).
        pfold. punfold H0. absobs x ox. absobs y oy.
        inv H0; pclearbot; [| |destruct e; [|destruct f0]]; cbn; eauto.
        - econstructor. intros. specialize (REL v). pclearbot. eauto.
        - econstructor. right. eapply CIH.
          eapply eq_itree_bind.
          + reflexivity.
          + intro. specialize (REL a). pclearbot. eauto.
      Qed.

      Theorem homfix_bind {U T}: forall t k,
          @homFix T (ITree.bind t k) ≅ ITree.bind (@homFix U t) (fun x => homFix (k x)).
      Proof.
        intros. pupto2_init. revert t k.
        pcofix CIH. intros.
        absobs t ot. destruct ot.
        - rewrite (itree_eta (homFix (Ret _))). cbn. rewrite !ret_bind.
          pupto2_final.
          eapply paco2_mon; [apply Reflexive_eq_itree | contradiction].
        - rewrite tau_bind. repeat (rewrite (itree_eta (homFix (Tau _))); cbn). rewrite tau_bind.
          pupto2_final. pfold. cbn. eauto.
        - rewrite vis_bind; repeat (rewrite (itree_eta (homFix (Vis _ _))); cbn).
          destruct e; [|destruct f0]; cbn.
          + pupto2_final. rewrite vis_bind. pfold. cbn. eauto.
          + rewrite tau_bind.
            pupto2 (eq_itree_clo_trans E T). econstructor; [|reflexivity|].
            { eapply eq_itree_tau, eq_itree_homfix. rewrite <-bind_bind. reflexivity. }
            pupto2_final. pfold. cbn. eauto.
      Qed.

      Lemma homfix_interp_finite : forall {T} (c : itree _ T),
          finite_taus (homFix c) <-> finite_taus (interp eval_fixpoint c).
      Proof.
        split; intros.
        { destruct H as [n [t FIN]]. move n before f. revert_until n.
          generalize (PeanoNat.Nat.lt_succ_diag_r n); generalize (S n) at 1; intro m; revert n.
          induction m; intros; [nia|].
          rewrite (itree_eta (homFix c)) in FIN.
          absobs c oc. destruct oc; [| |destruct e; [|destruct f0]]
          ; simpl; try (inversion FIN; subst; try contradiction; eauto; fail).
          - rewrite tau_interp.
            eapply finite_taus_tau. simpl in FIN. inv FIN; try contradiction.
            eauto with arith.
          - rewrite vis_interp. simpl.
            cbn in FIN. inv FIN; try contradiction.
            hexploit @eq_unalltaus; try apply TAUS; eauto using homfix_bind. intros [t2 TAUS2].
            hexploit @finite_taus_bind_fst; eauto. intros [n3 [t3 TAUS3]].
            hexploit @untaus_prop; eauto. intros NOTAU.
            hexploit untaus_bind; eauto. intros TAUS4.
            hexploit untaus_bind; try apply TAUS3. intros TAUS5.
            absobs t3 ot3; destruct ot3; try contradiction; cycle 1.
            + do 2 eexists. eapply untaus_change_prop; eauto.
            + rewrite ret_bind in TAUS4, TAUS5.
              hexploit @untaus_unalltus_rev; try apply TAUS4; eauto. intros TAUS6.
              eapply IHm in TAUS6; try nia.
              eapply untaus_finite_taus; eauto.
              eapply finite_taus_tau; eauto.
        }
        { destruct H as [n [t FIN]]. move n before f. revert_until n.
          generalize (PeanoNat.Nat.lt_succ_diag_r n); generalize (S n) at 1; intro m; revert n.
          induction m; intros; [nia|].
          rewrite (itree_eta (homFix _)).
          absobs c oc; destruct oc; [| |destruct e; [|destruct f0]]
          ; try (inversion FIN; subst; cbn; try contradiction; eauto; fail).
          - rewrite tau_interp in FIN. cbn. eapply finite_taus_tau.
            inversion FIN; subst; try contradiction; cbn; eauto with arith.
          - rewrite vis_interp in FIN. cbn. eapply finite_taus_tau.
            eapply @finite_taus_eutt; [rewrite homfix_bind; reflexivity|].
            simpl in FIN.
            hexploit @finite_taus_bind_fst; eauto. intros [n3 [t3 TAUS3]].
            hexploit @untaus_prop; eauto. intros NOTAU.
            hexploit untaus_bind; eauto. intros TAUS4.
            hexploit untaus_bind; try apply TAUS3. intros TAUS5.
            absobs t3 ot3; destruct ot3; try contradiction; cycle 1.
            + do 2 eexists. eapply untaus_change_prop; eauto.
            + rewrite ret_bind in TAUS4, TAUS5.
              hexploit @untaus_unalltus_rev; try apply TAUS4; eauto. intros TAUS6.
              inversion TAUS6; try contradiction; subst.
              hexploit IHm; eauto; try nia. intros TAUS7.
              eapply untaus_finite_taus; eauto.
        }
      Qed.

      Theorem homFix_is_interp : forall {T} (c : itree _ T),
          homFix c ~~ interp eval_fixpoint c.
      Proof.
        intros. pupto2_init. revert c.
        pcofix CIH. intros.
        eapply eutt_strengthen; eauto using homfix_interp_finite.
        intro n. revert c. induction n; intros; try nia.
        rewrite (itree_eta (homFix _)) in UNT1.
        absobs c oc; destruct oc; [| |destruct e; [|destruct f0]]; cbn in *.
        - inv UNT1. rewrite ret_interp in UNT2. inv UNT2.
          pupto2_final. eapply paco2_mon; [apply Reflexive_eutt | contradiction].
        - inv UNT1; try contradiction.
          rewrite tau_interp in UNT2. apply unalltaus_tau in UNT2.
          eapply IHn; eauto; nia.
        - inv UNT1. rewrite vis_interp in UNT2. setoid_rewrite vis_bind in UNT2. inv UNT2.
          pupto2 (eutt_clo_trans E T). econstructor; [reflexivity| |].
          { eapply eutt_vis. intro v. rewrite ret_bind. apply eutt_tau1. }
          pupto2_final. pfold.
          simpl. econstructor; [split; eauto|].
          intros. inv UNTAUS1. inv UNTAUS2.
          econstructor. intros. eauto.
        - simpl in UNT1. rewrite vis_interp in UNT2. simpl in UNT2.
          inv UNT1; try contradiction.
          hexploit @eq_unalltaus_eq; [eauto | apply homfix_bind | ..]. intros [s' [UNT' EQV']].
          pupto2 (eutt_clo_trans E T). econstructor; [|reflexivity|].
          { rewrite EQV'. reflexivity. }
          hexploit @finite_taus_bind_fst; eauto. intros [n3 [t3 TAUS3]].
          hexploit @untaus_prop; eauto. intros NOTAU.
          hexploit untaus_bind; eauto. intros TAUS4.
          hexploit untaus_bind; try apply TAUS3. intros TAUS5.
          absobs t3 ot3; destruct ot3; try contradiction; cycle 1; cbn in *.
          + rewrite vis_bind in TAUS4. rewrite vis_bind in TAUS5.
            eapply (untaus_change_prop notau) in TAUS4; eauto.
            eapply (untaus_change_prop notau) in TAUS5; eauto.
            hexploit @unalltaus_injective; [apply UNT' | apply TAUS4 |]. intros X; subst.
            hexploit @unalltaus_injective; [apply UNT2 | apply TAUS5 |]. intros X; subst.
            pupto2 (eutt_clo_trans E T). econstructor; [reflexivity| |].
            { eapply eutt_vis. intro v.
              eapply eutt_bind; [reflexivity|].
              intro w. apply eutt_tau1. }
            pfold. econstructor; [split; eauto|].
            intros. inv UNTAUS1. inv UNTAUS2.
            econstructor. intros.
            upto2_low_step (eutt_clo_bind E T). econstructor.
            { reflexivity. }
            intros. upto2_low_final. eauto.
          + rewrite ret_bind in TAUS4, TAUS5.
            hexploit @untaus_unalltus_rev; try apply TAUS4; eauto. intros TAUS6.
            hexploit @untaus_unalltus_rev; try apply TAUS5; eauto. intros TAUS7.
            eapply unalltaus_tau in TAUS7.
            hexploit IHn; eauto; try nia.
      Qed.

    End mfix.

    Section mfixP.
      (* The parametric representation allows us to avoid reasoning about
       * `homFix` and `eval_fixpoint`. They are (essentially) replaced by
       * beta reduction.
       *
       * The downside, is that the type of the body is a little bit more
       * complex, though one could argue that it is a more abstract encoding.
       *)
      Definition fix_body : Type :=
        forall E',
          (forall t, itree E t -> itree E' t) ->
          (forall x : dom, itree E' (codom x)) ->
          forall x : dom, itree E' (codom x).

      Variable body : fix_body.

      Definition mfix
      : forall x : dom, itree E (codom x) :=
        _mfix
          (body (E +' fixpoint)
                (fun t => @interp _ _ (fun _ e => lift e) _)
                (fun x0 : dom => ITree.liftE (inrE (call x0)))).

      Theorem mfix_unfold : forall x,
          mfix x = body E (fun t => id) mfix x.
      Proof. Admitted.
    End mfixP.
  End Fix.

  (* [mfix] with singleton domain. *)
  Section Fix0.
    Variable E : Type -> Type.
    Variable codom : Type.

    Definition fix_body0 : Type :=
      forall E',
        (forall t, itree E t -> itree E' t) ->
        itree E' codom ->
        itree E' codom.

    Definition mfix0 (body : fix_body0) : itree E codom :=
      mfix E unit (fun _ => codom)
           (fun E' lift self (_ : unit) =>
              body E' lift (self tt)) tt.
  End Fix0.

  (* [mfix] with constant codomain. *)
  Section Fix1.
    Variable E : Type -> Type.
    Variable dom : Type.
    Variable codom : Type.

    Definition fix_body1 : Type :=
      forall E',
        (forall t, itree E t -> itree E' t) ->
        (dom -> itree E' codom) ->
        (dom -> itree E' codom).

    Definition mfix1 : fix_body1 -> dom -> itree E codom :=
      mfix E dom (fun _ => codom).
  End Fix1.

End FixImpl.

Export FixImpl.
Arguments mfix {_ _} _ _ _.
Arguments mfix0 {E codom} body.
Arguments mfix1 {E dom codom} body _.
