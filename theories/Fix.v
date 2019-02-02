(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     paco2_upto Core Morphisms MorphismsFacts OpenSum Eq.Eq Eq.UpToTaus.

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
        eutt (mfix body x) (body E (fun t => id) (mfix body) x).

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

      Definition homFix_match {T} (homFix: itree (sum1 E fixpoint) T -> itree E T) oc : itree E T :=
        match oc with
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

      Local CoFixpoint homFix {T : Type}
            (c : itree (sum1 E fixpoint) T)
      : itree E T :=
        homFix_match homFix (observe c).

      Definition _mfix x := homFix (f x).

      Definition eval_fixpoint T (X : sum1 E fixpoint T) : itree E T :=
        match X with
        | inlE e => ITree.liftE e
        | inrE f0 =>
          match f0 with
          | call x => _mfix x
          end
        end.

      Lemma homfix_unfold {T} (t: itree _ T) :
        observe (homFix t) = observe (homFix_match homFix (observe t)).
      Proof. cbn. eauto. Qed.

      Lemma unfold_homfix {T} (t: itree _ T) :
        homFix t ≅ homFix_match homFix (observe t).
      Proof. rewrite itree_eta, homfix_unfold, <-itree_eta. reflexivity. Qed.

      Lemma ret_homfix {T} (x: T) :
        homFix (Ret x) ≅ Ret x.
      Proof. rewrite unfold_homfix. reflexivity. Qed.

      Lemma tau_homfix {T} (t: itree _ T) :
        homFix (Tau t) ≅ Tau (homFix t).
      Proof. rewrite unfold_homfix. reflexivity. Qed.

      Lemma vis_homfix_left {T U} (e: _ U) (k: U -> itree _ T) :
        homFix (Vis (inlE e) k) ≅ Vis e (fun x => homFix (k x)).
      Proof. rewrite unfold_homfix. reflexivity. Qed.

      Lemma vis_homfix_right {T} x (k: _ -> itree _ T) :
        homFix (Vis (inrE (call x)) k) ≅ Tau (homFix (ITree.bind (f x) k)).
      Proof. rewrite unfold_homfix. reflexivity. Qed.

      Instance eq_itree_homfix {T} :
        Proper (@eq_itree _ T ==>
                @eq_itree _ T) (@homFix T).
      Proof.
        repeat intro. pupto2_init. revert_until T.
        pcofix CIH. intros.
        rewrite (itree_eta (homFix x)), (itree_eta (homFix y)). pupto2_final.
        rewrite !homfix_unfold.
        punfold H0. inv H0; pclearbot; [| |destruct e; [|destruct f0]].
        - eapply eq_itree_refl.
        - pfold. econstructor. eauto.
        - pfold. econstructor. eauto 7.
        - pfold. econstructor. apply pointwise_relation_fold in REL.
          right. eapply CIH. rewrite REL. reflexivity.
      Qed.

      Theorem homfix_bind {U T}: forall t k,
          @homFix T (ITree.bind t k) ≅ ITree.bind (@homFix U t) (fun x => homFix (k x)).
      Proof.
        intros. pupto2_init. revert t k.
        pcofix CIH. intros.
        rewrite (itree_eta t). destruct (observe t); [| |destruct e; [|destruct f0]].
        - rewrite ret_bind, !ret_homfix, ret_bind. pupto2_final. apply eq_itree_refl.
        - rewrite tau_bind, !tau_homfix, tau_bind. pupto2_final.
          pfold. econstructor. eauto.
        - rewrite vis_bind, !vis_homfix_left, vis_bind. pupto2_final.
          pfold. econstructor. eauto.
        - rewrite vis_bind, !vis_homfix_right, tau_bind, <-bind_bind. pupto2_final.
          pfold. econstructor. eauto.
      Qed.

      Lemma homfix_interp_finite : forall {T} (c : itree _ T),
          finite_taus (observe (homFix c)) <-> finite_taus (observe (interp eval_fixpoint c)).
      Proof.
        split; intros.
        { destruct H as [n [t FIN]]. move n before f. revert_until n.
          generalize (PeanoNat.Nat.lt_succ_diag_r n); generalize (S n) at 1; intro m; revert n.
          induction m; intros; [nia|].
          rewrite interp_unfold.
          genobs c oc. destruct oc; [| |destruct e; [|destruct f0]]; simpl.
          - eauto using finite_taus_ret.
          - rewrite homfix_unfold in FIN. simpobs. cbn in FIN.
            eapply finite_taus_tau; eauto.
            destruct n; [inv FIN; contradiction|].
            eapply unalltaus_tau in FIN; cycle 1; eauto with arith.
          - cbn. eauto using finite_taus_vis.
          - rewrite homfix_unfold in FIN. simpobs. simpl in FIN.
            destruct n; [inv FIN; contradiction|].
            eapply unalltaus_tau in FIN; cycle 1; eauto. simpl in FIN.
            eapply eq_unalltaus in FIN; [|apply homfix_bind].
            destruct FIN as [s' FIN].
            hexploit @finite_taus_bind_fst; eauto. intros [n' [t' TAUS']].
            hexploit untaus_bind; eauto. intros UTAUS.
            genobs t' ot'. destruct ot'; swap 1 3.
            + do 2 eexists. eapply untaus_all; [apply UTAUS|].
              rewrite !bind_unfold. simpobs. simpl. auto.
            + eapply unalltaus_notau in TAUS'. exfalso; eauto.
            + hexploit untaus_bind.
              { instantiate (1:= go _). simpl. apply TAUS'. } intros UTAUS'.
              hexploit untaus_unalltus_rev; [apply UTAUS' | apply FIN|]. intros UTAUS''.
              rewrite bind_unfold in UTAUS''. simpl in UTAUS''.
              eapply IHm in UTAUS''; try nia.
              eapply untaus_finite_taus; eauto.
              rewrite bind_unfold. simpobs. cbn.
              eapply finite_taus_tau; eauto.
        }
        { destruct H as [n [t FIN]]. move n before f. revert_until n.
          generalize (PeanoNat.Nat.lt_succ_diag_r n); generalize (S n) at 1; intro m; revert n.
          induction m; intros; [nia|].
          rewrite homfix_unfold.
          genobs c oc. destruct oc; [| |destruct e; [|destruct f0]]; cbn; simpobs; simpl.
          - eauto using finite_taus_ret.
          - rewrite interp_unfold in FIN. simpobs. cbn in FIN.
            eapply finite_taus_tau; eauto.
            destruct n; [inv FIN; contradiction|].
            eapply unalltaus_tau in FIN; cycle 1; eauto with arith.
          - eauto using finite_taus_vis.
          - rewrite interp_unfold in FIN. simpobs. simpl in FIN.
            eapply finite_taus_tau; eauto.
            rewrite homfix_bind.
            hexploit @finite_taus_bind_fst; eauto. intros [n' [t' TAUS']].
            hexploit untaus_bind; eauto. intros UTAUS.
            genobs t' ot'. destruct ot'; swap 1 3.
            + do 2 eexists. eapply untaus_all; [apply UTAUS|].
              rewrite !bind_unfold. simpobs. simpl. auto.
            + eapply unalltaus_notau in TAUS'. exfalso; eauto.
            + hexploit untaus_bind.
              { instantiate (1:= go _). simpl. apply TAUS'. } intros UTAUS'.
              hexploit untaus_unalltus_rev; [apply UTAUS' | apply FIN|]. intros UTAUS''.
              rewrite bind_unfold in UTAUS''. simpl in UTAUS''.
              destruct n; [inv UTAUS''; contradiction|].
              eapply unalltaus_tau in UTAUS''; try reflexivity.
              eapply IHm in UTAUS''; try nia.
              eapply untaus_finite_taus; eauto.
              rewrite bind_unfold. simpobs. simpl. eauto.
        }
      Qed.

      Theorem homFix_is_interp : forall {T} (c : itree _ T),
          homFix c ~~ interp eval_fixpoint c.
      Proof.
        intros. pupto2_init. revert c.
        pcofix CIH. intros.
        eapply eutt_strengthen; eauto using homfix_interp_finite.
        intro n. revert c. induction n; intros; try nia.
        rewrite homfix_unfold in UNT1.
        rewrite interp_unfold in UNT2.
        genobs c oc; destruct oc; [| |destruct e; [|destruct f0]]; cbn in UNT1; simpobs.
        - dependent destruction UNT1. dependent destruction UNT2.
          rewrite (itree_eta t1'), (itree_eta t2'). simpobs. simpl.
          pupto2_final. apply eutt_refl.
        - dependent destruction UNT1; try contradiction.
          eapply unalltaus_tau in UNT2; try reflexivity.
          eapply IHn; eauto. nia.
        - dependent destruction UNT1. cbn in UNT2. dependent destruction UNT2.
          rewrite (itree_eta t1'), (itree_eta t2'); simpobs.
          pfold. econstructor; [split; eauto|].
          intros. dependent destruction UNTAUS1. dependent destruction UNTAUS2. simpobs.
          econstructor. intros.
          fold_bind. rewrite ret_bind, tau_eutt; try reflexivity.
          pupto2_final. eauto.
        - simpl in UNT2. dependent destruction UNT1; try contradiction.
          hexploit @eq_unalltaus_eq; [apply UNT1 | apply homfix_bind |]. intros [s' [UNT' EQV']].
          rewrite EQV'.
          hexploit @finite_taus_bind_fst; eauto. intros [n3 [t3 TAUS3]].
          hexploit @unalltaus_notau; eauto. intros NOTAU.
          hexploit untaus_bind; eauto. intros TAUS4.
          hexploit untaus_bind; try apply TAUS3. intros TAUS5.
          setoid_rewrite bind_unfold in TAUS4 at 2.
          setoid_rewrite bind_unfold in TAUS5 at 2.
          genobs t3 ot3; destruct ot3; try contradiction; cycle 1; fold_bind.
          + eapply untaus_all in TAUS4; eauto.
            eapply untaus_all in TAUS5; eauto.
            hexploit @unalltaus_injective; [apply TAUS4 | apply UNT' |]. intros OBS1.
            hexploit @unalltaus_injective; [apply TAUS5 | apply UNT2 |]. intros OBS2.
            simpl in OBS1, OBS2. fold_bind.
            rewrite (itree_eta s'), (itree_eta t2'). simpobs.
            setoid_rewrite tau_eutt.
            pfold. econstructor; [split; eauto|].
            intros. dependent destruction UNTAUS1. dependent destruction UNTAUS2. simpobs.
            econstructor. intros.
            pupto2 (eutt_clo_bind E T). econstructor; [reflexivity|].
            intros. pupto2_final. eauto.
          + hexploit @untaus_unalltus_rev; try apply TAUS4; eauto. intros TAUS6.
            hexploit @untaus_unalltus_rev; try apply TAUS5; eauto. intros TAUS7.
            eapply unalltaus_tau in TAUS7; [|reflexivity].
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
                (fun t => interp (fun _ e => lift e))
                (fun x0 : dom => ITree.liftE (inrE (call x0)))).

      Theorem mfix_unfold : forall x,
          eutt (mfix x) (body E (fun t => id) mfix x).
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
