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
      Variable f : forall x : dom, itree (sum1 fixpoint E) (codom x).

      Definition homFix_match {T} (homFix: itree (sum1 fixpoint E) T -> itree E T) oc : itree E T :=
        match oc with
        | RetF x => Ret x
        | @VisF _ _ _ u ee k =>
          match ee with
          | inlE e =>
            match e in fixpoint u return (u -> _) -> _ with
            | call x => fun k =>
              Tau (homFix (ITree.bind (f x) k))
            end k
          | inrE e' =>
            Vis e' (fun x => homFix (k x))
          end
        | TauF x => Tau (homFix x)
        end.

      Local CoFixpoint homFix {T : Type}
            (c : itree (sum1 fixpoint E) T)
      : itree E T :=
        homFix_match homFix (observe c).

      Definition _mfix x := homFix (f x).

      Definition eval_fixpoint T (e_fix : fixpoint T) : itree E T :=
        match e_fix with
        | call x => _mfix x
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
        homFix (Vis (inrE e) k) ≅ Vis e (fun x => homFix (k x)).
      Proof. rewrite unfold_homfix. reflexivity. Qed.

      Lemma vis_homfix_right {T} x (k: _ -> itree _ T) :
        homFix (Vis (inlE (call x)) k) ≅ Tau (homFix (ITree.bind (f x) k)).
      Proof. rewrite unfold_homfix. reflexivity. Qed.

      Instance eq_itree_homfix {T} :
        Proper (@eq_itree _ T ==>
                @eq_itree _ T) (@homFix T).
      Proof.
        repeat intro. pupto2_init. revert_until T.
        pcofix CIH. intros.
        rewrite (itree_eta (homFix x)), (itree_eta (homFix y)). pupto2_final.
        rewrite !homfix_unfold.
        punfold H0. inv H0; pclearbot; [| |destruct e; [destruct f0|]].
        - eapply eq_itree_refl.
        - pfold. econstructor. eauto.
        - pfold. econstructor. apply pointwise_relation_fold in REL.
          right. eapply CIH. rewrite REL. reflexivity.
        - pfold. econstructor. eauto 7.
      Qed.

      Theorem homfix_bind {U T}: forall t k,
          @homFix T (ITree.bind t k) ≅ ITree.bind (@homFix U t) (fun x => homFix (k x)).
      Proof.
        intros. pupto2_init. revert t k.
        pcofix CIH. intros.
        rewrite (itree_eta t). destruct (observe t); [| |destruct e; [destruct f0|]].
        - rewrite ret_bind, !ret_homfix, ret_bind. pupto2_final. apply eq_itree_refl.
        - rewrite tau_bind, !tau_homfix, tau_bind. pupto2_final.
          pfold. econstructor. eauto.
        - rewrite vis_bind, !vis_homfix_right, tau_bind, <-bind_bind. pupto2_final.
          pfold. econstructor. eauto.
        - rewrite vis_bind, !vis_homfix_left, vis_bind. pupto2_final.
          pfold. econstructor. eauto.
      Qed.

      Inductive homFix_invariant {U} (c1 c2 : itree _ U) : Prop :=
      | homFix_main (d1 d2 : _ U)
                    (Ed : eq_itree d1 d2)
                    (Ec1 : eq_itree c1 (homFix d1))
                    (Ec2 : eq_itree c2 (interp1 eval_fixpoint d2)) :
          homFix_invariant c1 c2
      | homFix_interp1 T (d : _ T) k1 k2
          (Ek : forall x, eq_itree (k1 x) (k2 x))
          (Ec1 : eq_itree c1 (homFix (d >>= k1)))
          (Ec2 : eq_itree c2 (homFix d >>= fun x => interp1 eval_fixpoint (k2 x))) :
          homFix_invariant c1 c2
      .

      Lemma homFix_invariant_init {U} (r : relation _)
            (INV : forall t1 t2, homFix_invariant t1 t2 -> r t1 t2)
            (c1 c2 : itree _ U)
            (Ec : eq_itree c1 c2) :
        paco2 (compose eq_itreeF (gres2 eq_itreeF)) r
              (homFix c1)
              (interp1 eval_fixpoint c2).
      Proof.
        pupto2 (eq_itree_clo_trans E U); econstructor.
        eapply unfold_homfix.
        eapply unfold_interp1.
        punfold Ec.
        inversion Ec; cbn.
        + pupto2_final. eapply eq_itree_refl. (* This should be reflexivity. *)
        + destruct REL as [ | [] ].
          pfold; constructor. pupto2_final. right; apply INV.
          eapply homFix_main; [ eapply H1 | |]; reflexivity.
        + destruct e. cbn. unfold ITree.liftE.
          { destruct f0.
            pupto2_final; pfold; constructor; cbn; right. unfold _mfix.
            apply INV. eapply homFix_interp1.
            - reflexivity.
            - cbn. reflexivity.
            - cbn. (* Proper lemmas needed *) admit.
          }
          { pupto2 (eq_itree_clo_trans E U); econstructor.
            * reflexivity.
            * reflexivity.
            * pfold; constructor; intros x.
              destruct (REL x) as [ | []].
              pupto2 (eq_itree_clo_trans E U); econstructor.
              { reflexivity. }
              { reflexivity. }
              pupto2_final. right.
              apply INV.
              eapply homFix_main; [ eassumption | | ]; reflexivity.
          }
      Admitted.

      Lemma homfix_interp_itree {U} (c1 c2 : itree _ U) :
          homFix_invariant c1 c2 -> eq_itree c1 c2.
      Proof.
        intro H; pupto2_init; revert c1 c2 H. pcofix self.
        intros c1 c2 [d1 d2 Ed Ec1 Ec2 | T d k1 k2 Ek Ec1 Ec2].
        - pupto2 (eq_itree_clo_trans E U). econstructor.
          + apply Ec1. + apply Ec2.
          + apply homFix_invariant_init; auto.
        - pupto2 (eq_itree_clo_trans E U). econstructor.
          { apply Ec1. } { apply Ec2. }
          clear Ec1 Ec2.
          cbn.
          rewrite unfold_homfix. rewrite (unfold_bind (homFix d)).
          unfold observe, _observe; cbn.
          destruct (observe d); fold_observe; cbn.
          + rewrite <- unfold_homfix.
            apply homFix_invariant_init; auto.
          + pupto2_final; pfold; constructor; right.
            apply self.
            eapply homFix_interp1.
            * eapply Ek.
            * cbn; unfold ITree.bind; reflexivity.
            * cbn; unfold ITree.bind; reflexivity.
          + destruct e; cbn.
            * destruct f0; cbn.
              pfold; constructor.
              pupto2 (eq_itree_clo_trans E U). econstructor.
              ++ pose proof @bind_bind as bb.
                 unfold ITree.bind in bb.
                 unfold ITree.bind.
                 rewrite <- bb; clear bb.
                 reflexivity.
              ++ reflexivity.
              ++ pupto2_final; right.
                 apply self.
                 eapply homFix_interp1.
                 ** apply Ek.
                 ** cbn; unfold ITree.bind; reflexivity.
                 ** cbn; unfold ITree.bind; reflexivity.
            * pupto2_final; pfold; constructor; right.
              apply self.
              eapply homFix_interp1.
              ++ eapply Ek.
              ++ cbn; unfold ITree.bind; reflexivity.
              ++ cbn; unfold ITree.bind; reflexivity.
      Qed.

      Theorem homFix_is_interp : forall {T} (c : itree _ T),
          eq_itree (homFix c) (interp1 eval_fixpoint c).
      Proof.
        intros.
        apply homfix_interp_itree.
        eapply homFix_main; reflexivity.
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
          (body (fixpoint +' E)
                (fun t => interp (fun _ e => lift e))
                (fun x0 : dom => ITree.liftE (inlE (call x0)))).

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
