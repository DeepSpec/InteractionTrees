(** Properties of [Fix.mrec] and [Fix.rec]. *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics
     Core
     Morphisms
     MorphismsFacts
     Fix
     Effect.Sum
     Eq.Eq Eq.UpToTaus.

Section Facts.

Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

(** Unfolding of [interp_mrec]. *)
Definition interp_mrecF R :
  itreeF (D +' E) R _ -> itree E R :=
  handleF1 (interp_mrec ctx R)
           (fun _ d k => Tau (interp_mrec ctx _ (ctx _ d >>= k))).

Lemma unfold_interp_mrecF R (t : itree (D +' E) R) :
  observe (interp_mrec ctx _ t) = observe (interp_mrecF _ (observe t)).
Proof. reflexivity. Qed.

Lemma unfold_interp_mrec R (t : itree (D +' E) R) :
  eq_itree eq
           (interp_mrec ctx _ t)
           (interp_mrecF _ (observe t)).
Proof.
  rewrite itree_eta, unfold_interp_mrecF, <-itree_eta.
  reflexivity.
Qed.

Lemma ret_mrec {T} (x: T) :
  interp_mrec ctx _ (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp_mrec; reflexivity. Qed.

Lemma tau_mrec {T} (t: itree _ T) :
  interp_mrec ctx _ (Tau t) ≅ Tau (interp_mrec ctx _ t).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_right {T U} (e : E U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx _ (Vis (inr1 e) k) ≅
  Vis e (fun x => interp_mrec ctx _ (k x)).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_left {T U} (d : D U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx _ (Vis (inl1 d) k) ≅
  Tau (interp_mrec ctx _ (ITree.bind (ctx _ d) k)).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Hint Rewrite @ret_mrec : itree.
Hint Rewrite @vis_mrec_left : itree.
Hint Rewrite @vis_mrec_right : itree.
Hint Rewrite @tau_mrec : itree.

Instance eq_itree_mrec {R} :
  Proper (eq_itree eq ==> eq_itree eq) (interp_mrec ctx R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  pupto2_final.
  punfold H0. inv H0; pclearbot; [| |destruct e].
  - apply reflexivity.
  - pfold. econstructor. eauto.
  - pfold. econstructor. apply pointwise_relation_fold in REL.
    right. eapply CIH. rewrite REL. reflexivity.
  - pfold. econstructor. eauto 7.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx _ (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx _ t) (fun x => interp_mrec ctx _ (k x)).
Proof.
  intros. pupto2_init. revert t k.
  pcofix CIH. intros.
  rewrite (itree_eta t).
  destruct (observe t);
    [| |destruct e];
    autorewrite with itree;
    try rewrite <- bind_bind;
    pupto2_final.
  1: { apply reflexivity. }
  all: try (pfold; econstructor; eauto).
Qed.

Let h_mrec : D ~> itree E := mrec ctx.

Inductive mrec_invariant {U} : relation (itree _ U) :=
| mrec_main (d1 d2 : _ U) (Ed : eq_itree eq d1 d2) :
    mrec_invariant (interp_mrec ctx _ d1)
                   (interp1 (mrec ctx) _ d2)
| mrec_bind T (d : _ T) (k1 k2 : T -> itree _ U)
    (Ek : forall x, eq_itree eq (k1 x) (k2 x)) :
    mrec_invariant (interp_mrec ctx _ (d >>= k1))
                   (interp_mrec ctx _ d >>= fun x =>
                        interp1 h_mrec _ (k2 x))
.

Notation mi_holds r :=
  (forall c1 c2 d1 d2,
      mrec_invariant d1 d2 ->
      eq_itree eq c1 d1 -> eq_itree eq c2 d2 -> r c1 c2).

Lemma mrec_invariant_init {U} (r : relation (itree _ U))
      (INV : mi_holds r)
      (c1 c2 : itree _ U)
      (Ec : eq_itree eq c1 c2) :
  paco2 (compose (eq_itree_ eq) (gres2 (eq_itree_ eq))) r
        (interp_mrec ctx _ c1)
        (interp1 h_mrec _ c2).
Proof.
  rewrite unfold_interp_mrec, unfold_interp1.
  punfold Ec.
  inversion Ec; cbn; pclearbot; pupto2_final.
  + subst; apply reflexivity.
  + pfold; constructor. right; eapply INV.
    1: apply mrec_main; eassumption.
    all: reflexivity.
  + destruct e.
    { pfold; constructor; cbn; right. eapply INV.
      1: apply mrec_bind; eassumption.
      all: cbn; reflexivity.
    }
    { pfold; econstructor.
      intros; right. eapply INV.
      1: apply mrec_main; eapply REL.
      all: reflexivity.
    }
Qed.

Lemma mrec_invariant_eq {U} : mi_holds (@eq_itree _ U _ eq).
Proof.
  intros d1 d2 c1 c2 Ec1 Ec2 H.
  pupto2_init; revert d1 d2 c1 c2 Ec1 Ec2 H; pcofix self.
  intros _d1 _d2 c1 c2 [d1 d2 Ed | T d k1 k2 Ek] Ec1 Ec2.
  - rewrite Ec1, Ec2.
    apply mrec_invariant_init; auto 10.
  - rewrite Ec1, Ec2. cbn.
    rewrite unfold_interp_mrec.
    rewrite (unfold_bind (interp_mrec _ _ d)).
    unfold observe, _observe; cbn.
    destruct (observe d); fold_observe; cbn.
    + rewrite <- unfold_interp_mrec.
      apply mrec_invariant_init; auto.
    + pupto2_final; pfold; constructor; right.
      eapply self.
      1: apply mrec_bind; eassumption.
      all: cbn; fold_bind; reflexivity.
    + destruct e; cbn.
      * fold_bind. rewrite <-bind_bind.
        pupto2_final. pfold. econstructor. right.
        eapply self.
        1: apply mrec_bind; eassumption.
        all: cbn; reflexivity.
      * pupto2_final; pfold; constructor; right.
        eapply self.
        1: apply mrec_bind; eassumption.
        all: cbn; fold_bind; reflexivity.
Qed.

Theorem interp_mrec_is_interp : forall {T} (c : itree _ T),
    eq_itree eq (interp_mrec ctx _ c) (interp1 h_mrec _ c).
Proof.
  intros; eapply mrec_invariant_eq;
    try eapply mrec_main; reflexivity.
Qed.

End Facts.

Lemma rec_unfold {E A B} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec f x ≈ interp (fun _ e => match e with
                               | inl1 e => calling' (rec f) _ e
                               | inr1 e => ITree.liftE e
                               end) _ (f x).
Proof.
  unfold rec. unfold mrec.
  rewrite interp_mrec_is_interp.
  repeat rewrite <- interp_is_interp1.
  unfold interp_match.
  unfold mrec.
  eapply eutt_interp.
  { red. destruct e; try reflexivity.
    destruct c.
    reflexivity. }
  reflexivity.
Qed.

Lemma loop_unfold {E A B} (f : A -> itree E (A + B)) (x : A) :
  loop f x ≈ (ab <- f x ;;
              match ab with
              | inl a => loop f a
              | inr b => Ret b
              end).
Proof.
  unfold loop at 1.
  rewrite rec_unfold.
  rewrite interp_bind.
  rewrite interp_translate.
  rewrite interp_id_liftE.
  eapply eutt_bind; [ reflexivity |].
  intros [a | b].
  - rewrite interp_liftE; cbn.
    reflexivity.
  - rewrite ret_interp.
    reflexivity.
Qed.

Definition sum_map1 {A B C} (f : A -> B) (ac : A + C) : B + C :=
  match ac with
  | inl a => inl (f a)
  | inr c => inr c
  end.

Lemma bind_loop {E A B C} (f : A -> itree E (A + B)) (g : B -> itree E (B + C)) (x : A) :
    (loop f x >>= loop g)
  ≈ loop (fun ab =>
       match ab with
       | inl a => ITree.map inl (f a)
       | inr b => ITree.map (sum_map1 inr) (g b)
       end) (inl x).
Admitted.
