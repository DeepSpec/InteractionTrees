From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics
     Core
     Effect.Sum
     OpenSum
     Translate
     Morphisms
     Eq.Eq
     Eq.UpToTaus
     TranslateFacts.

Import ITreeNotations.

(** * Morphism equivalence *)
Definition Rhom {A B : Type -> Type} (R : forall t, B t -> B t -> Prop)
           (f g : A ~> B) : Prop :=
  forall X, pointwise_relation (A X) (R X) (f X) (g X).

Definition eh_eq {A B : Type -> Type}
: (A ~> itree B) -> (A ~> itree B) -> Prop :=
  Rhom (fun t => @eq_itree B _ t eq).

Definition eh_eutt {A B : Type -> Type}
: (A ~> itree B) -> (A ~> itree B) -> Prop :=
  Rhom (fun t => @eutt B _ t eq).

Notation "f ≡ g" := (eh_eutt f g) (at level 70).


(** * [interp] *)

(* Proof of
   [interp f (t >>= k) ~ (interp f t >>= fun r => interp f (k r))]

   "By coinduction", case analysis on t:

    - [t = Ret r] or [t = Vis e k] (...)

    - [t = Tau t]:
          interp f (Tau t >>= k)
        = interp f (Tau (t >>= k))
        = Tau (interp f (t >>= k))
        { by "coinductive hypothesis" }
        ~ Tau (interp f t >>= fun ...)
        = Tau (interp f t) >>= fun ...
        = interp f (Tau t) >>= fun ...
        (QED)

 *)

(* Unfolding of [interp]. *)
Definition interp_u {E F} (f : E ~> itree F) R (ot : itreeF E R _)
  : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp f _ t)
  | VisF e k => Tau (f _ e >>= (fun x => interp f _ (k x)))
  end.

Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  interp f _ t ≅ (interp_u f _ (observe t)).
Proof.
  unfold interp. rewrite unfold_aloop'.
  destruct (observe t); cbn.
  - reflexivity.
  - rewrite ret_bind; reflexivity. (* TODO: Incredibly slow *)
  - rewrite map_bind. apply eq_itree_tau. eapply eq_itree_bind.
    reflexivity.
    intros ? _ []; reflexivity.
Qed.

(** ** [interp] and constructors *)

Lemma ret_interp {E F R} {f : E ~> itree F} (x: R):
  interp f _ (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma tau_interp {E F R} {f : E ~> itree F} (t: itree E R):
  eq_itree eq (interp f _ (Tau t)) (Tau (interp f _ t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma vis_interp {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  eq_itree eq (interp f _ (Vis e k)) (Tau (ITree.bind (f _ e) (fun x => interp f _ (k x)))).
Proof. rewrite unfold_interp. reflexivity. Qed.

(** ** [interp] properness *)
Instance eq_itree_interp {E F R}:
  Proper (Rhom (fun _ => eq_itree eq) ==> eq_itree eq ==> eq_itree eq)
         (fun f => @interp E F f R).
Proof.
  intros f g Hfg.
  intros l r Hlr.
  pupto2_init; revert l r Hlr; pcofix CIH.
  rename r into rr; intros l r Hlr.
  rewrite 2 unfold_interp.
  punfold Hlr; red in Hlr.
  destruct Hlr; pclearbot; cbn.
  - pupto2_final. pfold. constructor; auto.
  - pupto2_final. pfold. constructor; auto.
  - pfold; constructor.
    pupto2 @eq_itree_clo_bind. econstructor.
    eapply Hfg.
    intros ? _ [].
    pupto2_final; auto.
Qed.

Global Instance Proper_interp_eq_itree {E F R f}
: Proper (eq_itree eq ==> eq_itree eq) (@interp E F f R).
Proof.
  eapply eq_itree_interp.
  red. reflexivity.
Qed.

(* Note that this allows rewriting of handlers. *)
Definition eutt_interp_gen (E F : Type -> Type) (R : Type) :
  Proper (Rhom (fun _ => eutt eq) ==> eutt eq ==> eutt eq)
         (fun f => @interp E F f R).
Proof.
  repeat intro. pupto2_init. revert_until H. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.

  rewrite !unfold_interp. do 2 punfold H1.
  induction H1; intros; subst; pclearbot; simpl; eauto.
  - pfold; constructor.
    pupto2 eutt_nested_clo_bind.
    econstructor; [apply H|].
    intros; subst. pupto2_final.
    right. eapply CIH'. edestruct EUTTK; pclearbot; eauto.
  - pfold; econstructor. pupto2_final. eauto 7.
  - pfold; constructor. pfold_reverse. rewrite unfold_interp.
    auto.
  - pfold; constructor. pfold_reverse. rewrite unfold_interp. auto.
Qed.

Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt eq ==> eutt eq)
         (@interp E F f R).
Proof.
  apply eutt_interp_gen.
  red; reflexivity.
Qed.

Lemma interp_ret : forall {E F R} x
      (f : E ~> itree F),
   (interp f R (Ret x)) ≅ Ret x.
Proof.
  intros. apply observing_eq_itree_eq.
  constructor. reflexivity.
Qed.

Lemma interp_bind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
   (interp f _ (ITree.bind t k)) ≅ (ITree.bind (interp f _ t) (fun r => interp f _ (k r))).
Proof.
  pupto2_init; revert R t k; pcofix CIH; intros.
  rewrite unfold_bind, (unfold_interp t).
  destruct (observe t); cbn.
  (* TODO: [ret_bind] (0.8s) is much slower than [ret_bind_] (0.02s) *)
  - rewrite ret_bind. pupto2_final. apply reflexivity.
  - rewrite tau_bind, !tau_interp.
    pupto2_final. pfold. econstructor. eauto.
  - rewrite vis_interp, tau_bind. rewrite bind_bind.
    pfold; constructor.
    pupto2 (eq_itree_clo_bind F S). econstructor.
    + reflexivity.
    + intros; subst. pupto2_final. auto.
Qed.

Lemma interp_liftE {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f _ (ITree.liftE e) ≅ Tau (f _ e >>= fun x => Ret x).
Proof.
  unfold ITree.liftE. rewrite vis_interp.
  apply eq_itree_tau.
  setoid_rewrite ret_interp.
  reflexivity.
Qed.


(** ** Composition of [interp] *)

Lemma interp_id_liftE {E R} (t : itree E R) :
  interp (fun _ e => ITree.liftE e) _ t ≈ t.
Proof.
  pupto2_init; revert t; pcofix CIH; intros t.
  pfold. pupto2_init; revert t; pcofix CIH'; intros t.
  rewrite unfold_interp.
  destruct (observe t); cbn; eauto.
  - pfold. constructor. pupto2_final; auto.
  - unfold ITree.liftE. rewrite vis_bind; cbn.
    pfold; constructor; constructor.
    left. rewrite ret_bind.
    auto.
Qed.


Theorem interp_interp {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g _ (interp f _ t)
    ≅ interp (fun _ e => interp g _ (f _ e)) _ t.
Proof.
  intros t.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite ret_interp. pupto2_final. pfold. constructor. reflexivity.
  - rewrite tau_interp. pupto2_final. pfold. constructor. auto.
  - rewrite tau_interp, interp_bind.
    pfold; constructor.
    pupto2 eq_itree_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros ? _ [].
      pupto2_final; auto.
Qed.

(** * [interp_state] *)

Import Monads.

Definition _interp_state {E F S}
           (f : E ~> stateT S (itree F)) R (ot : itreeF E R _)
  : stateT S (itree F) R := fun s =>
  match ot with
  | RetF r => Ret (s, r)
  | TauF t => Tau (interp_state f _ t s)
  | VisF e k => Tau (f _ e s >>= (fun sx => interp_state f _ (k (snd sx)) (fst sx)))
  end.

Lemma unfold_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) t s :
    eq_itree eq
      (interp_state h _ t s)
      (_interp_state h R (observe t) s).
Proof.
  unfold interp_state.
  rewrite unfold_aloop'.
  destruct observe; cbn.
  - reflexivity.
  - rewrite ret_bind_.
    reflexivity.
  - rewrite map_bind. eapply eq_itree_tau.
    eapply eq_itree_bind.
    + reflexivity.
    + intros [] _ []; reflexivity.
Qed.

Instance eq_itree_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq)
         (interp_state h R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros h x y H0 x2 y0 H1.
  rewrite !unfold_interp_state.
  unfold _interp_state.
  punfold H0; red in H0.
  genobs x ox; destruct ox; simpobs; dependent destruction H0; simpobs; pclearbot.
  - pupto2_final. pfold. red. cbn. subst. eauto.
  - pupto2_final. pfold. red. cbn. subst. eauto.
  - subst. pfold; constructor. pupto2 eq_itree_clo_bind. econstructor.
    + reflexivity.
    + intros [] _ []. pupto2_final. auto.
Qed.

Lemma interp_state_ret {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (s : S) (r : R) :
  (interp_state f _ (Ret r) s) ≅ (Ret (s, r)).
Proof.
  rewrite itree_eta. reflexivity.
Qed.

Lemma interp_state_vis {E F:Type -> Type} {S T U : Type} (s:S) e k
      (h : E ~> Monads.stateT S (itree F)) :
    interp_state h U (Vis e k) s
  ≅ Tau (h T e s >>= fun sx => interp_state h _ (k (snd sx)) (fst sx)).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_tau {E F:Type -> Type} S {T : Type} (t:itree E T) (s:S)
      (h : E ~> Monads.stateT S (itree F)) :
    interp_state h _ (Tau t) s ≅ Tau (interp_state h _ t s).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_liftE {E F : Type -> Type} {R S : Type}
      (f : E ~> Monads.stateT S (itree F))
      (s : S) (e : E R) :
  (interp_state f _ (ITree.liftE e) s) ≅ Tau (f _ e s >>= fun i => Ret i).
Proof.
  unfold ITree.liftE. rewrite interp_state_vis.
  apply eq_itree_tau.
  eapply eq_itree_bind.
  - reflexivity.
  - intros [] _ []; rewrite interp_state_ret. reflexivity.
Qed.

Lemma interp_state_bind {E F : Type -> Type} {A B S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (t : itree E A) (k : A -> itree E B)
      (s : S) :
  (interp_state f _ (t >>= k) s)
    ≅
  (interp_state f _ t s >>= fun st => interp_state f _ (k (snd st)) (fst st)).
Proof.
  pupto2_init.
  revert A t k s.
  pcofix CIH.
  intros A t k s.
  rewrite unfold_bind, (unfold_interp_state f t).
  destruct (observe t).
  (* TODO: performance issues with [ret|tau|vis_bind] here too. *)
  - cbn. rewrite !ret_bind. simpl.
    pupto2_final. apply reflexivity.
  - cbn. rewrite !tau_bind, interp_state_tau.
    pupto2_final. pfold. econstructor. right. apply CIH.
  - cbn. rewrite interp_state_vis, tau_bind, bind_bind.
    pfold; constructor.
    pupto2 eq_itree_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. specialize (CIH _ (k0 (snd u2)) k (fst u2)).
      auto.
Qed.

Instance eutt_interp_state {E F: Type -> Type} {S : Type}
         (h : E ~> Monads.stateT S (itree F)) R :
  Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E F S h R).
Proof.
  repeat intro. subst. pupto2_init. revert_until R. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.

  rewrite !unfold_interp_state. do 2 punfold H0.
  induction H0; intros; subst; simpl; pclearbot; eauto.
  - pfold; constructor.
    pupto2 eutt_nested_clo_bind; econstructor; [reflexivity|].
    intros; subst. pupto2_final.
    right. eapply CIH'. edestruct EUTTK; pclearbot; eauto.
  - econstructor. pupto2_final. eauto 9.
  - pfold; constructor. pfold_reverse.
    rewrite unfold_interp_state; auto.
  - pfold; constructor. pfold_reverse.
    rewrite unfold_interp_state; auto.
Qed.

(* Commuting interpreters --------------------------------------------------- *)

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g _ (translate f  t) ≅ interp (fun _ e => g _ (f _ e)) _ t.
Proof.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite !unfold_interp. unfold interp_u.
  rewrite unfold_translate. unfold translateF.
  destruct (observe t); cbn.
  - pupto2_final. apply Reflexive_eq_itree. (* SAZ: typeclass resolution failure? *)
  - pfold. constructor. pupto2_final. right. apply CIH.
  - pfold; constructor.
    pupto2 eq_itree_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. pupto2_final. auto.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.liftE (f _ e)) _ t.
Proof.
  pupto2_init; revert t; pcofix CIH; intros t.
  pfold. pupto2_init; revert t; pcofix CIH'; intros t.
  rewrite unfold_translate.
  rewrite unfold_interp.
  unfold translateF, interp_u.
  destruct (observe t); cbn; simpl in *; eauto.
  - pfold. constructor. auto.
  - unfold ITree.liftE. rewrite vis_bind.
    pfold. do 2 constructor.
    left. rewrite ret_bind. auto.
Qed.

(* Morphism Category -------------------------------------------------------- *)



Lemma eh_cmp_id_left_strong :
  forall A R (t : itree A R), interp eh_id R t ≈ t.
Proof.
  intros A R.
  intros t.
  pupto2_init; revert t; pcofix CIH; intros t.
  pfold; pupto2_init; revert t; pcofix CIH'; intros.
  rewrite unfold_interp. unfold interp_u.
  destruct (observe t); cbn; eauto.
  - pfold. econstructor. auto.
  - unfold eh_id, ITree.liftE. rewrite vis_bind.
    pfold; do 2 constructor.
    left; rewrite ret_bind; auto.
Qed.


Lemma eh_cmp_id_left :
  forall A B (f : A ~> itree B), eh_cmp eh_id f ≡ f.
Proof.
  intros A B f X e.
  unfold eh_cmp. apply eh_cmp_id_left_strong.
Qed.  


Lemma eh_cmp_id_right :
  forall A B (f : A ~> itree B), eh_cmp f eh_id ≡ f.
Proof.
  intros B A f X e.
  unfold eh_cmp.
  unfold eh_id. unfold ITree.liftE.
  rewrite unfold_interp. unfold interp_u.
  cbn. setoid_rewrite tau_eutt. setoid_rewrite interp_ret. rewrite bind_ret.
  reflexivity.
Qed.

Lemma eh_both_left_right_id : forall A B X e,  eh_both eh_inl eh_inr X e = (@eh_id (A +' B)) X e.
Proof.
  intros A B X e.
  unfold eh_both.
  unfold eh_id. unfold ITree.liftE.
  destruct e.
  - unfold eh_inl. reflexivity.
  - unfold eh_inr. reflexivity.
Qed.

Lemma eh_cmp_assoc : forall A B C D (h : C ~> itree D) (g : B ~> itree C) (f : A ~> itree B),
    eh_cmp h (eh_cmp g f) ≡ (eh_cmp (eh_cmp h g) f).
Proof.
  intros A B C D h g f X e.
  unfold eh_cmp. rewrite interp_interp. reflexivity.
Qed.

Lemma eh_par_id : forall A B, eh_par eh_id eh_id ≡ (@eh_id (A +' B)).
Proof.
  intros A B X e.
  unfold eh_par.
  unfold eh_id.
  destruct e.
  - unfold ITree.liftE.
    rewrite translate_vis.
    assert (pointwise_relation X (@eq_itree (A +' B) _ _ eq) (fun x : X => translate (inl1 (E2:=B)) (Ret x)) (fun x : X => Ret x)).
    { intros x. rewrite translate_ret. reflexivity. }
    rewrite H. reflexivity.
  - unfold ITree.liftE.
    rewrite translate_vis.
    assert (pointwise_relation X (@eq_itree (A +' B) _ _ eq) (fun x : X => translate (inr1 (E2:=B)) (Ret x)) (fun x : X => Ret x)).
    { intros x. rewrite translate_ret. reflexivity. }
    rewrite H. reflexivity.
Qed.

  
Lemma eh_swap_swap_id : forall A B, eh_cmp eh_swap eh_swap ≡ (eh_id : (A +' B) ~> itree (A +' B)).
Proof.
  intros A B X e.
  unfold eh_cmp. unfold eh_swap. unfold eh_lift.
  rewrite interp_liftE.
  setoid_rewrite tau_eutt. rewrite bind_ret.
  destruct e; simpl; reflexivity.
Qed.                                                               

Lemma eh_empty_unit_l : forall A, eh_cmp eh_empty_right eh_inl ≡ (eh_id : A ~> itree A).
Proof.
  intros A X e.
  unfold eh_cmp.
  unfold eh_empty_right.
  unfold eh_inl.
  unfold eh_lift.
  rewrite interp_liftE.
  setoid_rewrite tau_eutt. rewrite bind_ret.
  simpl. unfold Sum1.idE. reflexivity.
Qed.

Lemma eh_empty_unit_r : forall A, eh_cmp eh_empty_left eh_inr ≡ (eh_id : A ~> itree A).
Proof.
  intros A X e.
  unfold eh_cmp.
  unfold eh_empty_left.
  unfold eh_inr.
  unfold eh_lift.
  rewrite interp_liftE.
  setoid_rewrite tau_eutt. rewrite bind_ret.
  simpl. unfold Sum1.idE. reflexivity.
Qed.
