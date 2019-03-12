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
Definition interp_u {E F} (f : E ~> itree F) R :
  itreeF E R _ -> itree F R :=
  handleF (interp f _)
          (fun _ e k => Tau (ITree.bind (f _ e)
                                        (fun x => interp f _ (k x)))).

Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  observing eq (interp f _ t) (interp_u f _ (observe t)).
Proof. econstructor. reflexivity. Qed.

(** ** [interp] and constructors *)

Lemma ret_interp {E F R} {f : E ~> itree F} (x: R):
  observing eq (interp f _ (Ret x)) (Ret x).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma tau_interp {E F R} {f : E ~> itree F} (t: itree E R):
  observing eq (interp f _ (Tau t)) (Tau (interp f _ t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma vis_interp {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  observing eq (interp f _ (Vis e k)) (Tau (ITree.bind (f _ e) (fun x => interp f _ (k x)))).
Proof. rewrite unfold_interp. reflexivity. Qed.

(** ** [interp] properness *)
Instance eq_itree_interp {E F R}:
  Proper (Rhom (fun _ => eq_itree eq) ==> eq_itree eq ==> eq_itree eq)
         (fun f => @interp E F f R).
Proof.
  intros f g Hfg.
  intros l r Hlr.
  pupto2_init.
  revert l r Hlr.
  pcofix CIH.
  rename r into rr.
  intros l r Hlr.
  rewrite itree_eta, (itree_eta (interp g _ r)), !unfold_interp.
  punfold Hlr; red in Hlr.
  destruct Hlr; pclearbot.
  - pupto2_final. pfold. red. cbn. eauto.
  - pupto2_final. pfold. red. cbn. eauto.
  - pfold. econstructor. pupto2 eq_itree_clo_bind.
    econstructor.
    + eapply Hfg.
    + intros; subst; pupto2_final; right; eauto.
Qed.

Global Instance Proper_interp_eq_itree {E F R f}
: Proper (eq_itree eq ==> eq_itree eq) (@interp E F f R).
Proof.
  eapply eq_itree_interp.
  red. reflexivity.
Qed.

(* Note that this allows rewriting of handlers. *)
Instance eutt_interp (E F : Type -> Type) (R : Type) :
  Proper (Rhom (fun _ => eutt eq) ==> eutt eq ==> eutt eq)
         (fun f => @interp E F f R).
Proof.
  repeat intro. pupto2_init. revert_until H. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.

  rewrite !unfold_interp. do 2 punfold H1. pfold.
  induction H1; intros; subst; pclearbot; simpl; eauto.
  - econstructor. pupto2 eutt_nested_clo_bind.
    econstructor; [apply H|].
    intros; subst. pupto2_final.
    right. eapply CIH'. edestruct EUTTK; pclearbot; eauto.
  - econstructor. pupto2_final. eauto 7.
Qed.

Lemma interp_ret : forall {E F R} x
      (f : E ~> itree F),
   (interp f R (Ret x)) ≅ Ret x.
Proof.
  intros. rewrite (itree_eta (Ret x)).
  rewrite unfold_interp. unfold interp_u. unfold handleF.
  cbn. reflexivity.
Qed.

Lemma interp_bind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
   (interp f _ (ITree.bind t k)) ≅ (ITree.bind (interp f _ t) (fun r => interp f _ (k r))).
Proof.
  pupto2_init.
  revert R t k.
  pcofix CIH. intros.
  rewrite (itree_eta t). destruct (observe t).
  (* TODO: [ret_bind] (0.8s) is much slower than [ret_bind_] (0.02s) *)
  - rewrite ret_interp. rewrite !ret_bind. pupto2_final. apply reflexivity.
  - rewrite tau_interp, !tau_bind, tau_interp.
    pupto2_final. pfold. econstructor. eauto.
  - rewrite vis_interp, tau_bind. rewrite bind_bind.
    pfold. do 2 red; cbn. constructor.
    pupto2 (eq_itree_clo_bind F S). econstructor.
    + reflexivity.
    + intros; subst. specialize (CIH _ (k0 u2) k); auto.
Qed.

Lemma interp_liftE {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f _ (ITree.liftE e) ≅ Tau (f _ e).
Proof.
  unfold ITree.liftE. rewrite vis_interp.
  apply itree_eq_tau.
  assert (pointwise_relation _ (@eq_itree _ _ _ (@eq R)) (fun x : R => interp f R (Ret x)) (fun x => Ret x)).
  {red. intros. rewrite ret_interp. reflexivity. }
  rewrite H. rewrite bind_ret.
  reflexivity.
Qed.


(** ** Composition of [interp] *)

Lemma interp_id_liftE {E R} (t : itree E R) :
  interp (fun _ e => ITree.liftE e) _ t ≈ t.
Proof.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite unfold_interp. unfold interp_u. unfold handleF.
  pfold. revert t. pcofix CIH'.
  intros t.
  destruct (observe t); cbn; eauto.
  - pfold. econstructor.
    right. rewrite unfold_interp. unfold interp_u. unfold handleF.
    apply CIH'.
  - pfold. econstructor. cbn. econstructor. intros.
    assert (ITree.bind' (fun x0 : u => interp (fun (T : Type) (e0 : E T) => ITree.liftE e0) R (k x0)) (Ret x) = (x0 <- Ret x ;; interp (fun (T : Type) (e0 : E T) => ITree.liftE e0) R (k x0))).
    { intros; reflexivity. }
    left. rewrite H, ret_bind.
    pupto2_final. eauto.
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
  rewrite !unfold_interp.
  destruct (observe t); cbn.
  - pupto2_final. pfold. econstructor. reflexivity.
  - pupto2_final. pfold. econstructor. right.  apply CIH.
  - rewrite interp_bind.
    pfold. econstructor.
    pupto2 eq_itree_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros.
      pupto2_final. right. subst. apply CIH.
Qed.

(** * [interp_state] *)

Lemma unfold_interp_state : forall {E F S R} (h : E ~> Monads.stateT S (itree F)) t s,
    observe (interp_state h _ t s) =
    observe (interp_state_match h (interp_state h R) (observe t) s).
Proof.
  intros E F S R h t s.
  econstructor.
Qed.

Instance eq_itree_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq)
         (interp_state h R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros h x y H0 x2 y0 H1.
  rewrite itree_eta, (itree_eta (interp_state h _ y y0)), !unfold_interp_state.
  unfold interp_state_match.
  punfold H0; red in H0.
  genobs x ox; destruct ox; simpobs; dependent destruction H0; simpobs; pclearbot.
  - pupto2_final. pfold. red. cbn. subst. eauto.
  - pupto2_final. pfold. red. cbn. subst. eauto.
  - pfold. econstructor. pupto2 (eq_itree_clo_bind F (S * R)).
    econstructor.
    + subst. reflexivity.
    + intros; subst. pupto2_final; right; eauto.
Qed.


Lemma unfold_interp1_state : forall {E F S R} (h : E ~> Monads.stateT S (itree F)) t s,
    observe (interp1_state h _ t s) =
    observe (interp1_state_match h (interp1_state h R) (observe t) s).
Proof.
  intros E F S R h t s.
  econstructor.
Qed.

Instance eq_itree_interp1_state {E F S R} (h : E ~> Monads.stateT S (itree F)) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq) (interp1_state h R).
Proof.
  repeat intro.
  pupto2_init. revert_until R.
  pcofix CIH. intros h x y H0 x2 y0 H1.
  rewrite itree_eta, (itree_eta (interp1_state h _ y y0)), !unfold_interp1_state.
  unfold interp1_state_match.
  punfold H0; red in H0.
  genobs x ox; destruct ox; simpobs; dependent destruction H0; simpobs; pclearbot.
  - pupto2_final. pfold. red. cbn. subst. eauto.
  - pupto2_final. pfold. red. cbn. subst. eauto.
  - pfold.
    destruct e.
    * econstructor. pupto2 (eq_itree_clo_bind F (S * R)).
      econstructor.
      + subst. reflexivity.
      + intros; subst. pupto2_final. right. eauto.
    * econstructor. intros. pupto2_final. right.
      eauto.
Qed.


Lemma interp_state_ret {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (s : S) (r : R) :
  (interp_state f _ (Ret r) s) ≅ (Ret (s, r)).
Proof.
  rewrite itree_eta. reflexivity.
Qed.


Lemma interp1_state_ret {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (s : S) (r : R) :
  (interp1_state f _ (Ret r) s) ≅ (Ret (s, r)).
Proof.
  rewrite itree_eta. reflexivity.
Qed.


Lemma interp_state_vis : forall {E F:Type -> Type} {S T U : Type} (s:S) e k
                           (h : E ~> Monads.stateT S (itree F)),
    interp_state h U (Vis e k) s ≅ Tau (ITree.bind (h T e s) (fun sx => interp_state h _ (k (snd sx)) (fst sx))).
Proof.
  intros E F S T U s e k h.
  rewrite itree_eta.
  reflexivity.
Qed.

Lemma interp1_state_vis1 : forall {E F:Type -> Type} {S T U : Type} (s:S) e k
                           (h : E ~> Monads.stateT S (itree F)),
    interp1_state h U (Vis (inl1 e) k) s ≅ Tau (ITree.bind (h T e s) (fun sx => interp1_state h _ (k (snd sx)) (fst sx))).
Proof.
  intros E F S T U s e k h.
  rewrite itree_eta.
  reflexivity.
Qed.

Lemma interp1_state_vis2 : forall {E F:Type -> Type} {S T U : Type} (s:S) (e : F T) k
                           (h : E ~> Monads.stateT S (itree F)),
    interp1_state h U (Vis (inr1 e) k) s ≅ (Vis e (fun x => interp1_state h _ (k x) s)).
Proof.
  intros E F S T U s e k h.
  rewrite itree_eta.
  reflexivity.
Qed.

Lemma interp_state_tau : forall {E F:Type -> Type} S {T : Type} (t:itree E T) (s:S)
                           (h : E ~> Monads.stateT S (itree F)),
    interp_state h _ (Tau t) s ≅ Tau (interp_state h _ t s).
Proof.
  intros E F S T t s h.
  rewrite itree_eta. reflexivity.
Qed.

Lemma interp1_state_tau : forall {E F:Type -> Type} S {T : Type} (t:itree (E +' F) T) (s:S)
                           (h : E ~> Monads.stateT S (itree F)),
    interp1_state h _ (Tau t) s ≅ Tau (interp1_state h _ t s).
Proof.
  intros E F S T t s h.
  rewrite itree_eta. reflexivity.
Qed.

Lemma interp_state_liftE {E F : Type -> Type} {R S : Type}
      (f : E ~> Monads.stateT S (itree F))
      (s : S) (e : E R) :
  (interp_state f _ (ITree.liftE e) s) ≅ Tau (f _ e s).
Proof.
  unfold ITree.liftE. rewrite interp_state_vis.
  assert (pointwise_relation _ (eq_itree eq) (fun sx : S * R => interp_state f R (Ret (snd sx)) (fst sx)) (fun sx => Ret sx)).
  { intros sx. destruct sx. simpl.
    rewrite itree_eta. cbn. reflexivity. }
  rewrite H.
  rewrite bind_ret.
  reflexivity.
Qed.

Lemma interp1_state_liftE1 {E F : Type -> Type} {R S : Type}
      (f : E ~> Monads.stateT S (itree F))
      (s : S) (e : E R) :
  (interp1_state f _ (ITree.liftE (inl1 e)) s) ≅ Tau (f _ e s).
Proof.
  unfold ITree.liftE. rewrite interp1_state_vis1.
  assert (pointwise_relation _ (eq_itree eq) (fun sx : S * R => interp1_state f R (Ret (snd sx)) (fst sx)) (fun sx => Ret sx)).
  { intros sx. destruct sx. simpl.
    rewrite itree_eta. cbn. reflexivity. }
  rewrite H.
  rewrite bind_ret.
  reflexivity.
Qed.

Lemma interp1_state_liftE2 {E F : Type -> Type} {R S : Type}
      (f : E ~> Monads.stateT S (itree F))
      (s : S) (e : F R) :
  (interp1_state f _ (ITree.liftE (inr1 e)) s) ≅ Vis e (fun x => Ret (s, x)).
Proof.
  unfold ITree.liftE. rewrite interp1_state_vis2.
  apply itree_eq_vis. intros.
  rewrite interp1_state_ret. reflexivity.
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
  rewrite (itree_eta t).
  destruct (observe t).
  (* TODO: performance issues with [ret|tau|vis_bind] here too. *)
  - cbn. rewrite interp_state_ret. rewrite !ret_bind. simpl.
    pupto2_final. apply reflexivity.
  - cbn. rewrite interp_state_tau, !tau_bind, interp_state_tau.
    pupto2_final. pfold. econstructor. right. apply CIH.
  - cbn. rewrite interp_state_vis, tau_bind, vis_bind, bind_bind, interp_state_vis.
    pfold. red. constructor.
    pupto2 (eq_itree_clo_bind F (S * B)). econstructor.
    + reflexivity.
    + intros. subst. specialize (CIH _ (k0 (snd u2)) k (fst u2)). auto.
Qed.

Lemma interp1_state_bind {E F : Type -> Type} {A B S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (t : itree (E +' F) A) (k : A -> itree (E +' F) B)
      (s : S) :
  (interp1_state f _ (t >>= k) s)
    ≅
  (interp1_state f _ t s >>= fun st => interp1_state f _ (k (snd st)) (fst st)).
Proof.
  pupto2_init.
  revert A t k s.
  pcofix CIH.
  intros A t k s.
  rewrite (itree_eta t).
  destruct (observe t).
  - cbn. rewrite interp1_state_ret. rewrite !ret_bind. simpl.
    pupto2_final. apply reflexivity.
  - cbn. rewrite interp1_state_tau, !tau_bind, interp1_state_tau.
    pupto2_final. pfold. econstructor. right. apply CIH.
  - cbn. destruct e.
    * rewrite interp1_state_vis1, tau_bind, vis_bind, bind_bind, interp1_state_vis1.
      pfold. red. constructor.
      pupto2 (eq_itree_clo_bind F (S * B)). econstructor.
      + reflexivity.
      + intros. subst. specialize (CIH _ (k0 (snd u2)) k (fst u2)). auto.
   * rewrite interp1_state_vis2, !vis_bind. rewrite itree_eta. rewrite unfold_interp1_state.
     cbn. pfold. constructor. intros.
     specialize (CIH _ (k0 v) k s). auto.
Qed.

Instance eutt_interp_state {E F: Type -> Type} {S : Type}
         (h : E ~> Monads.stateT S (itree F)) R :
  Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E F S h R).
Proof.
  repeat intro. subst. pupto2_init. revert_until R. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.

  rewrite !unfold_interp_state. do 2 punfold H0. pfold.
  induction H0; intros; subst; simpl; pclearbot; eauto.
  - econstructor. pupto2 eutt_nested_clo_bind.
    econstructor; [reflexivity|].
    intros; subst. pupto2_final.
    right. eapply CIH'. edestruct EUTTK; pclearbot; eauto.
  - econstructor. pupto2_final. eauto 7.
Qed.

(* Commuting interpreters --------------------------------------------------- *)

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g _ (translate f  t) ≅ interp (fun _ e => g _ (f _ e)) _ t.
Proof.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite (itree_eta).
  rewrite (itree_eta (interp (fun (T : Type) (e : E T) => g T (f T e)) R t)).
  rewrite !unfold_interp. unfold interp_u.
  unfold handleF. rewrite unfold_translate. unfold translateF.
  destruct (observe t); cbn.
  - pupto2_final. apply Reflexive_eq_itree. (* SAZ: typeclass resolution failure? *)
  - pfold. constructor. pupto2_final. right. apply CIH.
  - pfold. constructor.
    pupto2 eq_itree_clo_bind.
    econstructor.
    + reflexivity.
    + intros. subst. pupto2_final. right. apply CIH.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.liftE (f _ e)) _ t.
Proof.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite itree_eta.
  rewrite (itree_eta (interp (fun (T : Type) (e : E T) => ITree.liftE (f T e)) R t)).
  rewrite unfold_translate.
  rewrite unfold_interp.
  unfold translateF, interp_u, handleF.
  pfold. revert t. pcofix CIH'.
  intros t.
  destruct (observe t); cbn; simpl in *; eauto.
  - pfold. econstructor.
    right. rewrite unfold_translate. unfold translateF.
    rewrite unfold_interp. unfold interp_u. apply CIH'.
  - pfold. econstructor. unfold ITree.liftE. rewrite vis_bind.
    econstructor. intros.
    left.
    rewrite (itree_eta (x0 <- Ret x;; interp (fun (T : Type) (e0 : E T) => Vis (f T e0) (fun x1 : T => Ret x1)) R (k x0))).
    assert ((observe (x0 <- Ret x;; interp (fun (T : Type) (e0 : E T) => Vis (f T e0) (fun x1 : T => Ret x1)) R (k x0)))
            = observe (interp (fun (T : Type) (e0 : E T) => Vis (f T e0) (fun x1 : T => Ret x1)) R (k x))).
    { reflexivity. }
    rewrite H.
    unfold ITree.liftE in CIH.
    rewrite <- itree_eta.
    pupto2_final. right.
    apply CIH.
Qed.

(* Morphism Category -------------------------------------------------------- *)



Lemma eh_cmp_id_left_strong :
  forall A R (t : itree A R), interp eh_id R t ≈ t.
Proof.
  intros A R.
  intros t.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite unfold_interp. unfold interp_u. unfold handleF.
  pfold. revert t. pcofix CIH'.
  intros t.
  destruct (observe t); cbn; eauto.
  - pfold. econstructor.
    right. rewrite unfold_interp. unfold interp_u. unfold handleF.
    apply CIH'.
  - pfold. econstructor. cbn. econstructor. intros.
    assert (ITree.bind' (fun x0 : u => interp eh_id R (k x0)) (Ret x) = (x0 <- Ret x ;; interp eh_id R (k x0))).
    { intros; reflexivity. }
    left.
    rewrite H. rewrite ret_bind. (* TODO: [ret_bind] doesn't work *)
    pupto2_final. right. apply CIH.
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
  unfold handleF.
  cbn. eapply transitivity. apply tau_eutt.
  assert (pointwise_relation _ (eq_itree eq) (fun x : X => interp f X (Ret x)) (fun x => Ret x)).
  { red. intros. apply interp_ret. }
  rewrite H. rewrite bind_ret.
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
  rewrite interp_liftE. rewrite tau_eutt. destruct e; simpl; reflexivity.
Qed.                                                               

Lemma eh_empty_unit_l : forall A, eh_cmp eh_empty_right eh_inl ≡ (eh_id : A ~> itree A).
Proof.
  intros A X e.
  unfold eh_cmp.
  unfold eh_empty_right.
  unfold eh_inl.
  unfold eh_lift.
  rewrite interp_liftE.
  rewrite tau_eutt.
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
  rewrite tau_eutt.
  simpl. unfold Sum1.idE. reflexivity.
Qed.

(***
 lemmas about [interp1].
 We can remove [interp1] but keep it just in case it is useful.
 ***)

Definition interp1_u {E F G} `{F -< G} (h : E ~> itree G) R :
  itreeF (E +' F) R _ -> itree G R :=
  handleF (interp1 h _)
          (fun _ ef k =>
             match ef with
             | inl1 e => Tau (ITree.bind (h _ e)
                                         (fun x => interp1 h _ (k x)))
             | inr1 f => Vis (subeffect _ f) (fun x => interp1 h _ (k x))
             end).

Lemma unfold_interp1 {E F G : Type -> Type} `{F -< G} (h : E ~> itree G) R (t : itree (E +' F) R) :
  observing eq (interp1 h _ t) (interp1_u h _ (observe t)).
Proof. econstructor. auto. Qed.

Lemma unfold_interp1_ {E F G : Type -> Type} `{F -< G} (h : E ~> itree G) R (t : itree (E +' F) R) :
  interp1 h _ t ≅ interp1_u h _ (observe t).
Proof. rewrite itree_eta, unfold_interp1, <-itree_eta. reflexivity. Qed.

(** ** [interp1] is equivalent to [interp] *)

Section interp1_is_interp.

Context {E F G : Type -> Type} `{F -< G} (f : E ~> itree G).
  
Definition interp_match : (E +' F) ~> itree G :=
  fun _ ef => match ef with inl1 e => f _ e | inr1 e => Vis (subeffect _ e) (fun r => Ret r) end.

Lemma interp_is_interp1 R (t: itree _ R) :
  interp interp_match _ t ≈ interp1 f _ t.
Proof.
  pupto2_init. revert_until R. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.

  rewrite unfold_interp, unfold_interp1. unfold interp_u, interp1_u.
  destruct (observe t); [| |destruct e]; simpl; eauto.
  - pfold; econstructor. pupto2_final. eauto.
  - pfold; econstructor. pupto2 eutt_nested_clo_bind.
    econstructor; [reflexivity|].
    intros. subst. eauto.
  - rewrite vis_bind_. pfold. econstructor. econstructor.
    left. rewrite ret_bind_. pupto2_final. eauto.
Qed.

End interp1_is_interp.

Instance eq_itree_interp1 {E F G R} `{F -< G} (h : E ~> itree G) :
  Proper (@eq_itree (E +' F) _ _ eq ==> eq_itree eq) (interp1 h R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite !unfold_interp1_.
  punfold H1; red in H1.
  destruct H1; pclearbot.
  - pupto2_final. pfold. red. cbn. eauto.
  - pupto2_final. pfold. red. cbn. eauto.
  - pfold. destruct e; cbn; econstructor.
    + pupto2 eq_itree_clo_bind.
      econstructor.
      * reflexivity.
      * intros; subst. pupto2_final; eauto.
    + intros. pupto2_final. eauto.
Qed.

Instance eutt_interp1 {E F G R} `{F -< G} (h: E ~> itree G):
  Proper (eutt eq ==> eutt eq) (@interp1 E F G _ h R).
Proof.
  repeat intro. pupto2_init. revert_until H. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.

  rewrite !unfold_interp1. do 2 punfold H1. pfold.
  induction H1; intros; subst; pclearbot; simpl; eauto.
  - destruct e.
    + econstructor. pupto2 eutt_nested_clo_bind.
      econstructor; [reflexivity|].
      intros; subst. pupto2_final.
      right. eapply CIH'. edestruct EUTTK; pclearbot; eauto.
    + econstructor. left. pupto2_final.
      right. eapply CIH. edestruct EUTTK; pclearbot; eauto.
  - econstructor. pupto2_final. eauto 7.
Qed.

Lemma interp1_bind {E F G} `{F -< G} {R S} (h : E ~> itree G) (t : _ R) (k : _ -> itree (E +' F) S) :
  interp1 h _ (t >>= k) ≅ interp1 h _ t >>= fun x => interp1 h _ (k x).
Proof.
  pupto2_init.
  revert t; pcofix self; intros.
  rewrite !unfold_interp1_, unfold_bind, unfold_bind_.
  destruct (observe t); cbn.
  - rewrite unfold_interp1_.
    pupto2_final. apply reflexivity.
  - pfold; constructor; auto.
  - destruct e; cbn.
    + rewrite bind_bind. pfold; constructor.
      pupto2 eq_itree_clo_bind. econstructor.
      * reflexivity.
      * intros; subst. eauto.
    + pfold; constructor; auto.
Qed.

Lemma translate_interp1 {E F R} (h : F ~> itree E) :
  forall (t : itree E R),
    interp1 h _ (translate (fun _ e => inr1 e) t) ≅ t.
Proof.
  pcofix self; intros.
  pfold; red.
  rewrite unfold_interp1.
  rewrite TranslateFacts.unfold_translate.
  destruct (observe t); cbn; auto.
Qed.

Lemma interp1_liftE {E F G: Type -> Type} `{F -< G}:
  forall (h: forall T: Type, E T -> itree G T) T (e : E T),
    @interp1 E F G _ h T (lift e) ≈ h T e.
Proof.
  intros. unfold lift.
  rewrite unfold_interp1_; cbn.
  rewrite tau_eutt.
  setoid_rewrite unfold_interp1_; cbn.
  rewrite bind_ret.
  reflexivity.
Qed.
