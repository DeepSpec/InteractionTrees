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
     Morphisms
     Eq.Eq
     Eq.UpToTaus.

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

Lemma interp_unfold {E F R} {f : E ~> itree F} (t : itree E R) :
  observe (interp f _ t) = observe (interp_u f _ (observe t)).
Proof. eauto. Qed.

Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  interp f _ t ≅ interp_u f _ (observe t).
Proof. rewrite itree_eta, interp_unfold, <-itree_eta. reflexivity. Qed.

(** ** [interp] and constructors *)

Lemma ret_interp {E F R} {f : E ~> itree F} (x: R):
  interp f _ (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma tau_interp {E F R} {f : E ~> itree F} (t: itree E R):
  interp f _ (Tau t) ≅ Tau (interp f _ t).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma vis_interp {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  interp f _ (Vis e k) ≅ Tau (ITree.bind (f _ e) (fun x => interp f _ (k x))).
Proof. rewrite unfold_interp. reflexivity. Qed.

(** ** [interp] properness *)

Instance eq_itree_interp {E F R} (f : E ~> itree F) :
  Proper (eq_itree eq ==> eq_itree eq) (interp f R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite itree_eta, (itree_eta (interp f _ y)), !interp_unfold.
  punfold H0; red in H0.
  destruct H0; pclearbot.
  - pupto2_final. pfold. red. cbn. eauto.
  - pupto2_final. pfold. red. cbn. eauto.
  - pfold. econstructor. pupto2 (eq_itree_clo_bind F R).
    constructor.
    + reflexivity.
    + eauto. intros; pupto2_final; right; eauto.
Qed.

Definition Rhom {E F : Type -> Type} : relation (E ~> F) :=
  fun l r =>
    forall x (e : E x), l _ e = r _ e.

(* Note that this allows rewriting of handlers. *)
Instance eutt_interp :
  forall (E F : Type -> Type) (R : Type),
    Proper (@Rhom E (itree F) ==> eutt eq ==> eutt eq)
           (fun f => interp f R).
Proof. Admitted.

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
  - rewrite ret_interp, !ret_bind. pupto2_final. apply reflexivity.
  - rewrite tau_interp, !tau_bind, tau_interp.
    pupto2_final. pfold. econstructor. eauto.
  - rewrite vis_interp, tau_bind. rewrite bind_bind.
    pfold. do 2 red; cbn. constructor.
    pupto2 (eq_itree_clo_bind F S). econstructor.
    + reflexivity.
    + intros; specialize (CIH _ (k0 v) k); auto.
Qed.


Lemma interp_liftE {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f _ (ITree.liftE e) ≅ Tau (f _ e).
Proof.
  unfold ITree.liftE. rewrite vis_interp.
  apply itree_eq_tau.
  assert (pointwise_relation _ (@eq_itree _ _ _ (@eq R)) (fun x : R => interp f R (Ret x)) (fun x => Ret x)).
  {red. intros. apply ret_interp. }
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
  rewrite eutt_is_eutt'_gres.
  pfold. revert t. pcofix CIH'.
  intros t.
  destruct (observe t); cbn.
  - pfold. econstructor.
  - pfold. econstructor.
    right. rewrite interp_unfold. unfold interp_u. unfold handleF.
    apply CIH'.
  - pfold. econstructor. cbn. econstructor. intros.
    assert (ITree.bind' (fun x0 : u => interp (fun (T : Type) (e0 : E T) => ITree.liftE e0) R (k x0)) (Ret x) = (x0 <- Ret x ;; interp (fun (T : Type) (e0 : E T) => ITree.liftE e0) R (k x0))).
    { intros; reflexivity. }
    rewrite H.
    rewrite ret_bind.
    pupto2_final. right. apply CIH.
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
  rewrite itree_eta.
  rewrite (itree_eta t).
  rewrite (itree_eta (interp (fun (T : Type) (e : E T) => interp g T (f T e)) R {| _observe := observe t|})).
  rewrite unfold_interp.
  destruct (observe t); cbn.
  - pupto2_final. pfold. econstructor. reflexivity.
  - pupto2_final. pfold. econstructor. right.  apply CIH.
  - rewrite interp_bind.
    pfold. econstructor.
    pupto2 eq_itree_clo_bind_h.
    apply pbc_intro_h with (RU := eq).  
    + reflexivity.
    + intros.
      pupto2_final. right. subst. apply CIH.
Qed.  
  
(** * [interp1] *)

(* SAZ: If we need to introduce these auxilliar definitions to prove
   properties about functions like interp1, I think that we shoul
   _define_ interp1 in terms of its unfolding.  I have experimented
   with porting interp_state and interp1_state to this form.
*)
(* Unfolding of [interp1]. *)
Definition interp1_u {E F G} `{F -< G} (h : E ~> itree G) R :
  itreeF (E +' F) R _ -> itree G R :=
  handleF (interp1 h _)
          (fun _ ef k =>
             match ef with
             | inl1 e => Tau (ITree.bind (h _ e)
                                         (fun x => interp1 h _ (k x)))
             | inr1 f => Vis (subeffect _ f) (fun x => interp1 h _ (k x))
             end).

Lemma interp1_unfold {E F R} {f : E ~> itree F} (t : itree (E +' F) R) :
  observe (interp1 f _ t) = observe (interp1_u f _ (observe t)).
Proof. eauto. Qed.

Lemma unfold_interp1 {E F R} {f : E ~> itree F} (t : itree (E +' F) R) :
  interp1 f _ t ≅ interp1_u f _ (observe t).
Proof. rewrite itree_eta, interp1_unfold, <-itree_eta. reflexivity. Qed.

(** ** [interp1] is equivalent to [interp] *)

Definition interp_match {E F} (f: E ~> itree F) : (E +' F) ~> itree F :=
  fun _ ef => match ef with inl1 e => f _ e | inr1 e => Vis e (fun r => Ret r) end.

Inductive interp_inv {E F R} (f: E ~> itree F) : relation (itree' F R) :=
| _interp_inv_main t:
    interp_inv f
      (observe (interp (interp_match f) _ t)) (observe (interp1 f _ t))
| _interp_inv_bind u t (k: u -> _):
    interp_inv f
      (observe (ITree.bind t (fun x => interp (interp_match f) _ (k x))))
      (observe (ITree.bind t (fun x => interp1 f _ (k x))))
.
Hint Constructors interp_inv.

Lemma interp_inv_main_step E F R (f: E ~> itree F) (t: itree _ R) :
  euttF' (fun x y => interp_inv f (observe x) (observe y)) (interp_inv f)
         (observe (interp (interp_match f) _ t)) (observe (interp1 f _ t)).
Proof.
  rewrite interp_unfold, interp1_unfold.
  genobs t ot. clear Heqot t.
  destruct ot; simpl; eauto.
  destruct e; simpl; eauto.
  econstructor. rewrite bind_unfold.
  econstructor. intros.
  fold_bind. rewrite bind_unfold. simpl. eauto.
Qed.

Lemma interp_is_interp1 E F R (f: E ~> itree F) (t: itree _ R) :
  interp (interp_match f) _ t ≈ interp1 f _ t.
Proof.
  revert t.
  cut (forall (t1 t2: itree _ R) (REL: interp_inv f (observe t1) (observe t2)), t1 ≈ t2).
  { eauto. }

  intros. apply eutt_is_eutt'.
  revert t1 t2 REL. pcofix CIH. intros. pfold.
  revert t1 t2 REL. pcofix CIH'. intros.
  destruct REL.
  - pfold. eapply euttF'_mon; eauto using interp_inv_main_step; intros.
    eapply upaco2_mon; eauto. intros.
    eapply (CIH' (go x2) (go x3)); eauto.
  - rewrite !bind_unfold. fold_bind.
    genobs t ot. clear Heqot t.
    destruct ot; simpl; eauto 10. 
    pfold. eapply euttF'_mon; eauto using interp_inv_main_step; intros.
    eapply upaco2_mon; eauto. intros.
    eapply (CIH' (go x2) (go x3)); eauto.
Qed.

Instance eq_itree_interp1 {E F R} (h : E ~> itree F) :
  Proper (@eq_itree (E +' F) _ _ eq ==> eq_itree eq) (interp1 h R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite !unfold_interp1.
  punfold H0; red in H0.
  destruct H0; pclearbot.
  - pupto2_final. pfold. red. cbn. eauto.
  - pupto2_final. pfold. red. cbn. eauto.
  - pfold. destruct e; cbn; econstructor.
    + pupto2 (eq_itree_clo_bind F R).
      constructor.
      * reflexivity.
      * intros; pupto2_final; eauto.
    + intros. pupto2_final. eauto.
Qed.

Instance eutt_interp1 {E F: Type -> Type} (h: E ~> itree F) R:
  Proper (eutt eq ==> eutt eq) (@interp1 E F F _ h R).
Proof.
  repeat intro.
  rewrite <- 2 interp_is_interp1.
  eapply eutt_interp; auto.
  red; reflexivity.
Qed.

(** * [interp_state] *)

Lemma unfold_interp_state : forall {E F S R} (h : E ~> Monads.stateT S (itree F)) t s,
    observe (interp_state h _ t s) =
    observe (interp_state_match h (interp_state h R) t s).
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
    constructor.
    + subst. reflexivity.
    + intros; pupto2_final; right; eauto.
Qed.


Lemma unfold_interp1_state : forall {E F S R} (h : E ~> Monads.stateT S (itree F)) t s,
    observe (interp1_state h _ t s) =
    observe (interp1_state_match h (interp1_state h R) t s).
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
      constructor. 
      + subst. reflexivity.
      + intros. pupto2_final. right. eauto.
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
  - cbn. rewrite interp_state_ret. rewrite !ret_bind. simpl.
    pupto2_final. apply reflexivity.
  - cbn. rewrite interp_state_tau, !tau_bind, interp_state_tau.
    pupto2_final. pfold. econstructor. right. apply CIH.
  - cbn. rewrite interp_state_vis, tau_bind, vis_bind, bind_bind, interp_state_vis.
    pfold. red. constructor.
    pupto2 (eq_itree_clo_bind F (S * B)). econstructor.
    + reflexivity.
    + intros. specialize (CIH _ (k0 (snd v)) k (fst v)). auto.
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
      + intros. specialize (CIH _ (k0 (snd v)) k (fst v)). auto.
   * rewrite interp1_state_vis2, !vis_bind. rewrite itree_eta. rewrite unfold_interp1_state.
     cbn. pfold. constructor. intros.
     specialize (CIH _ (k0 v) k s). auto.
Qed.

Instance eutt_interp_state {E F: Type -> Type} {S : Type}
         (h : E ~> Monads.stateT S (itree F)) R :
  Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E F S h R).
Proof.
Admitted.

(* Translate facts ---------------------------------------------------------- *)

Definition translate_u {E F} (h : E ~> F) R :
  itreeF E R _ -> itree F R :=
      handleF (translate h _)
            (fun _ e k => Vis (h _ e) (fun x => translate h _ (k x))).

Lemma translate_unfold {E F R} {h : E ~> F} (t : itree E R) :
  observe (translate h _ t) = observe (translate_u h _ (observe t)).
Proof. eauto. Qed.

Lemma unfold_translate {E F R} {h : E ~> F} (t : itree E R) :
  translate h _ t ≅ translate_u h _ (observe t).
Proof. rewrite itree_eta, translate_unfold, <-itree_eta. reflexivity. Qed.


Instance translate_Proper : forall {A B R} (h : A ~> B), Proper ( (eq_itree (@eq R)) ==> eq_itree eq) (translate h _).
Proof.
  repeat red.
  intros A B R h x y H.
  pupto2_init.
  revert x y H.
  pcofix CIH.
  intros x y H.
  rewrite itree_eta.
  rewrite (itree_eta (translate h R y)).
  repeat rewrite translate_unfold. unfold translate_u.
  rewrite (itree_eta x) in H.
  rewrite (itree_eta y) in H.
  destruct (observe x); destruct (observe y); pinversion H; subst; cbn.
  - pupto2_final. apply Reflexive_eq_itree. (* SAZ: typeclass resolution not working *)
  - pupto2_final. pfold. constructor.  right. apply CIH. eauto.
  - pupto2_final. pfold.
    repeat (match goal with
          | [ H : _ |- _ ] => apply inj_pair2 in H
            end). subst.
    constructor.
    inversion H.
    repeat (match goal with
          | [ H : _ |- _ ] => apply inj_pair2 in H
            end). subst. 
    right. apply CIH. 
    eapply transitivity. pclearbot. apply REL0. reflexivity.
Qed.
  
Lemma translate_ret : forall {A B R} (h : A ~> B) (r:R),
    translate h _ (Ret r) ≅ Ret r.
Proof.
  intros A B R h r.
  rewrite itree_eta.
  cbn. reflexivity.
Qed.

Lemma translate_tau : forall {A B R} (h : A ~> B) (t: itree A R),
    translate h _ (Tau t) ≅ Tau (translate h _ t).
Proof.
  intros A B R h t.
  rewrite itree_eta.
  cbn. reflexivity.
Qed.

Lemma translate_vis : forall {A B R} (h : A ~> B) X (e : A X) (k: X -> itree A R),
    translate h _ (Vis e k) ≅ Vis (h _ e) (fun x => translate h _ (k x)).
Proof.
  intros A B R h X e k.
  rewrite itree_eta.
  cbn. reflexivity.
Qed.

(* Commuting interpreters --------------------------------------------------- *)

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g _ (translate f _ t) ≅ interp (fun _ e => g _ (f _ e)) _ t.
Proof.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite (itree_eta).
  rewrite (itree_eta (interp (fun (T : Type) (e : E T) => g T (f T e)) R t)).
  rewrite !unfold_interp. unfold interp_u.
Admitted.

(* Morphism Category -------------------------------------------------------- *)

Definition eh_eq {A B : Type -> Type} f g := forall X, pointwise_relation (A X) (@eutt B X _ (@eq X)) (f X) (g X).

Notation "f ≡ g" := (eh_eq f g) (at level 70).


Lemma eh_compose_id_left_strong :
  forall A R (t : itree A R), interp eh_id R t ≈ t.
Proof.
  intros A R. 
  intros t.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite unfold_interp. unfold interp_u. unfold handleF.
  rewrite eutt_is_eutt'_gres.
  pfold. revert t. pcofix CIH'.
  intros t.
  destruct (observe t); cbn.
  - pfold. econstructor.
  - pfold. econstructor.
    right. rewrite interp_unfold. unfold interp_u. unfold handleF.
    apply CIH'.
  - pfold. econstructor. cbn. econstructor. intros. 
    assert (ITree.bind' (fun x0 : u => interp eh_id R (k x0)) (Ret x) = (x0 <- Ret x ;; interp eh_id R (k x0))).
    { intros; reflexivity. }
    rewrite H. rewrite ret_bind.
    pupto2_final. right. apply CIH.
Qed.  
  

Lemma eh_compose_id_left :
  forall A B (f : A ~> itree B), eh_compose eh_id f ≡ f.
Proof.
  intros A B f X e.
  unfold eh_compose. apply eh_compose_id_left_strong.
Qed.  


Lemma eh_compose_id_right :
  forall A B (f : A ~> itree B), eh_compose f eh_id ≡ f.
Proof.
  intros B A f X e.
  unfold eh_compose.
  unfold eh_id. unfold ITree.liftE.
  rewrite unfold_interp. unfold interp_u.
  unfold handleF.
  cbn. eapply transitivity. apply tau_eutt.
  assert (pointwise_relation _ (eq_itree eq) (fun x : X => interp f X (Ret x)) (fun x => Ret x)).
  { red. intros. apply interp_ret. }
  rewrite H. rewrite bind_ret.
  reflexivity.
Qed.  
  
Lemma eh_both_left_right_id : forall A B X e,  eh_both eh_left eh_right X e = (@eh_id (A +' B)) X e.
Proof.
  intros A B X e.
  unfold eh_both.
  unfold eh_id. unfold ITree.liftE.
  destruct e.
  - unfold eh_left. reflexivity.
  - unfold eh_right. reflexivity.
Qed.

Lemma eh_compose_assoc : forall A B C D (h : C ~> itree D) (g : B ~> itree C) (f : A ~> itree B),
    eh_compose h (eh_compose g f) ≡ (eh_compose (eh_compose h g) f).
Proof.
  intros A B C D h g f X e.
  unfold eh_compose. rewrite interp_interp. reflexivity.
Qed.

Lemma eh_par_id : forall A B, eh_par eh_id eh_id ≡ (@eh_id (A +' B)).
Proof.
  intros A B X e.
  unfold eh_par.
  unfold eh_id.
  destruct e.
  - unfold ITree.liftE.
    rewrite translate_vis.
    assert (pointwise_relation X (@eq_itree (A +' B) _ _ eq) (fun x : X => translate (inl1 (E2:=B)) X (Ret x)) (fun x : X => Ret x)).
    { intros x. rewrite translate_ret. reflexivity. }
    rewrite H. reflexivity.
  - unfold ITree.liftE.
    rewrite translate_vis.
    assert (pointwise_relation X (@eq_itree (A +' B) _ _ eq) (fun x : X => translate (inr1 (E2:=B)) X (Ret x)) (fun x : X => Ret x)).
    { intros x. rewrite translate_ret. reflexivity. }
    rewrite H. reflexivity.
Qed.

    

