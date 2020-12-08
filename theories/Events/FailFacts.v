(** * Theorems about Failure effects *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.HeterogeneousRelations
     Basics.Monad
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Interp.Interp
     Interp.InterpFacts
     Interp.RecursionFacts
     Events.State.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.
Open Scope itree_scope.

Import Monads.

Section FailT.

  Context {m : Type -> Type} {Fm: Functor.Functor m} {Mm : Monad m} {MIm : MonadIter m}.

  Definition failT (m : Type -> Type) (a : Type) : Type :=
    m (option a)%type.

  Global Instance failT_fun : Functor.Functor (failT m) :=
    {| Functor.fmap := fun x y f => 
                         Functor.fmap (fun x => match x with | None => None | Some x => Some (f x) end) |}.

  Global Instance failT_monad : Monad (failT m) :=
    {| ret := fun _ x => ret (Some x);
       bind := fun _ _ c k =>
                 bind (m := m) c 
                      (fun x => match x with | None => ret (None) | Some x => k x end)
    |}.

  Global Instance failT_iter  : MonadIter (failT m) :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := option A) 
                               (fun i => bind (m := m)
                                           (body i)
                                           (fun x => match x with
                                                  | None       => ret (inr None)
                                                  | Some (inl j) => ret (inl j)
                                                  | Some (inr a) => ret (inr (Some a))
                                                  end))
                               i.

End FailT.

Section FailTLaws.

  (* With the current state of the monad theory, we cannot prove the laws generically.
     We specialize things to [failT (itree E)] until we generalize [Eq1] to be parameterized
     by the underlying relation on returned values.
   *)
  Definition option_rel {X : Type} (R : relation X) : relation (option X) :=
    fun mx my => match mx,my with
              | Some x, Some y => R x y
              | None, None => True
              | _, _ => False
              end.
  Hint Unfold option_rel : core.

  Lemma option_rel_eq : forall {A : Type},
      eq_rel (@eq (option A)) (option_rel eq).
  Proof.
    intros ?; split; intros [] [] EQ; subst; try inv EQ; cbn; auto.
  Qed.

  Global Instance failT_Eq1 {E} : Eq1 (failT (itree E)) :=
    fun _ => eutt (option_rel eq).

  Global Instance Reflexive_failT_eq1 {E T} : Reflexive (@failT_Eq1 E T).
  Proof.
    apply Reflexive_eqit.
    intros []; auto.
  Qed.

  Global Instance Symmetric_failT_eq1 {E T} : Symmetric (@failT_Eq1 E T).
  Proof.
    apply Symmetric_eqit.
    intros [] []; auto.
  Qed.

  Global Instance Transitive_failT_eq1 {E T} : Transitive (@failT_Eq1 E T).
  Proof.
    apply Transitive_eqit.
    intros [] [] [] ? ?; subst; cbn in *; subst; intuition.
  Qed.

  Global Instance Equivalence_failT_eq1 {E T} : Equivalence (@failT_Eq1 E T).
  Proof.
    split; typeclasses eauto.
  Qed.

  Global Instance MonadLaws_failE {E} : MonadLawsE (failT (itree E)).
  Proof.
    split; cbn.
    - cbn; intros; rewrite Eq.bind_ret_l; reflexivity.
    - cbn; intros.
      rewrite <- (Eq.bind_ret_r x) at 2.
      eapply eutt_eq_bind; intros []; reflexivity.
    - intros; cbn; rewrite Eq.bind_bind.
      eapply eutt_eq_bind; intros []. 
      + eapply eutt_eq_bind; intros []; reflexivity. 
      + rewrite Eq.bind_ret_l; reflexivity.
    - repeat intro; cbn.
      eapply eutt_clo_bind; eauto.
      intros [] [] REL; cbn in *; subst; try intuition discriminate.
      rewrite H0; reflexivity.
      reflexivity.
  Qed.
  
End FailTLaws.

Hint Unfold option_rel : core.

(* Failure handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

Definition interp_fail {E M}
           {FM : Functor.Functor M} {MM : Monad M}
           {IM : MonadIter M} (h : E ~> failT M) :
  itree E ~> failT M := interp h.
Arguments interp_fail {_ _ _ _ _} h [T].

(* (** Unfolding of [interp_fail]. *) *)
Definition _interp_fail {E F R} (f : E ~> failT (itree F)) (ot : itreeF E R _)
  : failT (itree F) R :=
  match ot with
  | RetF r => ret r
  | TauF t => Tau (interp_fail f t)
  | VisF e k => bind (f _ e) (fun x => Tau (interp_fail f (k x)))
  end.

(** Unfold lemma. *)
Lemma unfold_interp_fail {E F R} (f : E ~> failT (itree F)) (t : itree E R) :
  interp_fail f t ≅
         (_interp_fail f (observe t)).
Proof.
  unfold interp_fail,interp. unfold Basics.iter, failT_iter, Basics.iter, MonadIter_itree. rewrite unfold_iter.
  destruct (observe t).
  cbn; repeat (rewrite ?Eq.bind_bind, ?Eq.bind_ret_l, ?bind_map; try reflexivity).
  cbn; repeat (rewrite ?Eq.bind_bind, ?Eq.bind_ret_l, ?bind_map; try reflexivity).
  cbn; repeat (rewrite ?Eq.bind_bind, ?Eq.bind_ret_l, ?bind_map; try reflexivity).
  apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros x ? <-]. 
  destruct x as [| x].
  - rewrite Eq.bind_ret_l; reflexivity.
  - rewrite Eq.bind_ret_l; reflexivity.
Qed.

Global Instance interp_fail_eq_itree {X E F} {R : X -> X -> Prop} (h : E ~> failT (itree F)) :
  Proper (eq_itree R ==> eq_itree (option_rel R)) (@interp_fail _ _ _ _ _ h X).
Proof.
  repeat red. 
  ginit.
  gcofix CIH.
  intros s t EQ.
  rewrite 2 unfold_interp_fail.
  punfold EQ; red in EQ.
  destruct EQ; cbn; subst; try discriminate; pclearbot; try (gstep; constructor; eauto with paco; fail).
  guclo eqit_clo_bind; econstructor; [reflexivity | intros x ? <-].
  destruct x as [x|]; gstep; econstructor; eauto with paco.
Qed.

(* Convenient special case: [option_rel eq eq] is equivalent to [eq], so we can avoid bothering *)
Global Instance interp_fail_eq_itree_eq {X E F} (h : E ~> failT (itree F)) :
  Proper (eq_itree eq ==> eq_itree eq) (@interp_fail _ _ _ _ _ h X).
Proof.
  repeat intro.
  rewrite option_rel_eq.
  apply interp_fail_eq_itree; auto.
Qed.

Global Instance interp_fail_eutt {X E F R} (h : E ~> failT (itree F)) :
  Proper (eutt R ==> eutt (option_rel R)) (@interp_fail _ _ _ _ _ h X).
Proof.
  repeat red. 
  einit.
  ecofix CIH.
  intros s t EQ.
  rewrite 2 unfold_interp_fail.
  punfold EQ; red in EQ.
  induction EQ; intros; cbn; subst; try discriminate; pclearbot; try (estep; constructor; eauto with paco; fail).
  - ebind; econstructor; [reflexivity |].
    intros [] [] EQ; inv EQ.
    + estep; ebase.
    + eret. 
  - rewrite tau_euttge, unfold_interp_fail; eauto.
  - rewrite tau_euttge, unfold_interp_fail; eauto.
Qed.

(* Convenient special case: [option_rel eq eq] is equivalent to [eq], so we can avoid bothering *)
Global Instance interp_fail_eutt_eq {X E F} (h : E ~> failT (itree F)) :
  Proper (eutt eq ==> eutt eq) (@interp_fail _ _ _ _ _ h X).
Proof.
  repeat intro.
  rewrite option_rel_eq.
  apply interp_fail_eutt; auto.
Qed.

Lemma interp_fail_tau {E F R} {f : E ~> failT (itree F)} (t: itree E R):
  eq_itree eq (interp_fail f (Tau t)) (Tau (interp_fail f t)).
Proof. rewrite unfold_interp_fail. reflexivity. Qed.

Lemma interp_fail_vis {E F : Type -> Type} {T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> failT (itree F)) 
  : interp_fail h (Vis e k) 
                ≅ h T e >>= fun mx =>
                              match mx with
                              | None => Ret None
                              | Some x => Tau (interp_fail h (k x))
                              end.
Proof.
  rewrite unfold_interp_fail. reflexivity.
Qed.

(* YZ: as with state, there is this tension between "inlining" the monad transformer
     in order to rewrite at the itree level, and develop the infrastructure to "properly"
     work in the transformed monad.
     With the former style, we pay by systematically exposing what should be handled internally
     (threading the state, checking on failure).
     With the latter, we need to be more rigorous with the infrastructure.
 *)
Lemma interp_fail_Ret : forall {X E F} (h : E ~> failT (itree F)) (x : X),
    interp_fail h (Ret x) ≅ Ret (Some x).
Proof.
  intros; rewrite unfold_interp_fail; reflexivity.
Qed.

Lemma interp_fail_ret : forall {X E F} (h : E ~> failT (itree F)) (x : X),
    interp_fail h (Ret x) ≅ ret (m := failT (itree F)) x.
Proof.
  intros; rewrite unfold_interp_fail; reflexivity.
Qed.

Lemma interp_fail_trigger {E F : Type -> Type} {R : Type}
      (e : E R) (f : E ~> failT (itree F)) 
  : interp_fail f (ITree.trigger e) ≈ f _ e.
Proof.
  unfold ITree.trigger. rewrite interp_fail_vis.
  match goal with
    |- ?y ≈ ?x => remember y; rewrite <- (bind_ret_r x); subst
  end.
  eapply eutt_eq_bind.
  intros []; try reflexivity; rewrite interp_fail_ret,tau_eutt.
  reflexivity.
Qed.

(* Inlined *)
Lemma interp_fail_bind : forall {X Y E F} (t : itree _ X) (k : X -> itree _ Y) (h : E ~> failT (itree F)),
    interp_fail h (ITree.bind t k) ≅
                ITree.bind (interp_fail h t)
                (fun mx => match mx with | None => ret None | Some x => interp_fail h (k x) end).
Proof.
  intros X Y; ginit; gcofix CIH; intros.
  rewrite unfold_bind.
  rewrite (unfold_interp_fail h t).
  destruct (observe t) eqn:EQ; cbn.
  - rewrite Eq.bind_ret_l. apply reflexivity.
  - cbn. rewrite bind_tau, !interp_fail_tau.
    gstep. econstructor; eauto with paco.
  - rewrite bind_bind, interp_fail_vis.
    guclo eqit_clo_bind; econstructor.
    reflexivity.
    intros [] ? <-; cbn.
    + rewrite bind_tau.
      gstep; constructor.
      auto with paco.
    + rewrite bind_ret_l.
      apply reflexivity.
Qed.

(* proper *)
Lemma interp_failure_bind' : forall {X Y E F} (t : itree _ X) (k : X -> itree _ Y) (h : E ~> failT (itree F)),
    interp_fail h (bind t k) ≅
                bind (interp_fail h t)
                (fun x => interp_fail h (k x)).
Proof.
  intros X Y E F; ginit; gcofix CIH; intros.
  cbn in *.
  rewrite unfold_bind, (unfold_interp_fail _ t).
  destruct (observe t) eqn:EQ; cbn.
  - rewrite bind_ret_l. apply reflexivity.
  - rewrite bind_tau, !interp_fail_tau.
    gstep. econstructor; eauto with paco.
  - rewrite bind_bind, interp_fail_vis.
    guclo eqit_clo_bind; econstructor.
    reflexivity.
    intros [] ? <-; cbn.
    + rewrite bind_tau.
      gstep; constructor.
      auto with paco.
    + rewrite bind_ret_l.
      apply reflexivity.
Qed.

