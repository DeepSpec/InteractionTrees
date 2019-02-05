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
     Basics
     Core
     Morphisms
     MorphismsFacts
     Effect.Sum
     Eq.Eq Eq.UpToTaus.

(* The indexed type [D : Type -> Type] gives the signature of
   a set of functions. For example, a pair of mutually recursive
   [even : nat -> bool] and [odd : nat -> bool] can be declared
   as follows:

[[
   Inductive D : Type -> Type :=
   | Even : nat -> D bool
   | Odd  : nat -> D bool.
]]

   Their mutually recursive definition can then be written finitely
   (without [Fixpoint]):

[[
   Definition def : D ~> itree (D +' emptyE) := fun _ d =>
     match d with
     | Even n => match n with
                 | O => ret true
                 | S m => liftE (Odd m)
                 end
     | Odd n => match n with
                | O => ret false
                | S m => liftE (Even m)
                end
     end.
]]

   The function [interp_mutrec] below then ties the knot.

[[
   Definition f : D ~> itree emptyE :=
     interp_mutrec def.

   Definition even (n : nat) : itree emptyE bool := f _ (Even n).
   Definition odd  (n : nat) : itree emptyE bool := f _ (Odd n).
]]

   The result is still in the [itree] monad of possibly divergent
   computations, because [mutfix_itree] doesn't care whether
   the mutually recursive definition is well-founded.

 *)

(** Interpret an itree in the context of a mutually recursive
    definition ([ctx]). *)
Definition interp_mutrec {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
  fun R =>
    cofix mutfix_ (t : itree (D +' E) R) : itree E R :=
      handleF1 mutfix_
               (fun _ d k => Tau (mutfix_ (ctx _ d >>= k)))
               (observe t).

(** Unfold a mutually recursive definition into separate trees,
    resolving the mutual references. *)
Definition fix_mutrec {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : D ~> itree E :=
  fun R d => interp_mutrec ctx _ (ctx _ d).

Inductive callE (A B : Type) : Type -> Type :=
| Call : A -> callE A B B.

Arguments Call {A B}.

(* Interpret a single recursive definition. *)
Definition fix_rec {E : Type -> Type} {A B : Type}
           (body : A -> itree (callE A B +' E) B) :
  A -> itree E B :=
  fun a => fix_mutrec (fun _ call =>
    match call in callE _ _ T return itree (_ +' E) T with
    | Call a => body a
    end) _ (Call a).

(** Properties of [interp_mutrec] and [fix_mutrec]. *)
Section Facts.

Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

(** Unfolding of [interp_mutrec]. *)
Definition interp_mutrecF R :
  itreeF (D +' E) R _ -> itree E R :=
  handleF1 (interp_mutrec ctx R)
           (fun _ d k => Tau (interp_mutrec ctx _ (ctx _ d >>= k))).

Lemma unfold_interp_mutrecF R (t : itree (D +' E) R) :
  observe (interp_mutrec ctx _ t) = observe (interp_mutrecF _ (observe t)).
Proof. reflexivity. Qed.

Lemma unfold_interp_mutrec R (t : itree (D +' E) R) :
  eq_itree (interp_mutrec ctx _ t)
           (interp_mutrecF _ (observe t)).
Proof.
  rewrite itree_eta, unfold_interp_mutrecF, <-itree_eta.
  reflexivity.
Qed.

Lemma ret_mutrec {T} (x: T) :
  interp_mutrec ctx _ (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp_mutrec; reflexivity. Qed.

Lemma tau_mutrec {T} (t: itree _ T) :
  interp_mutrec ctx _ (Tau t) ≅ Tau (interp_mutrec ctx _ t).
Proof. rewrite unfold_interp_mutrec. reflexivity. Qed.

Lemma vis_mutrec_right {T U} (e : E U) (k : U -> itree (D +' E) T) :
  interp_mutrec ctx _ (Vis (inr1 e) k) ≅
  Vis e (fun x => interp_mutrec ctx _ (k x)).
Proof. rewrite unfold_interp_mutrec. reflexivity. Qed.

Lemma vis_mutrec_left {T U} (d : D U) (k : U -> itree (D +' E) T) :
  interp_mutrec ctx _ (Vis (inl1 d) k) ≅
  Tau (interp_mutrec ctx _ (ITree.bind (ctx _ d) k)).
Proof. rewrite unfold_interp_mutrec. reflexivity. Qed.

Hint Rewrite @ret_mutrec : itree.
Hint Rewrite @vis_mutrec_left : itree.
Hint Rewrite @vis_mutrec_right : itree.
Hint Rewrite @tau_mutrec : itree.

Instance eq_itree_mutrec {R} :
  Proper (@eq_itree _ R ==> @eq_itree _ R) (interp_mutrec ctx R).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite !unfold_interp_mutrec.
  pupto2_final.
  punfold H0. inv H0; pclearbot; [| |destruct e].
  - eapply eq_itree_refl.
  - pfold. econstructor. eauto.
  - pfold. econstructor. apply pointwise_relation_fold in REL.
    right. eapply CIH. rewrite REL. reflexivity.
  - pfold. econstructor. eauto 7.
Qed.

Theorem interp_mutrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mutrec ctx _ (ITree.bind t k) ≅
  ITree.bind (interp_mutrec ctx _ t) (fun x => interp_mutrec ctx _ (k x)).
Proof.
  intros. pupto2_init. revert t k.
  pcofix CIH. intros.
  rewrite (itree_eta t).
  destruct (observe t);
    [| |destruct e];
    autorewrite with itree;
    try rewrite <- bind_bind;
    pupto2_final.
  1: { apply eq_itree_refl. }
  all: try (pfold; econstructor; eauto).
Qed.

Let h_mutrec : D ~> itree E := fix_mutrec ctx.

Inductive mutrec_invariant {U} (c1 c2 : itree _ U) : Prop :=
| mutrec_main (d1 d2 : _ U)
    (Ed : eq_itree d1 d2)
    (Ec1 : eq_itree c1 (interp_mutrec ctx _ d1))
    (Ec2 : eq_itree c2 (interp1 (fix_mutrec ctx) _ d2)) :
    mutrec_invariant c1 c2
| mutrec_bind T (d : _ T) (k1 k2 : T -> itree _ U)
    (Ek : forall x, eq_itree (k1 x) (k2 x))
    (Ec1 : eq_itree c1 (interp_mutrec ctx _ (d >>= k1)))
    (Ec2 : eq_itree c2 (interp_mutrec ctx _ d >>= fun x =>
                        interp1 h_mutrec _ (k2 x))) :
    mutrec_invariant c1 c2
.

Lemma mutrec_invariant_init {U} (r : relation _)
      (INV : forall t1 t2, mutrec_invariant t1 t2 -> r t1 t2)
      (c1 c2 : itree _ U)
      (Ec : eq_itree c1 c2) :
  paco2 (compose eq_itreeF (gres2 eq_itreeF)) r
        (interp_mutrec ctx _ c1)
        (interp1 h_mutrec _ c2).
Proof.
  rewrite unfold_interp_mutrec, unfold_interp1.
  punfold Ec.
  inversion Ec; cbn; pclearbot; pupto2_final.
  + eapply eq_itree_refl. (* This should be reflexivity. *)
  + pfold; constructor. right; apply INV.
    eapply mutrec_main; [ eapply REL | |]; reflexivity.
  + destruct e.
    { pfold; constructor; cbn; right.
      apply INV. eapply mutrec_bind.
      - reflexivity.
      - cbn. reflexivity.
      - cbn. setoid_rewrite REL. reflexivity.
    }
    { pfold; econstructor.
      intros. right. apply INV.
      eapply mutrec_main; eauto; reflexivity.
    }
Qed.

Lemma mutrec_invariant_eq {U} (c1 c2 : itree _ U) :
  mutrec_invariant c1 c2 -> eq_itree c1 c2.
Proof.
  intro H; pupto2_init; revert c1 c2 H. pcofix self.
  intros c1 c2 [d1 d2 Ed Ec1 Ec2 | T d k1 k2 Ek Ec1 Ec2].
  - rewrite Ec1, Ec2.
    apply mutrec_invariant_init; auto.
  - rewrite Ec1, Ec2. cbn.
    rewrite unfold_interp_mutrec.
    rewrite (unfold_bind (interp_mutrec _ _ d)).
    unfold observe, _observe; cbn.
    destruct (observe d); fold_observe; cbn.
    + rewrite <- unfold_interp_mutrec.
      apply mutrec_invariant_init; auto.
    + pupto2_final; pfold; constructor; right.
      apply self.
      eapply mutrec_bind.
      * eapply Ek.
      * cbn; fold_bind; reflexivity.
      * cbn; fold_bind; reflexivity.
    + destruct e; cbn.
      * fold_bind. rewrite <-bind_bind.
        pupto2_final. pfold. econstructor. right.
        apply self.
        eapply mutrec_bind.
        ** apply Ek.
        ** cbn. reflexivity.
        ** cbn. reflexivity.
      * pupto2_final; pfold; constructor; right.
        apply self.
        eapply mutrec_bind.
        ++ eapply Ek.
        ++ cbn; fold_bind; reflexivity.
        ++ cbn; fold_bind; reflexivity.
Qed.

Theorem interp_mutrec_is_interp : forall {T} (c : itree _ T),
    eq_itree (interp_mutrec ctx _ c) (interp1 h_mutrec _ c).
Proof.
  intros.
  apply mutrec_invariant_eq.
  eapply mutrec_main; reflexivity.
Qed.

End Facts.
