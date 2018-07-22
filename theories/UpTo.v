(* From interaction trees you can define semantics in an "up-to" style.
 * 
 * With interaction trees, you need to maintain the effects so the output
 * that you get is an inductive interaction tree with an extra
 * `Unknown`/`OutOfFuel` constructor. This is analagous to the need to
 * maintain the trace in a trace-based semantics.
 *)
Require Import Coq.Classes.RelationClasses.

Require Import ITree.ITree.
Require Import ITree.Effect.

Section with_effects.
  Variable E : Type -> Type.

  Inductive Eff {t : Type} : Type :=
  | Ret (_ : t)
  | Vis {u} (_ : E u) (_ : u -> Eff)
  | Unknown.
  Arguments Eff _ : clear implicits.

  (* `Approx a b` when `a` is a "prefix" of `b`
   *)
  Inductive Approx {t} : Eff t -> Eff t -> Prop :=
  | Approx_Any : forall b, Approx Unknown b
  | Approx_Ret : forall a, Approx (Ret a) (Ret a)
  | Approx_Vis : forall u (e : E u) k1 k2,
      (forall x, Approx (k1 x) (k2 x)) ->
      Approx (Vis e k1) (Vis e k2).

  Global Instance Reflexive_Approx {t} : Reflexive (@Approx t).
  Proof. compute. induction x; constructor; eauto. Qed.

  Lemma Approx_inj_Vis:
    forall (t : Type) (z : Eff t) (u : Type) (e : E u) (k2 : u -> Eff t),
      Approx (Vis e k2) z ->
      exists k : u -> Eff t, z = Vis e k /\ (forall x : u, Approx (k2 x) (k x)).
  Proof.
    intros t z u e k2 H1.
    refine
      match H1 in Approx a b
            return match a  return Prop with
                   | Vis e' k' => _
                   | _ => True
                   end
      with
      | Approx_Vis _ _ _ _ keq =>
        ex_intro _ _ (conj eq_refl keq)
      | _ => I
      end.
  Defined.

  Global Instance Transitive_Approx {t} : Transitive (@Approx t).
  Proof. compute. intros x y z H; revert z.
         induction H; simpl; intros; eauto; try econstructor.
         eapply Approx_inj_Vis in H1.
         destruct H1 as [ ? [ ? ? ] ].
         subst. constructor.
         intros. eapply H0. eauto.
  Qed.

End with_effects.

Arguments Eff _ _ : clear implicits.
Arguments Ret {_} [_] _.
Arguments Vis {_ _ _} _ _.
Arguments Unknown {_ _}.
Arguments Approx {_ _} _ _.

Section upto.
  Variable E : Type -> Type.

  Fixpoint upto {t} (n : nat) (i : itree E t) {struct n}
  : Eff E t :=
    match n with
    | 0 => Unknown
    | S n => match i with
            | ITree.Ret t => Ret t
            | ITree.Vis e k => Vis e (fun x => upto n (k x))
            | ITree.Tau k => upto n k
            end
    end.

  Lemma Approx_upto : forall n t (a : itree E t),
      Approx (upto n a) (upto (S n) a).
  Proof.
    induction n; simpl; intros.
    - constructor.
    - destruct a; try constructor; eauto.
  Qed.

  Lemma Approx_upto_strong
  : forall n m, n < m ->
           forall t (a : itree E t),
             Approx (upto n a) (upto m a).
  Proof.
    induction 1.
    - eapply Approx_upto.
    - intros. etransitivity. eapply IHle. eapply Approx_upto.
  Qed.

End upto.