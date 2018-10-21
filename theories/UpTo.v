(* From interaction trees you can define semantics in an "up-to" style.
 *
 * With interaction trees, you need to maintain the effects so the output
 * that you get is an inductive interaction tree with an extra
 * `Unknown`/`OutOfFuel` constructor. This is analagous to the need to
 * maintain the trace in a trace-based semantics.
 *)
Require Import Coq.Classes.RelationClasses.

Require Import ITree.ITree.
Require Import ITree.OpenSum.

Section with_effects.
  Variable E : Effect.

  Inductive Eff {t : Type} : Type :=
  | Ret (_ : t)
  | Vis (e : E) (_ : reaction e -> Eff)
  | Unknown.
  Arguments Eff _ : clear implicits.

  (* `EffLe a b` when `a` is a "prefix" of `b`
   *)
  Inductive EffLe {t} : Eff t -> Eff t -> Prop :=
  | EffLe_Any : forall b, EffLe Unknown b
  | EffLe_Ret : forall a, EffLe (Ret a) (Ret a)
  | EffLe_Vis : forall (e : E) k1 k2,
      (forall x, EffLe (k1 x) (k2 x)) ->
      EffLe (Vis e k1) (Vis e k2).

  Global Instance Reflexive_EffLe {t} : Reflexive (@EffLe t).
  Proof. compute. induction x; constructor; eauto. Qed.

  Lemma EffLe_inj_Vis:
    forall (t : Type) (z : Eff t) (e : E) (k2 : reaction e -> Eff t),
      EffLe (Vis e k2) z ->
      exists k : reaction e -> Eff t, z = Vis e k /\ (forall x : reaction e, EffLe (k2 x) (k x)).
  Proof.
    intros t z e k2 H1.
    refine
      match H1 in EffLe a b
            return match a  return Prop with
                   | Vis e' k' => _
                   | _ => True
                   end
      with
      | EffLe_Vis _ _ _ keq =>
        ex_intro _ _ (conj eq_refl keq)
      | _ => I
      end.
  Defined.

  Global Instance Transitive_EffLe {t} : Transitive (@EffLe t).
  Proof. compute. intros x y z H; revert z.
         induction H; simpl; intros; eauto; try econstructor.
         eapply EffLe_inj_Vis in H1.
         destruct H1 as [ ? [ ? ? ] ].
         subst. constructor.
         intros. eapply H0. eauto.
  Qed.

End with_effects.

Arguments Eff _ _ : clear implicits.
Arguments Ret {_} [_] _.
Arguments Vis {_ _} _ _.
Arguments Unknown {_ _}.
Arguments EffLe {_ _} _ _.

Section upto.
  Variable E : Effect.

  Inductive Approx {t} : itree E t -> Eff E t -> Prop :=
  | A_Unknown : forall it, Approx it Unknown
  | A_Ret     : forall v, Approx (ITree.Ret v) (Ret v)
  | A_Vis     : forall (e : E) k1 k2, (forall x, Approx (k1 x) (k2 x)) ->
                                       Approx (ITree.Vis e k1) (Vis e k2)
  | A_Tau     : forall it e, Approx it e -> Approx (ITree.Tau it) e.

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

  Theorem Approx_upto : forall t n (it : itree E t),
      Approx it (upto n it).
  Proof.
    induction n; simpl.
    - constructor.
    - destruct it; try constructor; eauto.
  Qed.

  Lemma EffLe_upto : forall n t (a : itree E t),
      EffLe (upto n a) (upto (S n) a).
  Proof.
    induction n; simpl; intros.
    - constructor.
    - destruct a; try constructor; eauto.
  Qed.

  Lemma EffLe_upto_strong
  : forall n m, n < m ->
           forall t (a : itree E t),
             EffLe (upto n a) (upto m a).
  Proof.
    induction 1.
    - eapply EffLe_upto.
    - intros. etransitivity. eapply IHle. eapply EffLe_upto.
  Qed.

End upto.
