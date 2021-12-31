(** * Shallow equivalence *)

(** Equality under [observe]:

[[
  observing eq t1 t2 <-> t1.(observe) = t2.(observe)
]]

  We actually define a more general relation transformer
  [observing] to lift arbitrary relations through [observe].
 *)

(* begin hide *)
From Coq Require Import Morphisms.

From ITree Require Import Core.ITreeDefinition.

Set Implicit Arguments.
(* end hide *)

Definition eqeq {A : Type} (P : A -> Type) {a1 a2 : A} (p : a1 = a2) : P a1 -> P a2 -> Prop :=
  match p with
  | eq_refl => eq
  end.

Definition pweqeq {R1 R2} (RR : R1 -> R2 -> Prop) {X1 X2 : Type} (p : X1 = X2)
  : (X1 -> R1) -> (X2 -> R2) -> Prop :=
  match p with
  | eq_refl => fun k1 k2 => forall x, RR (k1 x) (k2 x)
  end.

Lemma pweqeq_mon {R1 R2} (RR1 RR2 : R1 -> R2 -> Prop) X1 X2 (p : X1 = X2) k1 k2
  : (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) -> pweqeq RR1 p k1 k2 -> pweqeq RR2 p k1 k2.
Proof.
  destruct p; cbn; auto.
Qed.

Lemma eq_inv_VisF_weak {E R X1 X2} (e1 : E X1) (e2 : E X2) (k1 : X1 -> itree E R) (k2 : X2 -> itree E R)
  : VisF (R := R) e1 k1 = VisF (R := R) e2 k2 ->
    exists p : X1 = X2, eqeq E p e1 e2 /\ eqeq (fun X => X -> itree E R) p k1 k2.
Proof.
  refine (fun H =>
    match H in _ = t return
      match t with
      | VisF e2 k2 => _
      | _ => True
      end
    with
    | eq_refl => _
    end); cbn.
  exists eq_refl; cbn; auto.
Qed.

Ltac inv_Vis :=
  discriminate +
  match goal with
  | [ E : VisF _ _ = VisF _ _ |- _ ] =>
     apply eq_inv_VisF_weak in E; destruct E as [ <- [<- <-]]
  end.

(** ** [observing]: Lift relations through [observe]. *)
Record observing {E R1 R2}
           (eq_ : itree' E R1 -> itree' E R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) : Prop :=
  observing_intros
  { observing_observe : eq_ (observe t1) (observe t2) }.
#[global] Hint Constructors observing : itree.

Section observing_relations.

Context {E : Type -> Type} {R : Type}.
Variable (eq_ : itree' E R -> itree' E R -> Prop).

#[global]
Instance observing_observe_ :
  Proper (observing eq_ ==> eq_) (@observe E R).
Proof. intros ? ? []; cbv; auto. Qed.

#[global]
Instance observing_go : Proper (eq_ ==> observing eq_) (@go E R).
Proof. cbv; auto with itree. Qed.

#[global]
Instance monotonic_observing eq_' :
  subrelation eq_ eq_' ->
  subrelation (observing eq_) (observing eq_').
Proof. intros ? ? ? []; cbv; eauto with itree. Qed.

#[global]
Instance Equivalence_observing :
  Equivalence eq_ -> Equivalence (observing eq_).
Proof with (auto with itree).
  intros []; split; cbv...
  - intros ? ? []; auto...
  - intros ? ? ? [] []; eauto with itree.
Qed.

End observing_relations.

(** ** Unfolding lemmas for [bind] *)

#[global]
Instance observing_bind {E R S} :
  Proper (observing eq ==> eq ==> observing eq) (@ITree.bind E R S).
Proof.
  repeat intro; subst. constructor. unfold observe. cbn.
  rewrite (observing_observe H). reflexivity.
Qed.

Lemma bind_ret_ {E R S} (r : R) (k : R -> itree E S) :
  observing eq (ITree.bind (Ret r) k) (k r).
Proof. constructor; reflexivity. Qed.

Lemma bind_tau_ {E R} U t (k: U -> itree E R) :
  observing eq (ITree.bind (Tau t) k) (Tau (ITree.bind t k)).
Proof. constructor; reflexivity. Qed.

Lemma bind_vis_ {E R U V} (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  observing eq
    (ITree.bind (Vis e ek) k)
    (Vis e (fun x => ITree.bind (ek x) k)).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [aloop]. There is also a variant [unfold_aloop]
    without [Tau]. *)
Lemma unfold_aloop_ {E A B} (f : A -> itree E (A + B)) (x : A) :
  observing eq
    (ITree.iter f x)
    (ITree.bind (f x) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l)))).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [forever]. *)
Lemma unfold_forever_ {E R S} (t: itree E R):
  observing eq (@ITree.forever E R S t) (ITree.bind t (fun _ => Tau (ITree.forever t))).
Proof. econstructor. reflexivity. Qed.

(** ** [going]: Lift relations through [go]. *)

Inductive going {E R1 R2} (r : itree E R1 -> itree E R2 -> Prop)
          (ot1 : itree' E R1) (ot2 : itree' E R2) : Prop :=
| going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
#[global] Hint Constructors going : itree.

Lemma observing_going {E R1 R2} (eq_ : itree' E R1 -> itree' E R2 -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto with itree.
  intros [[]]; auto.
Qed.

Section going_relations.

Context {E : Type -> Type} {R : Type}.
Variable (eq_ : itree E R -> itree E R -> Prop).

#[global]
Instance going_go : Proper (going eq_ ==> eq_) (@go E R).
Proof. intros ? ? []; auto. Qed.

#[global]
Instance monotonic_going eq_' :
  subrelation eq_ eq_' ->
  subrelation (going eq_) (going eq_').
Proof. intros ? ? ? []; eauto with itree. Qed.

#[global]
Instance Equivalence_going :
  Equivalence eq_ -> Equivalence (going eq_).
Proof.
  intros []; constructor; cbv; eauto with itree.
  - intros ? ? []; auto with itree.
  - intros ? ? ? [] []; eauto with itree.
Qed.

End going_relations.
