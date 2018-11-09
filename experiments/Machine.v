(* We can view an [itree] as a generalized state machine,
   where at every step it either returns ([Ret]), steps silently
   ([Tau]), or perfoms some effect ([Vis]), moving to a new
   state depending on the environment's response. In other words,
   instead of a tree, we define a tuple
   [(S : Type, s : S, step : S -> output S)] for some functor
   [output] which is the sum of the above alternatives. *)

(* + No coinduction

   - Less efficiently executable (every [bind] grows the state type)
 *)

(* That tuple can be given the type
   [{ S : Type & S * (S -> output S) }], which is another
   representation of the final coalgebra of the functor [output].
   A basic theory of final coalgebras is in the module
   [ITree.CoAlgebra]. *)

From Coq Require Import
     Relations RelationClasses ProofIrrelevance.

From ExtLib.Structures Require Import
     Functor Applicative Monad.

From ITree Require Import
     Eq.Eq.

From ITree Require ITree.

From ITree.Experiments Require Import
     CoAlgebra.

Set Implicit Arguments.
Set Contextual Implicit.

(* [St]: State type ([S] is already used by [nat].) *)
Variant output (E : Type -> Type) (R : Type) (St : Type) : Type :=
| Ret : R -> output E R St
| Tau : St -> output E R St
| Vis : forall {u} (e : E u), (u -> St) -> output E R St
.

Arguments Ret {E R St}.
Arguments Tau {E R St}.
Arguments Vis {E R St _}.

Module Output.

(* Change the output state type using [f : St1 -> St2], and if
   the output is a [Ret q] for some [q : Q], get the output of
   the continuation [k q : output E R St2]. *)
Definition bind {St1 St2 E Q R}
           (f : St1 -> St2)
           (o : output E Q St1)
           (k : Q -> output E R St2) : output E R St2 :=
  match o with
  | Ret q => k q
  | Tau s => Tau (f s)
  | Vis e h => Vis e (fun x => f (h x))
  end.

(* Change the output state type. *)
Definition map {St1 St2 E R}
           (f : St1 -> St2)
           (o : output E R St1) : output E R St2 :=
  bind f o Ret.

(* Equivalence of outputs, lifting equivalence of states. *)
Inductive eq {E : Type -> Type} {R : Type} (St1 St2 : Type)
          (eq_St : St1 -> St2 -> Prop) :
  output E R St1 -> output E R St2 -> Prop :=
| eq_Ret : forall r, eq eq_St (Ret r) (Ret r)
| eq_Tau : forall s1 s2,
    eq_St s1 s2 ->
    eq eq_St (Tau s1) (Tau s2)
| eq_Vis : forall {u} e k1 k2,
    (forall x : u, eq_St (k1 x) (k2 x)) ->
    eq eq_St (Vis e k1) (Vis e k2)
.

Global Instance Functor_output {E R} : Functor (output E R) := {|
  fmap _ _ := map;
|}.

Module Functor <: CoAlgebra.EndoFunctor CoAlgebra.SetoidCategory.
Import CoAlgebra.SetoidCategory CoAlgebra.SetoidCategory.Types.

Parameter E : Type -> Type.
Parameter R : Type.

Definition eq_F {St} : relation St -> relation (output E R St) :=
  fun eq_St => eq eq_St.

Ltac inj_pairs :=
  repeat (
    match goal with
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
      apply inj_pair2 in H
    end; subst).

Instance Equivalence_eq St (eq_St : relation St)
         `{Equivalence _ eq_St} :
  Equivalence (eq eq_St : relation (output E R St)).
Proof.
  constructor.
  - intros []; constructor; reflexivity.
  - intros [] [] E; inversion E; subst; inj_pairs;
      constructor; intros; symmetry; auto.
  - intros [] [] [] E1 E2; inversion E1; subst; inj_pairs;
      inversion E2; subst; inj_pairs;
        constructor; intros; etransitivity;
        eauto.
Qed.

Canonical Structure F (St : object) : object := {|
    carrier := output E R (carrier St);
    equiv := eq_F (equiv St);
    equiv_equiv := @Equivalence_eq _ _ (equiv_equiv St);
  |}.

Lemma equiv_map A B (a : A --> B) (x x' : F A) :
  x == x' -> map a x == map a x'.
Proof.
  intros []; constructor; intros; apply a; auto.
Qed.

Definition F_map A B (a : A --> B) : F A --> F B := {|
    apply := map (apply a);
    equiv_apply := @equiv_map _ _ _;
  |}.

Lemma F_id A : F_map (@id A) =~ id.
Proof.
  intros x x' []; simpl; constructor; auto.
Qed.

Lemma F_compose A B C (a : A --> B) (b : B --> C) :
  F_map (a * b) =~ F_map a * F_map b.
Proof.
  intros x x' []; simpl; constructor; intros; apply b, a; auto.
Qed.

End Functor.

End Output.

(* Alternative to [itrees]. *)
Definition machine (E : Type -> Type) (R : Type) : Type := nu (output E R).

Module Machine.

(* Two machines are equivalent if they simulate each other
   (produce the same outputs). *)
Definition eq {E R} : machine E R -> machine E R -> Prop :=
  Nu.eq Output.eq.

(* The state type of a machine. *)
Definition type {E R} : machine E R -> Type :=
  Nu.type.

(* The initial state of a machine. *)
Definition state {E R} (m : machine E R) : Machine.type m :=
  Nu.state m.

(* The step function of a machine. *)
Definition step {E R} (m : machine E R) :
  Machine.type m -> output E R (Machine.type m) :=
  Nu.step m.

(* Run the first step of a machine. *)
Definition step_once {E R} (m : machine E R) :
  output E R (Machine.type m) :=
  Nu.step_once m.

Lemma step_state {E R} (m : machine E R) :
  step m (state m) = step_once m.
Proof. apply Nu.step_state. Qed.

(* Can't write [machine E R -> output E R (machine E R)] because
   of universe inconsistency... *)
Definition run {E R} :
  nu (output E R) -> output E R (nu (output E R)) :=
  Nu.run.

(*
Definition run2 {E R} :
  nu (output E R) -> output E R (machine E R) :=
  Nu.run.
*)

Definition ret {E R} (r : R) : machine E R :=
  Nu tt (fun _ => Ret r).

Definition bind {E Q R}
           (m : machine E Q) (k : Q -> machine E R) :=
  let mtype :=
      (Machine.type m + { q : Q & Machine.type (k q) })%type in
  let mstate := inl (Machine.state m) in
  let wrap_sk (q : Q) (s : Machine.type (k q)) : mtype :=
      inr (existT _ q s) in
  let mstep (s : mtype) :=
      match s with
      | inl sm => Output.bind inl
          (Machine.step m sm)
          (fun q => Output.map (wrap_sk q) (Machine.step_once (k q)))
      | inr (existT _ q sk) =>
        Output.map (wrap_sk q) (Machine.step (k q) sk)
      end in
  Nu mstate mstep.

Global Instance Monad_machine {E} : Monad (machine E) := {|
  Monad.ret _ := ret;
  Monad.bind _ _ := bind;
|}.

End Machine.

Module ITreeEquivalence.

Definition to_itree {E R} (m : machine E R) : ITree.itree E R :=
  match m with
  | Nu s t =>
    (cofix ana s :=
       match t s with
       | Ret r => ITree.Ret r
       | Tau s' => ITree.Tau (ana s')
       | Vis e k => ITree.Vis e (fun x => ana (k x))
       end) s
  end.

(* universe inconsistency :(
CoFixpoint to_itree {E R} (m : machine E R) : ITree.itree E R :=
  match Machine.run m with
  | Ret r => ITree.Ret r
  | Tau m' => ITree.Tau (to_itree m')
  | Vis e k => ITree.Vis e (fun x => to_itree (k x))
  end.
*)

Definition from_itree {E R} (t : ITree.itree E R) : machine E R :=
  Nu t (fun t =>
          match t with
          | ITree.Ret r => Ret r
          | ITree.Tau t' => Tau t'
          | ITree.Vis e k => Vis e k
          end).

End ITreeEquivalence.

(* ITree as the final [output]-coalgebra. *)
Module ITreeFinalCoAlgebra <:
  FinalCoAlgebra SetoidCategory Output.Functor.
Import SetoidCategory Output.Functor.
Module Import CA := CoAlgebra SetoidCategory Output.Functor.

Section Object.
Import Types.

Canonical Structure nu_F_obj : object := {|
    carrier := ITree.itree E R;
  |}.

Definition f_nu_apply : nu_F_obj -> F nu_F_obj :=
  fun t =>
    match t with
    | ITree.Ret r => Ret r
    | ITree.Tau t' => Tau t'
    | ITree.Vis e k => Vis e k
    end.

Definition f_nu_apply' : F nu_F_obj -> nu_F_obj := fun t =>
  match t with
  | Ret r => ITree.Ret r
  | Tau t' => ITree.Tau t'
  | Vis e k => ITree.Vis e k
  end.

Lemma equiv_f_nu (a a' : nu_F_obj) :
  a == a' -> f_nu_apply a == f_nu_apply a'.
Proof.
  intros []; constructor; auto.
Qed.

Definition f_nu : nu_F_obj --> F nu_F_obj := {|
    apply := f_nu_apply;
    equiv_apply := equiv_f_nu;
  |}.

End Object.

Definition nu_F : coalgebra := {|
    carrier := nu_F_obj;
    ops := f_nu;
  |}.

Section Ana.
Import Types.

Definition ana_apply (A : object) (f_A : A -> F A) :=
  cofix ana (a : A) :=
    match f_A a with
    | Ret r => ITree.Ret r
    | Tau a' => ITree.Tau (ana a')
    | Vis e k => ITree.Vis e (fun x => ana (k x))
    end.
(* cofix ana a := f_nu' (Output.map ana (f_A a)) *)

Lemma equiv_ana_apply (A : coalgebra) :
  forall a a',
    a == a' -> ana_apply (ops A) a == ana_apply (ops A) a'.
Proof.
  cofix self.
  intros a a' Eaa'.
  rewrite (ITree.match_itree (ana_apply _ a)).
  rewrite (ITree.match_itree (ana_apply _ a')).
  simpl.
  pose proof (equiv_apply (ops A) a a' Eaa') as equiv.
  inversion equiv; constructor.
  - apply self; auto.
  - intro x; apply self; auto.
Qed.

Definition ana_morphism (A : coalgebra) :
  CA.carrier A --> CA.carrier nu_F := {|
    apply := ana_apply _;
    equiv_apply := equiv_ana_apply _;
  |}.

Lemma comm_ana_morphism (A : coalgebra) :
      ops A * F_map (ana_morphism A) =~ ana_morphism A * ops nu_F.
Proof.
  intros a a' Eaa'.
  simpl.
  unfold Output.map.
  unfold Output.bind.
  pose proof (equiv_apply (ops A) a a' Eaa') as fac.
  inversion fac; constructor.
  - apply (ana_morphism A); auto.
  - intro x. apply (ana_morphism A); auto.
Qed.

Definition ana (A : coalgebra) : A ~~> nu_F := {|
    morphism := ana_morphism A;
    comm := comm_ana_morphism A;
  |}.

Lemma ana_final' (A : coalgebra) (m : A ~~> nu_F) :
  forall (a a' : CA.carrier A) (Eaa' : a == a') n,
    n == morphism m a ->
    n == morphism ana a'.
Proof.
  cofix self.
  intros a a' Eaa' n Hn.
  pose proof (equiv_apply (morphism m)) as m_morphism.
  rewrite (ITree.match_itree (morphism ana _)).
  simpl.
  pose proof (equiv_apply (ops A) a a' Eaa') as faa'.
  pose proof (comm m a a' Eaa') as m_ca_morphism.
  pose proof (equiv_equiv (CA.carrier A)) as EquivA.
  pose proof (m_morphism _ _ Eaa') as Emaa'.
  simpl in *.
  symmetry in Eaa'.
  pose proof (equiv_apply (ops A) a' a Eaa') as fa'a.
  simpl in *. unfold Output.map, Output.bind in *. simpl in *.
  destruct (ops A a');
    destruct (ops A a);
    inversion faa';
    inversion fa'a;
    destruct (@apply _ nu_F_obj (morphism m) a);
    inversion Hn;
    destruct (@apply _ nu_F_obj (morphism m) a'); simpl in *;
    inversion Emaa';
    inversion m_ca_morphism;
    inj_pairs;
    constructor.
  - eapply self; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
    symmetry; auto.
  - intro y.
    inversion m_ca_morphism.
    inversion Emaa'.
    inj_pairs;
    repeat match goal with
           | [H : _ |- _ ] => specialize (H y)
           end; subst.
    eapply self; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
    symmetry; auto.
Qed.

Lemma ana_final A (m : A ~~> nu_F) : m =~ ana.
Proof.
  intros a a' Eaa'; eapply ana_final'; eauto. reflexivity.
Qed.

(* Failed naive attempt. *)
Lemma ana_final_failed A (m : A ~~> nu_F) : m =~ ana.
Proof.
  cofix self.
  intros a a' Eaa'.
  pose proof (equiv_apply (morphism m)) as m_morphism.
  rewrite (ITree.match_itree (morphism ana _)).
  simpl.
  pose proof (equiv_apply (ops A) a a' Eaa') as faa'.
  pose proof (comm m a a' Eaa') as m_ca_morphism.
  pose proof (equiv_equiv (CA.carrier A)) as EquivA.
  pose proof (m_morphism _ _ Eaa') as Emaa'.
  simpl in *.
  symmetry in Eaa'.
  pose proof (equiv_apply (ops A) a' a Eaa') as fa'a.
  simpl in *. unfold Output.map, Output.bind in *. simpl in *.
  destruct (ops A a');
    destruct (ops A a);
    inversion faa';
    inversion fa'a;
    destruct (@apply _ nu_F_obj (morphism m) a);
    destruct (@apply _ nu_F_obj (morphism m) a'); simpl in *;
    inversion Emaa';
    inversion m_ca_morphism;
    inj_pairs;
    constructor.
  - subst.
    etransitivity; eauto.
    symmetry in H10; etransitivity; eauto.
    apply self; auto.
    (* Unguarded: Coinductive hypothesis as an argument
       to transitivity lemma. *)
  - intro y.
    inversion m_ca_morphism.
    inversion Emaa'.
    inj_pairs;
    repeat match goal with
           | [H : _ |- _ ] => specialize (H y)
           end; subst.
    etransitivity; eauto.
    symmetry in H1; etransitivity; eauto.
    apply self; auto. (* Unguarded. *)
(* Fail Qed. *)
Abort.

End Ana.

End ITreeFinalCoAlgebra.
