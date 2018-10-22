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
     CoAlgebra Effect Eq.Eq.

From ITree Require ITree.

Set Implicit Arguments.
Set Contextual Implicit.

(* [St]: State type ([S] is already used by [nat].) *)
Variant output (E : Effect) (R : Type) (St : Type) : Type :=
| Ret : R -> output E R St
| Tau : St -> output E R St
| Vis : forall e : E, (reaction e -> St) -> output E R St
.

Arguments Ret {E R St}.
Arguments Tau {E R St}.
Arguments Vis {E R St}.

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
Inductive eq {E : Effect} {R : Type} (St1 St2 : Type)
          (eq_St : St1 -> St2 -> Prop) :
  output E R St1 -> output E R St2 -> Prop :=
| eq_Ret : forall r, eq eq_St (Ret r) (Ret r)
| eq_Tau : forall s1 s2,
    eq_St s1 s2 ->
    eq eq_St (Tau s1) (Tau s2)
| eq_Vis : forall e k1 k2,
    (forall x : reaction e, eq_St (k1 x) (k2 x)) ->
    eq eq_St (Vis e k1) (Vis e k2)
.

Global Instance Functor_output {E R} : Functor (output E R) := {|
  fmap _ _ := map;
|}.

Module Functor <: CoAlgebra.FunctorSig.
Parameter E : Effect.
Parameter R : Type.
Definition F : Type -> Type := output E R.
Instance Functor_F : Functor F := Functor_output.
Definition eq_F {St} : relation St -> relation (output E R St) :=
  fun eq_St => eq eq_St.
End Functor.

End Output.

(* Alternative to [itrees]. *)
Definition machine (E : Effect) (R : Type) : Type := nu (output E R).

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
Module ITreeFinalCoAlgebra <: FinalCoAlgebraSig (Output.Functor).
Import Output.Functor.
Module CA := CoAlgebra (Output.Functor).

Definition nu_F : Type := ITree.itree E R.

Definition eq_nu_F : relation nu_F := eq_itree.

Definition f_nu : nu_F -> F nu_F := fun t =>
  match t with
  | ITree.Ret r => Ret r
  | ITree.Tau t' => Tau t'
  | ITree.Vis e k => Vis e k
  end.

Definition f_nu' : F nu_F -> nu_F := fun t =>
  match t with
  | Ret r => ITree.Ret r
  | Tau t' => ITree.Tau t'
  | Vis e k => ITree.Vis e k
  end.

Lemma f_nu_morphism : CA.morphism eq_nu_F (eq_F eq_nu_F) f_nu.
Proof.
  intros a a' Eaa'; inversion Eaa'; constructor; auto.
Qed.

Definition ana {A} (f_A : A -> F A) :=
  cofix ana (a : A) :=
    match f_A a with
    | Ret r => ITree.Ret r
    | Tau a' => ITree.Tau (ana a')
    | Vis e k => ITree.Vis e (fun x => ana (k x))
    end.
(* cofix ana a := f_nu' (Output.map ana (f_A a)) *)

Lemma ana_morphism A (eq_A : relation A) (f_A : A -> F A)
      (f_A_coalgebra : CA.coalgebra eq_A f_A) :
  CA.morphism eq_A eq_nu_F (ana f_A).
Proof.
  cofix self.
  intros a a' Eaa'.
  rewrite (ITree.match_itree (ana _ a)).
  rewrite (ITree.match_itree (ana _ a')).
  simpl.
  specialize (f_A_coalgebra a a' Eaa').
  inversion f_A_coalgebra; constructor.
  - apply self; auto.
  - intro x; apply self; auto.
Qed.

Lemma ana_ca_morphism A (eq_A : relation A) (f_A : A -> F A)
      (f_A_coalgebra : CA.coalgebra eq_A f_A) :
  CA.ca_morphism eq_A eq_nu_F f_A f_nu (ana f_A).
Proof.
  intros a a' Eaa'.
  simpl.
  unfold Output.map.
  unfold Output.bind.
  pose proof (f_A_coalgebra a a' Eaa') as fac.
  inversion fac; constructor.
  - apply (ana_morphism f_A_coalgebra); auto.
  - intro x. apply (ana_morphism f_A_coalgebra); auto.
Qed.

Lemma ana_universal' A (eq_A : relation A)
      (Refl_A : Reflexive eq_A) (Sym_A : Symmetric eq_A)
      (f_A : A -> F A)
      (m : A -> nu_F)
      (f_A_coalgebra : CA.coalgebra eq_A f_A)
      (m_morphism : CA.morphism eq_A eq_nu_F m)
      (m_ca_morphism : CA.ca_morphism eq_A eq_nu_F f_A f_nu m) :
  forall (a a' : A) (Eaa' : eq_A a a') n,
    eq_nu_F n (m a) ->
    eq_nu_F n (ana f_A a').
Proof.
  cofix self.
  intros a a' Eaa' n Hn.
  unfold CA.morphism in m_morphism.
  rewrite (ITree.match_itree (ana _ _)).
  simpl.
  pose proof (f_A_coalgebra a a' Eaa') as faa'.
  specialize (m_ca_morphism a a' Eaa').
  symmetry in Eaa'.
  pose proof (f_A_coalgebra a' a Eaa') as fa'a.
  destruct (m a);
    inversion Hn;
    destruct (f_A a');
    inversion m_ca_morphism;
    destruct (f_A a);
    inversion faa';
    inversion fa'a;
    subst; constructor.
  - eapply self; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
  - intro y.
    inversion m_ca_morphism.
    repeat match goal with
           | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
             apply inj_pair2 in H
           | [H : _ |- _ ] => specialize (H y)
           end; subst.
    eapply self; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
Qed.

Lemma ana_universal A (eq_A : relation A)
      (Refl_A : Reflexive eq_A) (Sym_A : Symmetric eq_A)
      (f_A : A -> F A)
      (m : A -> nu_F)
      (f_A_coalgebra : CA.coalgebra eq_A f_A)
      (m_morphism : CA.morphism eq_A eq_nu_F m)
      (m_ca_morphism : CA.ca_morphism eq_A eq_nu_F f_A f_nu m) :
  forall (a a' : A) (Eaa' : eq_A a a'),
    eq_nu_F (m a) (ana f_A a').
Proof.
  intros.
  eapply ana_universal'; eauto.
Qed.

End ITreeFinalCoAlgebra.
