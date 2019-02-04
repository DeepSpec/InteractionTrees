Require Import ExtLib.Structures.Monads.
Require Import Paco.paco.

Import MonadNotation.
Open Scope monad_scope.

From ITree Require Import
     Core Fix.

Section M.
  (* The effects interface *)
  Variable IO : Type -> Type.

  Variable M : Type -> Type.
  Variable m : Monad M.

  (* A monadic "handler" for some effects E is just a mapping from
     the actions to monadic computations that return values of the
     right type. *)
  Variable handler : forall {X} (e:IO X), M X.

  (* "Weak" mfix *)
  Definition mfix_weak := forall A B, ((A -> M B) -> (A -> M B)) -> A -> M B.
  Variable mfix : mfix_weak.

  Definition run_weak {X} (t : itree IO X) : M X :=
            mfix (itree IO X) X
                   ( fun (f : (itree IO X -> M X)) =>
                       (fun (u : itree IO X) =>
                          match u.(observe) with
                          | RetF x => ret x
                          | TauF w => f w
                          | VisF e k =>
                            bind (handler _ e) (fun a => f (k a))
                          end)
                     ) t.

  (* "Parametric" mfix, tries to ensure that f is "monotone" *)
  Definition mfix_type := forall A B, (forall N `{Monad N} (inc:forall A, M A -> N A), ((A -> N B) -> (A -> N B))) -> A -> M B.
  Variable mfix_parametric : mfix_type.

  Definition run_parametric {X} (t : itree IO X) : M X :=
            mfix_parametric (itree IO X) X
                   ( fun N _ inc (f : (itree IO X -> N X)) =>
                       (fun (u : itree IO X) =>
                          match u.(observe) with
                          | RetF x => ret x
                          | TauF w => f w
                          | VisF e k =>
                            bind (inc _ (handler _ e)) (fun a => f (k a))
                          end)
                     ) t.

End M.


Section P.

  Definition P (A:Type) := A -> Prop.

  Definition ret_P {A} (a0:A) := fun (a1:A) =>  a1 = a0.
  Definition bind_P {A B} (m : P A) (f : A -> P B) : P B :=
    fun (b:B) => exists (a:A), m a /\ (f a b).

  Global Instance Monad_P : Monad P :=
    {
      ret := @ret_P ;
      bind := @bind_P ;
    }.

  Definition mfix_P {a b:Type} (f : ((a -> P b) -> (a -> P b))) : a -> P b :=
    @paco2 a (fun _ => b) f bot2.

  Lemma mfix_law1 : forall (a b : Type) f (x:a) (y:b), (@monotone2 a (fun _ => b) f) -> (mfix_P f x y) -> f (mfix_P f) x y.
  Proof.
    intros a b f x y Hm H.
    punfold H. unfold mfix_P. unfold upaco2 in H. unfold monotone2 in Hm.
    eapply Hm. apply H.
    intros. inversion PR. exact H0. inversion H0.
  Qed.

  Lemma mfix_law2 : forall (a b : Type) f (x:a) (y:b), (@monotone2 a (fun _ => b) f) -> f (mfix_P f) x y -> (mfix_P f x y).
  Proof.
    intros a b f x y Hm H.
    unfold mfix_P.
    pfold. unfold mfix_P in H. unfold monotone2 in Hm. eapply Hm. apply H.
    intros x0 x1 PR.
    left. exact PR.
  Qed.

  Definition run_P IO (handler : forall X, IO X -> P X) : forall X: Type, itree IO X -> P X :=
    @run_weak IO P _ handler (@mfix_P).

End P.

Section EX.

  Inductive IO : Type -> Type :=
  | Out : nat -> IO unit
  | In : IO nat.

  Definition handle_IO {X} (e:IO X) : P X :=
    match e with
    | Out n => fun _ => True
    | In => fun n => True
    end.

  Definition run := run_P IO (@handle_IO).

End EX.

Section SP.
  Variable state : Type.
  Definition SP (A:Type) := state -> (state * A) -> Prop.

  Definition ret_SP {A} (a0:A) : SP A := fun (st0:state) '(st1, a1) =>  a1 = a0 /\ st1 = st0.
  Definition bind_SP {A B} (m : SP A) (f : A -> SP B) : SP B :=
    fun (st0:state) => fun '(st2,b) => exists (st1:state) (a:A), m st0 (st1, a) /\ (f a st1 (st2, b)).

  Global Instance Monad_SP : Monad SP :=
    {
      ret := @ret_SP ;
      bind := @bind_SP ;
    }.

  Definition mfix_SP {a b:Type} (f : ((a -> SP b) -> (a -> SP b))) : a -> SP b :=
    @paco3 a (fun _ => state) (fun _ _ => (state * b)%type) f bot3.

  Lemma mfix_SP_law1 : forall (a b : Type) f (x:a) (y : state * b) st, monotone3 f -> (mfix_SP f x st y) -> f (mfix_SP f) x st y.
  Proof.
    intros a b f x y st Hm H.
    punfold H. unfold mfix_P. unfold upaco3 in H. unfold monotone3 in Hm.
    eapply Hm. apply H.
    intros. inversion PR. exact H0. inversion H0.
  Qed.

  Lemma mfix_SP_law2 : forall (a b : Type) f (x:a) (y:state * b) st, monotone3 f -> f (mfix_SP f) x st y -> (mfix_SP f x st y).
  Proof.
    intros a b f x y st Hm H.
    unfold mfix_SP.
    pfold. unfold mfix_SP in H. unfold monotone3 in Hm. eapply Hm. apply H.
    intros x0 x1 x2 PR.
    left. exact PR.
  Qed.

  Definition run_SP IO (handler : forall X, IO X -> SP X) : forall X: Type, itree IO X -> SP X :=
    @run_weak IO SP _ handler (@mfix_SP).

End SP.

Section EX2.
  (* The environment acts as a reference cell, but also provides a nondeterministic choice *)
  Inductive SIO : Type -> Type :=
  | Store : nat -> SIO unit   (* stores the nat in the cell *)
  | Load : SIO nat           (* reads the value of the cell *)
  | Undef : SIO nat          (* nondeterministic value *)
  .

  Definition handle_SIO {X} (e:SIO X) : SP nat X :=
    match e with
    | Store x => fun (st:nat) => fun '(st', a) => st' = x
    | Load => fun (st:nat) => fun '(st', a) => st = st' /\ st = a
    | Undef => fun (st:nat) => fun '(st', a) => st = st'
    end.

  Definition interp_SIO := run_SP _ (@SIO) (@handle_SIO).

  (* This could probably be factored out somehow *)
  Lemma monotone_body :
    monotone3
   (fun (f : itree SIO nat -> SP nat nat) (u : itree SIO nat) =>
    match u.(observe) with
    | RetF x => ret x
    | TauF w => f w
    | VisF e k => bind (handle_SIO e) (fun a => f (k a))
    end).
  Proof.
    unfold monotone3.
    intros x0 x1 x2 r r' IN LE.
    destruct x0.(observe).
    - apply IN.
    - apply LE. apply IN.
    - unfold bind in *. unfold Monad_SP in *. unfold bind_SP in *.
      destruct x2.
      destruct IN as [st1 [a [H1 H2]]].
      exists st1. exists a. split. exact H1. apply LE. exact H2.
  Qed.
  Hint Resolve monotone_body.


  Definition undef := ITree.liftE Undef.
  Definition store x := ITree.liftE (Store x).
  Definition load := ITree.liftE Load.

  Definition prog1 : itree SIO nat  :=
    x <- undef ;;
    store (x + x) ;;
    load.

  Definition prog2 : itree SIO nat  :=
    store 3 ;;
    x <- load ;;
    ret x.


  Lemma las : forall st st' a, interp_SIO nat prog2 st (st', a) -> a = 3.
  Proof.
    intros st st' a H.
    unfold interp_SIO in H.
    unfold run_SP in H.
    unfold run_weak in H.
    unfold mfix_SP in H.
    pinversion H.
    destruct H0 as [a0 [H1 H2]].
    simpl in H1.
    inversion H2.
    pinversion H2.
    destruct H0 as [a1 [[H31 H32] H4]].
    inversion H4.
    pinversion H4.
    simpl in H3. subst.
    reflexivity.
  Qed.

End EX2.


(*
Variable E: Type -> Type.

Check Fix.FixImpl.mfix.
Locate MonadFix.
Set Printing Universes.
Print mfix_type.
Print Monad_itree.
Definition mfix_itree : mfix_type (itree E) :=
  fun A B f => Fix.FixImpl.mfix (fun _ => B) (fun E' inc rec => f (itree E') (Monad_itree) inc rec).
*)
