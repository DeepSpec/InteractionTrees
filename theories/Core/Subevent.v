(** * Extensible effects *)

(** Notations to handle large sums and classes for extensible effects. *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFacts
     Basics.Function
     Basics.FunctionFacts
     Core.ITreeDefinition
     Indexed.Sum
     Indexed.Function.

From ExtLib Require Import
     Monad.

Import MonadNotation.

(* end hide *)

Set Implicit Arguments.

(* Lifting of the [option] monad over indexed types *)
Inductive option1 (A : Type -> Type) X :Type :=
| None1
| Some1 (_: A X)
.
Arguments None1 {_ _}.
Arguments Some1 {_} [_].

Section Subevent.

  (**
     The [Subevent] typeclasse expresses the intuitive set inclusion over family of events.
     `A` is a subdomain of `B` if there is an injection from `A` into `B`.
   *)
  Class Subevent {A B : Type -> Type} : Type :=
    {   prj : B ~> option1 A
      ; inj : A ~> B
      ; prj_inj : forall {t} (a : A t), prj (inj a) = Some1 a
      ; inj_prj : forall {t} (b : B t) a, prj b = Some1 a -> inj a = b
    }.
  Arguments Subevent : clear implicits.
  Arguments prj {_ _ _} [_].
  Arguments inj {_ _ _} [_].

  (* Embedding of the subdomain into the bigger one *)
  Definition subeventV {A B} {V : Subevent A B} : A ~> B := inj.

End Subevent.

Arguments Subevent : clear implicits.
Arguments prj {_ _ _} [_].
Arguments inj {_ _ _} [_].

Section Trigger.

  (**
     The [Trigger M E] typeclass contains an operation that given
     an event [e] builds the "smallest" monadic value that executes [e].
   *)

  (* Temporary prime, to remove once the old trigger is scrapped off *)
  Class Trigger (E: Type -> Type) (M: Type -> Type) := trigger': E ~> M.
  (* Remark: could be a property of a family of monads instead: *)
  (* Class Trigger (M: (Type -> Type) -> Type -> Type) := *)
  (*   trigger': forall (E: Type -> Type) (X: Type), E X -> M E X. *)

End Trigger.

(**
   Generic lifting of an handler over a super-set of events.
   The [Subevent] typeclass gives us the partial inverse to call the handler on its domain.
   The [Trigger] typeclass gives us a way to otherwise embed the event into
   the monad of interest "in a minimal way".
 *)
Definition over {A B M : Type -> Type} {S:Subevent A B} {T:Trigger B M} (f : A ~> M) : B ~> M  :=
  fun t b => match prj b with
          | Some1 a => f _ a
          | None1  => trigger' _ b
          end.
Arguments over {_ _ _ _ _} _ [_] _.

(* Recovering the previous notion of effect inclusion. *)
Notation "A -< B" := (Subevent A B)
                       (at level 90, left associativity) : type_scope.

Definition subevent {E F : Type -> Type} `{E -< F} : E ~> F := subeventV.

(** A polymorphic version of [Vis]. *)
Notation vis e k := (Vis (subevent _ e) k).

(* Called [send] in Haskell implementations of Freer monads. *)
(* YZ: TODO: kill or change this notation? *)
Notation trigger e := (ITree.trigger (subevent _ e)).

(*************** Instances ***************)
Section Instances.

  Section Trigger_Instances.

    (* TODO: SZ: this is the place where [eqm] should be part of the monad equivalence.
       for M = itree we probably want to instantiate eqm as eutt or equiv
     *)
    (*
      YZ: Is it the place though? Shouldn't these concerns only show up when we reason about them rather than
      when building the monadic values?
     *)

    (* The minimal [itree] that performs [e] is [Vis e (fun x => Ret x)], already defined as [ITree.trigger] *)
    Instance Trigger_ITree {E} : Trigger E (itree E) := ITree.trigger.

    (* The [stateT] transformer relies on the trigger instance of its monad and simply pass away the state untouched *)
    Instance Trigger_State {S} {E} {M} `{Monad M} `{Trigger E M}: Trigger E (Monads.stateT S M) :=
      (fun T e s => t <- trigger' _ e ;; ret (s,t))%monad.

    (* The [PropT] transformer returns the propositional singleton of the underlying trigger.
       However, we might want this singleton to be up to some equivalence *)
    Instance Trigger_Prop {E} {M} `{Monad M} `{Trigger E M} (eqm : forall X, M X -> M X -> Prop) : Trigger E (fun X => M X -> Prop) :=
      (fun T e m => eqm _ m (trigger' _ e)).

  End Trigger_Instances.

  Section Subevent_Instances.

    (** Event level instances *)

    (* The subeffect relationship is reflexive: A -<  A *)
    Instance Subevent_refl {A} : Subevent A A.
    refine
      {| prj := Some1
         ; inj := fun _ x => x
      |}.
    auto.
    intros ? ? ? H; inversion H; auto.
    Defined.

    (* void1 is a subeffect of any type
       void1 -< A *)
    Instance Subevent_void {A}: Subevent void1 A.
    refine
      {| prj := fun _ _ => None1
         ; inj := fun t (x: void1 t) => match x with end
      |}.
    intros ? x; inversion x.
    intros ? ? x; inversion x.
    Defined.

    Instance Subevent_Assoc1 {A B C D: Type -> Type} `{Subevent (A +' (B +' C)) D}: Subevent ((A +' B) +' C) D.
    refine
      {| prj := fun _ d => match prj d with
                        | Some1 x => Some1 (assoc_l _ x)
                        | None1 => None1
                        end
         ; inj := fun _ x => inj (assoc_r _ x)
      |}.
    - intros t [[|]|]; cbn; rewrite prj_inj; cbn; auto.
    - intros t f e EQ.
      match type of EQ with
      | context[match ?x with | _ => _  end] => destruct x eqn:PROJ
      end; [inv EQ |].
      inv EQ.
      apply inj_prj in PROJ; subst.
      admit. (* assoc_r ∘  assoc_l ~ id *)
    Admitted.

    Instance Subevent_Assoc2 {A B C D: Type -> Type} `{Subevent A (B +' (C +' D))}: Subevent A ((B +' C) +' D).
    refine
      {| prj := fun _ d => prj (assoc_r _ d)
         ; inj := fun _ x => assoc_l _ (inj x) 
      |}.
    - intros t a.
      admit. (* assoc_r ∘  assoc_l ~ id *)
    - intros t f e EQ.
      apply inj_prj in EQ.
      rewrite EQ.
      admit. (* assoc_l ∘  assoc_r ~ id *)
    Admitted.


    (* Extends the domain to the left
       A -< B -> C +' A -< C +' B
     *)

    Instance Subevent_Sum_In {A B C: Type -> Type} `{A -< B} : C +' A -< C +' B.
    refine
      {|
        prj := fun _ cb =>
                     match cb with
                     | inl1 c =>  Some1 (inl1 c)
                     | inr1 b => match prj b with
                                | Some1 a => Some1 (inr1 a)
                                | None1 => None1
                                end
                     end
        ; inj := fun _ ca => match ca with
                         | inl1 c => inl1 c
                         | inr1 a => inr1 (inj a)
                         end
      |}.
      - intros t [x | y]; auto. 
        rewrite prj_inj; reflexivity.
      - intros t [|] ? EQ.
        + inv EQ; auto.
        + match type of EQ with
          | context[match ?x with | _ => _  end] => destruct x eqn:PROJ
          end; inv EQ.
          f_equal; apply inj_prj; auto.
    Defined.

    Instance Subevent_Sum_Out {A B C: Type -> Type} `{A -< B} : A -< C +' B.
    refine
      {|
        prj := fun _ cb =>
                 match cb with
                 | inl1 c => None1
                 | inr1 b => match prj b with
                            | Some1 a => Some1 a
                            | None1   => None1
                            end
                 end
        ; inj := fun _ a => inr1 (inj a)
      |}.
      - intros t a.
        rewrite prj_inj; reflexivity.
      - intros t [|] a EQ; [inv EQ |].
        match type of EQ with
        | context[match ?x with | _ => _  end] => destruct x eqn:PROJ
        end; inv EQ.
        f_equal; apply inj_prj; auto.
    Defined.

    Instance Subevent_Base_In {A B: Type -> Type} : A -< A +' B.
    refine
      {|
        prj := fun _ ab =>
                 match ab with
                 | inl1 a => Some1 a
                 | inr1 _ => None1
                 end
        ; inj := inl1
      |}.
      - auto.
      - intros t [|] ? EQ; inv EQ; auto.
    Defined.

  End Subevent_Instances.

End Instances.

Existing Instance Subevent_refl | 0.
Existing Instance Subevent_void | 0.
Existing Instance Subevent_Base_In | 0.
Existing Instance Subevent_Sum_In | 2.
Existing Instance Subevent_Sum_Out | 3.
Existing Instance Subevent_Assoc1 | 10.
Existing Instance Subevent_Assoc2 | 10.
Existing Instance Trigger_ITree | 1.
Existing Instance Trigger_State | 1.
Existing Instance Trigger_Prop  | 1.

Section Test.

  (* Small stress test: can we infer a view instance picking event domains 1 and 3 in a list? *)
  Variable A B C D: Type -> Type.
  Goal (A +' C) -< (A +' B +' C +' D).
    typeclasses eauto.
  Qed.

  (* Reassociation is fine *)
  Goal (A +' C) -< (A +' B) +' (C +' D).
    typeclasses eauto.
  Qed.

  (* Test for [over] *)
  Variable S: Type.
  Variable h: A ~> (* Monads.stateT S *) (itree void1).
  Typeclasses eauto := 4.
  (* This cannot work: the instances do not extend void1, i.e. do not alter the monad into which we trigger. Should it? *)
  Fail Goal forall {X} (e: (A +' B) X), over h e = over h e.

End Test.


(* Embedding events into trees.

   For example:
[[
   embed :
     (forall x y z,       E (f x y z)) ->
     (forall x y z, itree E (f x y z))
]]
 *)
Class Embeddable U V :=
  embed : U -> V.

Instance Embeddable_forall {A : Type} {U : A -> Type} {V : A -> Type}
         `(forall a, Embeddable (U a) (V a)) :
  Embeddable (forall a, U a) (forall a, V a) :=
  fun u a => embed (u a).

Instance Embeddable_itree {E F : Type -> Type} {R : Type}
         `(E -< F) :
  Embeddable (E R) (itree F R) :=
  fun e => trigger e.
