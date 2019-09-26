(** * Extensible effects *)

(** Notations to handle large sums and classes for extensible effects. *)

From Coq Require Import
     Setoid Morphisms.

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
     Indexed.Function
     Indexed.FunctionFacts
.

(* Want to import Indexed.FunctionFacts *)
From ExtLib Require Import
     Monad.

Import MonadNotation.
Import CatNotations.
Open Scope cat_scope.

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

  (* Isomorphism:  B <~> (A +' C) *)
  Class Subevent {A B C : Type -> Type} : Type :=
    {
      split_E : B ~> A +' C ;
      merge_E : (A +' C) ~> B
    }.

  Class Subevent_wf {A B C} (sub: @Subevent A B C): Prop :=
      {
        sub_iso : Iso _ split_E merge_E
      }.

  Arguments Subevent : clear implicits.
  Arguments split_E {_ _ _ _} [_].
  Arguments merge_E {_ _ _ _} [_].
  Definition inj1 {A B C} `{Subevent A B C} : A ~> B :=  inl_ >>> merge_E.
  Definition inj2 {A B C} `{Subevent A B C} : C ~> B :=  inr_ >>> merge_E.
  Definition case  {A B C} `{Subevent A B C} : B ~> (A +' C) := split_E.
End Subevent.

(*

  (**
     The [Subevent] typeclasse expresses the intuitive set inclusion over family of events.
     `A` is a subdomain of `B` if there is an injection from `A` into `B`.
   *)
  Class Subevent {A B C : Type -> Type} : Type :=
    {   prj : B ~> A +' C
      ; inj : A ~> B
      ; prj_inj : forall {t} (a : A t), prj (inj a) = inl1 a
      ; inj_prj : forall {t} (b : B t) a, prj b = inl1 a -> inj a = b
      ; inj_prj : forall {t} (b : B t) a, prj b = inl1 a -> inj a = b
    }.
  Arguments Subevent : clear implicits.
  Arguments prj {_ _ _} [_].
  Arguments inj {_ _ _} [_].

  (* Embedding of the subdomain into the bigger one *)
  Definition subeventV {A B} {V : Subevent A B} : A ~> B := inj.

*)
Arguments Subevent : clear implicits.
Arguments case {_ _ _ _} [_].
Arguments inj1 {_ _ _ _} [_].
Arguments inj2 {_ _ _ _} [_].



Section Trigger.

  (**
     The [Trigger M E] typeclass contains an operation that given
     an event [e] builds the "smallest" monadic value that executes [e].
   *)

  (* Temporary prime, to remove once the old trigger is scrapped off
     Trigger E
(itree E): Type -> Type
itree:(Type -> Type) -> Type -> Type
     Trigger itree
   *)
  Class Trigger (E: Type -> Type) (M: Type -> Type) := trigger: E ~> M.
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
Definition over {A B C M : Type -> Type} {S:Subevent A B C} {T:Trigger C M} (f : A ~> M) : B ~> M  :=
  fun t b =>  match case b with
           | inl1 a => f _ a
           | inr1 c => trigger _ c
           end.

Arguments over {_ _ _ _ _ _} _ [_] _.


(* Recovering the previous notion of effect inclusion. *)
Notation "A +? C -< B" := (Subevent A B C)
                       (at level 90, left associativity) : type_scope.
(*
Definition subevent {E F : Type -> Type} `{E -< F} : E ~> F := subeventV.
*)

(*
(** A polymorphic version of [Vis]. *)
Notation vis e k := (Vis (subevent _ e) k).

(* Called [send] in Haskell implementations of Freer monads. *)
(* YZ: TODO: kill or change this notation? *)
Notation trigger e := (ITree.trigger (subevent _ e)).
 *)

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
      (fun T e s => t <- trigger _ e ;; ret (s,t))%monad.

    (* The [PropT] transformer returns the propositional singleton of the underlying trigger.
       However, we might want this singleton to be up to some equivalence *)
    Instance Trigger_Prop {E} {M} `{Monad M} `{Trigger E M} : Trigger E (fun X => M X -> Prop) :=
      (fun T e m => m = (trigger _ e)).

  End Trigger_Instances.

  Section Subevent_Instances.

    (** Event level instances *)
    (* A ~> A +' void1
       A +' void1 ~> A
     *)
    (* The subeffect relationship is reflexive: A -<  A *)
    Instance Subevent_refl {A : Type -> Type} : A +? void1 -< A :=
      {| split_E := inl_: IFun _ _
         ; merge_E := unit_r: IFun _ _
      |}.

    Instance Subevent_void {A : Type -> Type} : void1 +? A -< A :=
      {| split_E := inr_: IFun _ _
         ; merge_E := unit_l: IFun _ _
      |}.

    (* Extends the domain to the left
       A -< B -> C +' A -< C +' B
     *)
    Instance Subevent_Sum_In {A B C D: Type -> Type} `{A +? D -< B} : (C +' A) +? D -< C +' B :=
      {|
        split_E := case_ (inl_ >>> inl_) (split_E >>> bimap inr_ (id_ _));
        merge_E := assoc_r >>> bimap (id_ _) merge_E
      |}.

    Instance Subevent_Sum_Out {A B C D: Type -> Type}
             `{A +? D -< B} : A +? C +' D -< C +' B :=
      {|
        split_E := case_ (inl_ >>> inr_) (split_E >>> bimap (id_ _) inr_)
        ; merge_E := case_ (inl_ >>> merge_E >>> inr_) (bimap (id_ _) (inr_ >>> merge_E))
      |}.

    Instance Subevent_Base {A B}: A +? B -< A +' B :=
      {|
        split_E := id_ _;
        merge_E := id_ _
      |}.

    Instance Subevent_Assoc1 {A B C D E: Type -> Type} `{Subevent (A +' (B +' C)) D E} : Subevent ((A +' B) +' C) D E :=
      {| split_E := split_E >>> case_ (assoc_l >>> inl_) inr_
         ; merge_E := bimap assoc_r (id_ _) >>> merge_E
      |}.

    Instance Subevent_Assoc2 {A B C D E: Type -> Type}
      `{A +? E -< (B +' (C +' D))}: A +? E -< ((B +' C) +' D) :=
        {| split_E := assoc_r >>> split_E
           ; merge_E := merge_E >>> assoc_l
        |}.

    Instance Subevent_Assoc3 {A B C D E: Type -> Type}
       `{A +? (B +' (C +' D)) -< E} : A +? ((B +' C) +' D) -< E :=
      {| split_E := split_E >>> (bimap (id_ _) assoc_l)
          ; merge_E := (bimap (id_ _) assoc_r) >>> merge_E
      |}.

    (**
       Well-formedness of the instances: each subevent instance defines an isomorphism.
     *)

    Instance Subevent_refl_wf {A : Type -> Type} : @Subevent_wf A _ _ Subevent_refl.
    constructor; split.
    - cbv; reflexivity.
    - cbv; intros ? [? | []]; reflexivity.
    Qed.

    Instance Subevent_void_wf {A : Type -> Type} : @Subevent_wf _ A _ Subevent_void.
    constructor; split.
    - cbv; reflexivity.
    - cbv. intros ? [[] | ?]; reflexivity.
    Qed.

    Instance Subevent_Base_wf {A B: Type -> Type} : Subevent_wf (@Subevent_Base A B).
    constructor; split; cbv; reflexivity.
    Qed.

    Instance Subevent_Assoc1_wf {A B C D E: Type -> Type}
             {Sub: (A +' B +' C) +? E -< D}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Assoc1 A B C D E Sub).
    constructor; split.
    - cbn.
      apply SemiIso_Cat.
      apply SubWf.
      unfold SemiIso.
      rewrite cat_case.
      rewrite cat_assoc, inl_bimap.
      rewrite <- cat_assoc, assoc_l_mono, cat_id_l.
      rewrite inr_bimap, cat_id_l.
      rewrite <- case_eta.
      reflexivity.
    - cbn. apply SemiIso_Cat.
      2 : apply SubWf.
      unfold SemiIso.
      rewrite bimap_case.
      rewrite cat_id_l.
      rewrite <- cat_assoc, assoc_r_mono.
      rewrite cat_id_l.
      rewrite <- case_eta.
      reflexivity.
    Qed.

    Instance Subevent_Assoc2_wf {A B C D E: Type -> Type}
             {Sub: A +? E -< (B +' (C +' D))}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Assoc2 A B C D E Sub).
    Proof.
      constructor; split.
      - cbn.
        apply SemiIso_Cat, SubWf.
        unfold SemiIso.
        rewrite assoc_r_mono; reflexivity.
      - cbn.
        apply SemiIso_Cat.
        apply SubWf.
        unfold SemiIso.
        rewrite assoc_l_mono; reflexivity.
    Qed.

    Instance Subevent_Assoc3_wf {A B C D E: Type -> Type}
             {Sub: A +? (B +' (C +' D)) -< E}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Assoc3 A B C D E Sub).
    Proof.
      constructor; split.
      - cbn.
        apply SemiIso_Cat. apply SubWf.
        apply SemiIso_Bimap.
        apply SemiIso_Id.
        apply AssocLMono_Coproduct.
      - cbn.
        apply SemiIso_Cat.
        apply SemiIso_Bimap.
        apply SemiIso_Id.
        apply AssocRMono_Coproduct.
        apply SubWf.
    Qed.

    Instance Subevent_Sum_In_wf {A B C D: Type -> Type}
             {Sub: A +? D -< B}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Sum_In A B C D Sub).
    Proof.
      constructor; split.
      - cbn.
        unfold SemiIso.
        rewrite cat_case.
        rewrite <- cat_assoc, (cat_assoc inl_ inl_), inl_assoc_r.
        do 2 rewrite inl_bimap, cat_id_l.
        rewrite <- inr_assoc_l. 
        rewrite ! cat_assoc, <- (cat_assoc _ assoc_r _), assoc_l_mono, cat_id_l.
        rewrite inr_bimap, <- cat_assoc.
        rewrite semi_iso; [| apply SubWf].
        rewrite cat_id_l, case_eta.
        reflexivity.
      - cbn.
        unfold SemiIso.
        rewrite cat_assoc, bimap_case, cat_id_l.
        rewrite <- cat_assoc.
        rewrite (@semi_iso _ _ _ _ _ _ _ merge_E split_E); [| apply SubWf].
        rewrite cat_id_l.
        unfold assoc_r, AssocR_Coproduct.
        rewrite cat_case.
        rewrite cat_assoc, case_inr.
        rewrite cat_case.
        rewrite cat_assoc, case_inr, case_inl.
        rewrite inr_bimap, inl_bimap, cat_id_l.
        rewrite <- case_eta', <- case_eta.
        reflexivity.
    Qed.

    Instance Subevent_Sum_Out_wf {A B C D: Type -> Type}
             {Sub: A +? D -< B}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Sum_Out A B C D Sub).
    Proof.
      constructor; split.
      - cbn.
        unfold SemiIso.
        rewrite cat_case.
        rewrite cat_assoc, inr_case, inl_bimap, cat_id_l.
        rewrite cat_assoc, bimap_case, cat_id_l.
        rewrite inr_bimap.
        rewrite 2 cat_assoc, <- cat_case, <- case_eta, cat_id_l.
        rewrite <- cat_assoc, semi_iso; [| apply SubWf].
        rewrite cat_id_l, <- case_eta.
        reflexivity.
      - cbn.
        unfold SemiIso.
        rewrite cat_case.
        rewrite 2 cat_assoc, inr_case.
        rewrite <- (cat_assoc _ split_E _), semi_iso; [| apply SubWf].
        rewrite cat_id_l, inl_bimap, cat_id_l.
        rewrite bimap_case, cat_id_l.
        rewrite <- cat_assoc, (cat_assoc _ merge_E _), semi_iso; [| apply SubWf].
        rewrite cat_id_r, inr_bimap, <- case_eta', <- case_eta.
        reflexivity.
    Qed.

  End Subevent_Instances.

End Instances.

Existing Instance Subevent_refl | 0.
Existing Instance Subevent_void | 0.
Existing Instance Subevent_Base | 0.
Existing Instance Subevent_Sum_In | 2.
Existing Instance Subevent_Sum_Out | 3.
Existing Instance Subevent_Assoc1 | 10.
Existing Instance Subevent_Assoc2 | 10.
Existing Instance Trigger_ITree | 1.
Existing Instance Trigger_State | 1.
Existing Instance Trigger_Prop  | 1.

Section Test.

  (* Small test: can we infer a view instance picking event domains 1 and 3 in a list? *)
  Variable A B C D: Type -> Type.
  Goal (A +' C) +? (B +' D) -< (A +' B +' C +' D).
    typeclasses eauto.
  Qed.

  (* Reassociation is fine *)
  Goal (A +' C) +? (B +' D) -< (A +' B) +' (C +' D).
    typeclasses eauto.
  Qed.

End Test.

Notation trigger e := (trigger _ (inj1 e)).
