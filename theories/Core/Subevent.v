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
     Indexed.Function
.

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
      f : B ~> (A +' C) ;
      g : (A +' C) ~> B ;
      iso : Iso _ f g ;
    }.
  
  Definition inj1 {A B C} `{Subevent A B C} : A ~> B :=  inl_ >>> g.
  Definition inj2 {A B C} `{Subevent A B C} : C ~> B :=  inr_ >>> g.
  Definition case  {A B C} `{Subevent A B C} : B ~> (A +' C) := f.
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
About case.
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
Definition over {A B C M : Type -> Type} {S:Subevent A B C} {T:Trigger C M} (f : A ~> M) : B ~> M  :=
  fun t b =>  match case b with
           | inl1 a => f _ a
           | inr1 c => trigger' _ c
           end.

Arguments over {_ _ _ _ _ _} _ [_] _.


(* TODO: Change these *)
(* Recovering the previous notion of effect inclusion. *)
(*
Notation "A -< B" := (C, Subevent A B C)
                       (at level 90, left associativity) : type_scope.

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
      (fun T e s => t <- trigger' _ e ;; ret (s,t))%monad.

    (* The [PropT] transformer returns the propositional singleton of the underlying trigger.
       However, we might want this singleton to be up to some equivalence *)
    Instance Trigger_Prop {E} {M} `{Monad M} `{Trigger E M} : Trigger E (fun X => M X -> Prop) :=
      (fun T e m => m = (trigger' _ e)).

  End Trigger_Instances.

  
  


  Section Subevent_Instances.

    (** Event level instances *)

    (* The subeffect relationship is reflexive: A -<  A *)
    Instance Subevent_refl {A : Type -> Type} : Subevent A A void1.
    refine
      {| f := inl1
         ; g := fun T (x : (A +' void1) T) => match x with inl1 a => a | inr1 abs => match abs with end end
                        
      |}.
    split. constructor.
    repeat intro. 
    unfold cat, Cat_IFun. cbn. destruct a. reflexivity. inversion v.
    Defined.

    (* 
    Instance Subevent_refl_BETTER {A : Type -> Type} : Subevent A A void1.
    refine
      {| f := inl_
       ; g := unit_r
      |}.
    split. constructor.
    repeat intro. 
    unfold cat, Cat_IFun. cbn. destruct a. reflexivity. inversion v.
    Defined.
     *)
    
    (* void1 is a subeffect of any type
       void1 -< A *)
    Instance Subevent_void {A}: void1 -< A.
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




Section View.

  
  Class View {A B Z : Type -> Type} : Type :=
    { preview : B ~> A +' Z
      ; review : A ~> B
      ; preview_review : forall {t} (a : A t), preview (review a) = inl1 a
      ; review_preview : forall {t} (b : B t) a, preview b = inl1 a -> review a = b
    }.
  Arguments View : clear implicits.
  Arguments preview {_ _ _ _} [_].
  Arguments review {_ _ _ _} [_].

(* The subeffect relationship is reflexive
   A <-> A -> void1 *)
  Instance View_id {A} : View A A void1.
  refine
    {| preview := inl1
       ; review := fun _ x => x
    |}.
  auto.
  intros ? ? ? H; inversion H; auto.
  Defined.

  (* void1 is a subeffect of any type
   void1 <-> A -> A *)
  Instance View_none {A}: View void1 A A.
  refine
    {| preview := inr1
       ; review := fun t (x: void1 t) => match x with end
    |}.
  intros ? x; inversion x.
  intros ? ? x; inversion x.
  Defined.

  (* Could use the categorical instances, but a bit annoying since we are working pointwise here *)
  (* Definition assoc_r {A B C: Type -> Type}: ((A +' B) +' C) ~> (A +' (B +' C)) := *)
  (*   fun _ x => *)
  (*     match x with *)
  (*     | inr1 c => inr1 (inr1 c) *)
  (*     | inl1 (inr1 b) => inr1 (inl1 b) *)
  (*     | inl1 (inl1 a) => inl1 a *)
  (*     end. *)

  (* Definition assoc_l {A B C: Type -> Type}: (A +' (B +' C)) ~> ((A +' B) +' C) := *)
  (*   fun _ x => *)
  (*     match x with *)
  (*     | inr1 (inr1 c) => inr1 c *)
  (*     | inr1 (inl1 b) => inl1 (inr1 b) *)
  (*     | inl1 a => inl1 (inl1 a) *)
  (*     end. *)

  (* Lemma assoc_rl {A B C: Type -> Type}: forall x, assoc_r (assoc_l x) = x. *)

  Instance View_Assoc1 {A B C D E: Type -> Type} `{View (A +' B +' C) D E}: View ((A +' B) +' C) D E.
  refine
    {| preview := fun _ d => match preview d with
                          | inl1 x => inl1 (assoc_l _ x)
                          | inr1 e => inr1 e
                          end
       ; review := fun _ x => review (assoc_r _ x)
    |}.
  Admitted.
  (* There appears to be problems with the `Category` instances *)
  (* - intros ? [a | [b | c]]; rewrite preview_review. *)
  (*   generalize (@Monoidal_Coproduct _ Fun _ _ _ _ _). *)
  (*   generalize (@monoidal_assoc_iso (Type -> Type) IFun Eq2_IFun Id_IFun Cat_IFun sum1 _ _ _ void1 _ _ _ _ (@Monoidal_Coproduct ). *)
  (*   generalize (@assoc_r_mono (Type -> Type) IFun Eq2_IFun Id_IFun Cat_IFun sum1 _ _ (@monoidal_assoc_iso (Type -> Type) IFun sum1 void1)). _ _ _ _ _ _ _ A B C). (. *)
  (*   inversion x. *)
  (* intros ? ? x; inversion x. *)
  (* Defined. *)

  Instance View_Assoc2 {A B C D E: Type -> Type} `{View A (B +' C +' D) E}: View A ((B +' C) +' D) E.
  refine
    {| preview := fun _ d => preview (assoc_r _ d)
       ; review := fun _ x => assoc_l _ (review x) 
    |}.
  Admitted.

  Instance View_Assoc3 {A B C D E: Type -> Type} `{View A B (C +' D +' E)}: View A B ((C +' D) +' E).
  refine
    {| preview := fun _ d => match preview d with
                          | inl1 a => inl1 a
                          | inr1 d => inr1 (assoc_l _ d)
                          end
       ; review := review
    |}.
  Admitted.

  (* Extends the complement to the left
     A <-> B -> Z
-------------------------
 A <-> B' +' B -> B' +' Z
   *)

  Instance View_comp {A B B' Z} `{View A B Z} : View A (B' +' B) (B' +' Z).
  refine
    {|
      preview := fun _ X =>
                   match X with
                   | inl1 b' =>  inr1 (inl1 b')
                   | inr1 b => match preview b with
                              | inl1 b => inl1 b
                              | inr1 z => inr1 (inr1 z)
                              end
                   end
      ; review := fun _ x => inr1 (review x)
    |}.
  Proof.
    - intros t x; cbn.
      rewrite preview_review; reflexivity.
    - intros t [x | y] x'; [intros abs; inversion abs |]; cbn. 
      destruct (preview y) eqn:EQ; [| intros abs; inversion abs].
      intros eq; inversion eq; subst.
      apply review_preview in EQ; rewrite EQ; reflexivity.
  Defined.

  (* The base case is anonying. Could consider introducing void1, but likely to be tricky to avoid looping *)
  Instance View_comp_base {A B B'} `{V: View A B void1} : View A (B' +' B) B'.
  refine
    {|
      preview := fun T X =>  
                   match X with
                   | inl1 b' => inr1 b'
                   | inr1 b => match preview b with
                              | inl1 a => inl1 a
                              | inr1 z => match z in void1 T with end
                              end
                   end
      ; review := fun _ x => inr1 (review x)
    |}.
  Proof.
    - intros t a; cbn; rewrite preview_review; auto. 
    - intros t [b' | b] a; cbn; intros EQ; inv EQ; auto.
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ =>
        destruct x eqn:EQ; [apply review_preview in EQ; subst; inv h | inv h]
      end; easy.
  Defined.

  (* Extends the subtype to the left
     A <-> B -> Z
-------------------------
 B' +' A <-> B' +' B -> Z
   *)

  Instance View_inner {A B B' Z} `{View A B Z} : View (B' +' A) (B' +' B) Z.
  refine
    {|
      preview := fun _ X => 
                   match X with
                   | inl1 b' =>  inl1 (inl1 b')
                   | inr1 b => match preview b with
                              | inl1 b => inl1 (inr1 b)
                              | inr1 z => inr1 z
                              end
                   end
      ; review := fun _ x => 
                    match x with
                    | inl1 b' => inl1 b'
                    | inr1 a => inr1 (review a) 
                    end
    |}.
  Proof.
    - intros t [b' | a]; cbn; auto.
      rewrite preview_review; reflexivity.
    - intros t [b' | b] [b'' | a]; cbn; intros EQ; inv EQ; auto;
        match goal with
        | h: context[match ?x with | _ => _ end] |- _ =>
          destruct x eqn:EQ; [apply review_preview in EQ; subst; inv h | inv h]
        end.
      auto.
  Defined.

  (* The base case is anonying. Could consider introducing void1, but likely to be tricky to avoid looping *)
  Instance View_inner_base {B B' Z} `{V: View void1 B Z} : View B' (B' +' B) Z.
  refine
    {|
      preview := fun _ X =>  
                   match X with
                   | inl1 b' =>  inl1 b'
                   | inr1 b => match preview b with
                               | inl1 b => match b in void1 _ with end
                               | inr1 z => inr1 z
                               end
                   end
      ; review := inl1
    |}.
  Proof.
    - auto. 
    - intros t [b' | b] a; cbn; intros EQ; inv EQ; auto.
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ =>
        destruct x eqn:EQ; [apply review_preview in EQ; subst; inv h | inv h]
      end; easy.
  Defined.

  (** Instances to call [over] into other monads *)

  (*
 A <-> B -> Z
------------------
 A <-> B -> stateT s Z
   *)

  (* Instance View_ToStateT {S: Type} {A B E: Type -> Type} {M: (Type -> Type) -> Type -> Type } *)
  (*          `{View A B (M E)} `{Triggerable' M}: View A B (Monads.stateT S (M E)). *)
  (* econstructor. *)
  (* Unshelve. *)
  (* 4:{ exact review. } *)
  (* 3:{ *)
  (*   destruct H. *)
  (*   intros t a. *)
  (*   destruct (preview0 _ a) as [b | m]; [left; exact b | right]. *)
  (*   eapply trigger'; eauto. *)
  (*   Unshelve. *)

  (*   Instance Trigger_State' {S} (* {M: (Type -> Type) -> Type -> Type} `{forall E, Monad (M E)} `{Triggerable' M} *): Triggerable' (Monads.stateT S). *)
  (*   intros E T e s. *)
    
  (*   (fun E T e s => t <- trigger' _ _ e ;; ret (s,t))%monad. *)
 
  (*   refine (fun _ a => match preview a with *)
  (*                  | inl1 b => inl1 b *)
  (*                  | inr1 z => inr1 (trigger' _ _ z) *)
  (*                  end). *)
  (*   typeclasses eauto. *)
  (*   := *)
  (*   {| *)
  (*     preview := fun _ a => _ *)
  (*                  match preview a with *)
  (*                  | inl1 b => inl1 b *)
  (*                  | inr1 z => inr1 _ *)
  (*                                  (* (trigger' z) *) *)
  (*                  end; *)
  (*     review := review *)
  (*   |}. *)
  (* Proof. *)
  (*   intros; rewrite preview_review; reflexivity. *)
  (*   - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto. *)
  (* Defined.   *)


  (* (* To avoid universe inconsistency *) *)
  From ITree Require Import
       Core.KTree
       Interp.Handler
       Interp.Recursion.

  (*
 A <-> B -> Z
------------------
 A <-> B -> itree Z
   *)
  Instance View_ToITree {A B Z} `{View A B Z}: View A B (itree Z) :=
    {|
      preview := fun _ x =>
                   match preview x with
                   | inl1 e => inl1 e
                   | inr1 f => inr1 (ITree.trigger f)
                   end;
      review := review
    |}.
  Proof.
    - intros; rewrite preview_review; reflexivity.
    - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
  Defined.

  (* Instance ViewToStateT {S A Z B} `{V: View A B Z}: View A B (Monads.stateT S Z). *)
  (* This instance seems impossible to write.
   It requires to build a [Z (S * T)] from a [Z T] which we cannot do in general.
   We can certainly build the specific instance for [Z ~ itree Y] for some Y.
   *)

  

  
  Definition pure_state {S E} : E ~> Monads.stateT S (itree E)
    := fun _ e s => Vis e (fun x => Ret (s, x)).

  Instance View_ToStateT {S A B Z} `{View A B Z}: View A B (Monads.stateT S (itree Z)) :=
    {|
      preview := fun _ a =>
                   match preview a with
                   | inl1 b => inl1 b
                   | inr1 z => inr1 (pure_state _ z)
                   end;
      review := review
    |}.
  Proof.
    intros; rewrite preview_review; reflexivity.
    - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
  Defined.  


  Instance View_ToStateT' {S A B Z} `{View A B Z}: View A B (Monads.stateT S Z) :=
    {|
      preview := fun _ a =>
                   match preview a with
                   | inl1 b => inl1 b
                   | inr1 z => inr1 (pure_state _ z)
                   end;
      review := review
    |}.
  Proof.
    intros; rewrite preview_review; reflexivity.
    - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
  Defined.  

  
End View.
Arguments View : clear implicits.
Arguments preview {_ _ _ _} [_].
Arguments review {_ _ _ _} [_].

Definition over' {A B Z} {z : View A B Z} (f : A ~> Z) : B ~> Z :=
  fun t b => match preview b with
          | inl1 a => f _ a
          | inr1 z => z
          end.
Arguments over' {_ _ _ _} _ [_] _.

Existing Instance View_id | 0.
Existing Instance View_none | 0.
Existing Instance View_inner | 3.
Existing Instance View_inner_base | 2.
Existing Instance View_comp | 3.
Existing Instance View_comp_base | 2.
Existing Instance View_Assoc1 | 10.
Existing Instance View_Assoc2 | 10.
Existing Instance View_Assoc3 | 10.
Existing Instance View_ToITree | 1.
Existing Instance View_ToStateT | 1.

Section Test.

  (* Small stress test: can we infer a view instance picking event domains 1 and 3 in a list? *)
  Variable A B C D: Type -> Type.
  Goal (A +' C) -< (A +' B +' C +' D).
    typeclasses eauto.
  Qed.

  Goal View (A +' C) (A +' B +' C +' D) (B +' D).
    typeclasses eauto.
  Qed.

  (* Reassociation is fine *)
  Goal (A +' C) -< (A +' B) +' (C +' D).
    typeclasses eauto.
  Qed.

  (* Test for [over] *)
  Variable S: Type.
  Variable h: forall E, A ~> (* Monads.stateT S *) (itree E).
  Typeclasses eauto := 4.
  (* This cannot work: the instances do not extend void1, i.e. do not alter the monad into which we trigger. Should it? *)
  Fail Goal forall {X} (e: (A +' B) X), over h e = over h e.
  (* Goal forall {X: Type} (e: (A +' B) X), @over' A (A +' B) (itree B) _ (h _) _ e= @over' A (A +' B) (itree B) _ (h _) _ e. *)
    (* intros ? ?. *)
    (* Set Printing Implicit. *)

End Test.


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
    Instance Trigger_Prop {E} {M} `{Monad M} `{Trigger E M} : Trigger E (fun X => M X -> Prop) :=
      (fun T e m => m = (trigger' _ e)).

  End Trigger_Instances.

  
  


  Section Subevent_Instances.

    (** Event level instances *)

    (* The subeffect relationship is reflexive: A -<  A *)
    Instance Subevent_refl {A : Type -> Type} : Subevent A A void1.
    refine
      {| f := inl1
         ; g := fun T (x : (A +' void1) T) => match x with inl1 a => a | inr1 abs => match abs with end end
                        
      |}.
    split. constructor.
    repeat intro. 
    unfold cat, Cat_IFun. cbn. destruct a. reflexivity. inversion v.
    Defined.

    (* 
    Instance Subevent_refl_BETTER {A : Type -> Type} : Subevent A A void1.
    refine
      {| f := inl_
       ; g := unit_r
      |}.
    split. constructor.
    repeat intro. 
    unfold cat, Cat_IFun. cbn. destruct a. reflexivity. inversion v.
    Defined.
     *)
    
    (* void1 is a subeffect of any type
       void1 -< A *)
    Instance Subevent_void {A}: void1 -< A.
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




Section View.

  
  Class View {A B Z : Type -> Type} : Type :=
    { preview : B ~> A +' Z
      ; review : A ~> B
      ; preview_review : forall {t} (a : A t), preview (review a) = inl1 a
      ; review_preview : forall {t} (b : B t) a, preview b = inl1 a -> review a = b
    }.
  Arguments View : clear implicits.
  Arguments preview {_ _ _ _} [_].
  Arguments review {_ _ _ _} [_].

(* The subeffect relationship is reflexive
   A <-> A -> void1 *)
  Instance View_id {A} : View A A void1.
  refine
    {| preview := inl1
       ; review := fun _ x => x
    |}.
  auto.
  intros ? ? ? H; inversion H; auto.
  Defined.

  (* void1 is a subeffect of any type
   void1 <-> A -> A *)
  Instance View_none {A}: View void1 A A.
  refine
    {| preview := inr1
       ; review := fun t (x: void1 t) => match x with end
    |}.
  intros ? x; inversion x.
  intros ? ? x; inversion x.
  Defined.

  (* Could use the categorical instances, but a bit annoying since we are working pointwise here *)
  (* Definition assoc_r {A B C: Type -> Type}: ((A +' B) +' C) ~> (A +' (B +' C)) := *)
  (*   fun _ x => *)
  (*     match x with *)
  (*     | inr1 c => inr1 (inr1 c) *)
  (*     | inl1 (inr1 b) => inr1 (inl1 b) *)
  (*     | inl1 (inl1 a) => inl1 a *)
  (*     end. *)

  (* Definition assoc_l {A B C: Type -> Type}: (A +' (B +' C)) ~> ((A +' B) +' C) := *)
  (*   fun _ x => *)
  (*     match x with *)
  (*     | inr1 (inr1 c) => inr1 c *)
  (*     | inr1 (inl1 b) => inl1 (inr1 b) *)
  (*     | inl1 a => inl1 (inl1 a) *)
  (*     end. *)

  (* Lemma assoc_rl {A B C: Type -> Type}: forall x, assoc_r (assoc_l x) = x. *)

  Instance View_Assoc1 {A B C D E: Type -> Type} `{View (A +' B +' C) D E}: View ((A +' B) +' C) D E.
  refine
    {| preview := fun _ d => match preview d with
                          | inl1 x => inl1 (assoc_l _ x)
                          | inr1 e => inr1 e
                          end
       ; review := fun _ x => review (assoc_r _ x)
    |}.
  Admitted.
  (* There appears to be problems with the `Category` instances *)
  (* - intros ? [a | [b | c]]; rewrite preview_review. *)
  (*   generalize (@Monoidal_Coproduct _ Fun _ _ _ _ _). *)
  (*   generalize (@monoidal_assoc_iso (Type -> Type) IFun Eq2_IFun Id_IFun Cat_IFun sum1 _ _ _ void1 _ _ _ _ (@Monoidal_Coproduct ). *)
  (*   generalize (@assoc_r_mono (Type -> Type) IFun Eq2_IFun Id_IFun Cat_IFun sum1 _ _ (@monoidal_assoc_iso (Type -> Type) IFun sum1 void1)). _ _ _ _ _ _ _ A B C). (. *)
  (*   inversion x. *)
  (* intros ? ? x; inversion x. *)
  (* Defined. *)

  Instance View_Assoc2 {A B C D E: Type -> Type} `{View A (B +' C +' D) E}: View A ((B +' C) +' D) E.
  refine
    {| preview := fun _ d => preview (assoc_r _ d)
       ; review := fun _ x => assoc_l _ (review x) 
    |}.
  Admitted.

  Instance View_Assoc3 {A B C D E: Type -> Type} `{View A B (C +' D +' E)}: View A B ((C +' D) +' E).
  refine
    {| preview := fun _ d => match preview d with
                          | inl1 a => inl1 a
                          | inr1 d => inr1 (assoc_l _ d)
                          end
       ; review := review
    |}.
  Admitted.

  (* Extends the complement to the left
     A <-> B -> Z
-------------------------
 A <-> B' +' B -> B' +' Z
   *)

  Instance View_comp {A B B' Z} `{View A B Z} : View A (B' +' B) (B' +' Z).
  refine
    {|
      preview := fun _ X =>
                   match X with
                   | inl1 b' =>  inr1 (inl1 b')
                   | inr1 b => match preview b with
                              | inl1 b => inl1 b
                              | inr1 z => inr1 (inr1 z)
                              end
                   end
      ; review := fun _ x => inr1 (review x)
    |}.
  Proof.
    - intros t x; cbn.
      rewrite preview_review; reflexivity.
    - intros t [x | y] x'; [intros abs; inversion abs |]; cbn. 
      destruct (preview y) eqn:EQ; [| intros abs; inversion abs].
      intros eq; inversion eq; subst.
      apply review_preview in EQ; rewrite EQ; reflexivity.
  Defined.

  (* The base case is anonying. Could consider introducing void1, but likely to be tricky to avoid looping *)
  Instance View_comp_base {A B B'} `{V: View A B void1} : View A (B' +' B) B'.
  refine
    {|
      preview := fun T X =>  
                   match X with
                   | inl1 b' => inr1 b'
                   | inr1 b => match preview b with
                              | inl1 a => inl1 a
                              | inr1 z => match z in void1 T with end
                              end
                   end
      ; review := fun _ x => inr1 (review x)
    |}.
  Proof.
    - intros t a; cbn; rewrite preview_review; auto. 
    - intros t [b' | b] a; cbn; intros EQ; inv EQ; auto.
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ =>
        destruct x eqn:EQ; [apply review_preview in EQ; subst; inv h | inv h]
      end; easy.
  Defined.

  (* Extends the subtype to the left
     A <-> B -> Z
-------------------------
 B' +' A <-> B' +' B -> Z
   *)

  Instance View_inner {A B B' Z} `{View A B Z} : View (B' +' A) (B' +' B) Z.
  refine
    {|
      preview := fun _ X => 
                   match X with
                   | inl1 b' =>  inl1 (inl1 b')
                   | inr1 b => match preview b with
                              | inl1 b => inl1 (inr1 b)
                              | inr1 z => inr1 z
                              end
                   end
      ; review := fun _ x => 
                    match x with
                    | inl1 b' => inl1 b'
                    | inr1 a => inr1 (review a) 
                    end
    |}.
  Proof.
    - intros t [b' | a]; cbn; auto.
      rewrite preview_review; reflexivity.
    - intros t [b' | b] [b'' | a]; cbn; intros EQ; inv EQ; auto;
        match goal with
        | h: context[match ?x with | _ => _ end] |- _ =>
          destruct x eqn:EQ; [apply review_preview in EQ; subst; inv h | inv h]
        end.
      auto.
  Defined.

  (* The base case is anonying. Could consider introducing void1, but likely to be tricky to avoid looping *)
  Instance View_inner_base {B B' Z} `{V: View void1 B Z} : View B' (B' +' B) Z.
  refine
    {|
      preview := fun _ X =>  
                   match X with
                   | inl1 b' =>  inl1 b'
                   | inr1 b => match preview b with
                               | inl1 b => match b in void1 _ with end
                               | inr1 z => inr1 z
                               end
                   end
      ; review := inl1
    |}.
  Proof.
    - auto. 
    - intros t [b' | b] a; cbn; intros EQ; inv EQ; auto.
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ =>
        destruct x eqn:EQ; [apply review_preview in EQ; subst; inv h | inv h]
      end; easy.
  Defined.

  (** Instances to call [over] into other monads *)

  (*
 A <-> B -> Z
------------------
 A <-> B -> stateT s Z
   *)

  (* Instance View_ToStateT {S: Type} {A B E: Type -> Type} {M: (Type -> Type) -> Type -> Type } *)
  (*          `{View A B (M E)} `{Triggerable' M}: View A B (Monads.stateT S (M E)). *)
  (* econstructor. *)
  (* Unshelve. *)
  (* 4:{ exact review. } *)
  (* 3:{ *)
  (*   destruct H. *)
  (*   intros t a. *)
  (*   destruct (preview0 _ a) as [b | m]; [left; exact b | right]. *)
  (*   eapply trigger'; eauto. *)
  (*   Unshelve. *)

  (*   Instance Trigger_State' {S} (* {M: (Type -> Type) -> Type -> Type} `{forall E, Monad (M E)} `{Triggerable' M} *): Triggerable' (Monads.stateT S). *)
  (*   intros E T e s. *)
    
  (*   (fun E T e s => t <- trigger' _ _ e ;; ret (s,t))%monad. *)
 
  (*   refine (fun _ a => match preview a with *)
  (*                  | inl1 b => inl1 b *)
  (*                  | inr1 z => inr1 (trigger' _ _ z) *)
  (*                  end). *)
  (*   typeclasses eauto. *)
  (*   := *)
  (*   {| *)
  (*     preview := fun _ a => _ *)
  (*                  match preview a with *)
  (*                  | inl1 b => inl1 b *)
  (*                  | inr1 z => inr1 _ *)
  (*                                  (* (trigger' z) *) *)
  (*                  end; *)
  (*     review := review *)
  (*   |}. *)
  (* Proof. *)
  (*   intros; rewrite preview_review; reflexivity. *)
  (*   - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto. *)
  (* Defined.   *)


  (* (* To avoid universe inconsistency *) *)
  From ITree Require Import
       Core.KTree
       Interp.Handler
       Interp.Recursion.

  (*
 A <-> B -> Z
------------------
 A <-> B -> itree Z
   *)
  Instance View_ToITree {A B Z} `{View A B Z}: View A B (itree Z) :=
    {|
      preview := fun _ x =>
                   match preview x with
                   | inl1 e => inl1 e
                   | inr1 f => inr1 (ITree.trigger f)
                   end;
      review := review
    |}.
  Proof.
    - intros; rewrite preview_review; reflexivity.
    - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
  Defined.

  (* Instance ViewToStateT {S A Z B} `{V: View A B Z}: View A B (Monads.stateT S Z). *)
  (* This instance seems impossible to write.
   It requires to build a [Z (S * T)] from a [Z T] which we cannot do in general.
   We can certainly build the specific instance for [Z ~ itree Y] for some Y.
   *)

  

  
  Definition pure_state {S E} : E ~> Monads.stateT S (itree E)
    := fun _ e s => Vis e (fun x => Ret (s, x)).

  Instance View_ToStateT {S A B Z} `{View A B Z}: View A B (Monads.stateT S (itree Z)) :=
    {|
      preview := fun _ a =>
                   match preview a with
                   | inl1 b => inl1 b
                   | inr1 z => inr1 (pure_state _ z)
                   end;
      review := review
    |}.
  Proof.
    intros; rewrite preview_review; reflexivity.
    - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
  Defined.  


  Instance View_ToStateT' {S A B Z} `{View A B Z}: View A B (Monads.stateT S Z) :=
    {|
      preview := fun _ a =>
                   match preview a with
                   | inl1 b => inl1 b
                   | inr1 z => inr1 (pure_state _ z)
                   end;
      review := review
    |}.
  Proof.
    intros; rewrite preview_review; reflexivity.
    - intros ? xy x; destruct (preview xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
  Defined.  

  
End View.
Arguments View : clear implicits.
Arguments preview {_ _ _ _} [_].
Arguments review {_ _ _ _} [_].

Definition over' {A B Z} {z : View A B Z} (f : A ~> Z) : B ~> Z :=
  fun t b => match preview b with
          | inl1 a => f _ a
          | inr1 z => z
          end.
Arguments over' {_ _ _ _} _ [_] _.

Existing Instance View_id | 0.
Existing Instance View_none | 0.
Existing Instance View_inner | 3.
Existing Instance View_inner_base | 2.
Existing Instance View_comp | 3.
Existing Instance View_comp_base | 2.
Existing Instance View_Assoc1 | 10.
Existing Instance View_Assoc2 | 10.
Existing Instance View_Assoc3 | 10.
Existing Instance View_ToITree | 1.
Existing Instance View_ToStateT | 1.

Section Test.

  (* Small stress test: can we infer a view instance picking event domains 1 and 3 in a list? *)
  Variable A B C D: Type -> Type.
  Goal (A +' C) -< (A +' B +' C +' D).
    typeclasses eauto.
  Qed.

  Goal View (A +' C) (A +' B +' C +' D) (B +' D).
    typeclasses eauto.
  Qed.

  (* Reassociation is fine *)
  Goal (A +' C) -< (A +' B) +' (C +' D).
    typeclasses eauto.
  Qed.

  (* Test for [over] *)
  Variable S: Type.
  Variable h: forall E, A ~> (* Monads.stateT S *) (itree E).
  Typeclasses eauto := 4.
  (* This cannot work: the instances do not extend void1, i.e. do not alter the monad into which we trigger. Should it? *)
  Fail Goal forall {X} (e: (A +' B) X), over h e = over h e.
  (* Goal forall {X: Type} (e: (A +' B) X), @over' A (A +' B) (itree B) _ (h _) _ e= @over' A (A +' B) (itree B) _ (h _) _ e. *)
    (* intros ? ?. *)
    (* Set Printing Implicit. *)

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
