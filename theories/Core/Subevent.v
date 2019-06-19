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
(* end hide *)

Set Implicit Arguments.

(** Automatic application of commutativity and associativity for
    sums types constructed with [sum1].

    N.B. This is prone to infinite instance resolution loops.
    Put the following option at the top of your [.v] files to
    bound the instance search depth:

[[
  Typeclasses eauto := 5.
]]

    Higher numbers allow bigger instances but grow the search
    space exponentially.
 *)

(* View A B Z generalizes the Subevent relation.
   Should be thought as `A` is a subdomain of `B`, and `Z` a view of the complement.
   Note that one could always chose to take Z = unit, but it is important to express operations.
 *)
Class View {A B Z : Type -> Type} : Type :=
  { preview : B ~> A +' Z
    ; review : A ~> B 
    ; preview_review : forall {t} (a : A t), preview (review a) = inl1 a
    ; review_preview : forall {t} (b : B t) a, preview b = inl1 a -> review a = b
  }.
Arguments View : clear implicits.
Arguments preview {_ _ _ _} [_].
Arguments review {_ _ _ _} [_].

(* Partial injection of the bigger domain of events back into the smaller one *)
Definition isa {A B Z} {V : View A B Z} : forall t, B t -> option (A t) :=
  fun t ma =>
    match preview ma with
    | inl1 a => Some a
    | inr1 _ => None
    end.

(* Embedding of the subdomain into the bigger one *)
Definition subeventV {A B Z} {V : View A B Z} : A ~> B := review.

(* Generic lifting of an type-indexed function from the subdomain of effects `a`
   into the ambient one `A`.
   This is where we crucially need the `Z` argument to
   ̀View` for `preview` to also tell us how to embed the complement `A\a` into
   `B`. *)
Definition over {A B Z} {z : View A B Z} (f : A ~> Z) : B ~> Z :=
  fun t b => match preview b with
          | inl1 a => f _ a
          | inr1 z => z
          end.
Arguments over {_ _ _ _} _ [_] _.

Definition unit1: Type -> Type := fun _ => unit.
(* The less informative previous Subevent relation is recovered by dismissing the `Z` parameter *)
Notation Subevent A B := (View A B unit1) (only parsing).
Notation "A -< B" := (Subevent A B) 
                       (at level 90, left associativity) : type_scope.

Definition subevent {E F : Type -> Type} `{E -< F} : E ~> F := subeventV.

(** A polymorphic version of [Vis]. *)
Notation vis e k := (Vis (subevent _ e) k).

(* Called [send] in Haskell implementations of Freer monads. *)
Notation trigger e := (ITree.trigger (subevent _ e)).

(*************** Instances ***************)
Section Instances.
(** Event level instances *)

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

(* Extends the supertype to the right
     A <-> B -> Z
-------------------------
 A <-> B +' B' -> Z +' B'
 *)
Instance View_R {A B B' Z} `{View A B Z} : View A (B +' B') (Z +' B').
refine
  {|
    preview := fun _ X =>
                 match X with
                 | inl1 a => match preview a with
                            | inl1 a2 => inl1 a2
                            | inr1 z => inr1 (inl1 z)
                            end
                 | inr1 b => inr1 (inr1 b)
                 end;
    review := fun (T : Type) (x : A T) => inl1 (review x)
  |}.
Proof.
  - intros t x; cbn.
    rewrite preview_review; reflexivity.
  - intros t [x | y] x'; [| intros abs; inversion abs]; cbn. 
    destruct (preview x) eqn:EQ; [| intros abs; inversion abs].
    intros eq; inversion eq; subst.
    apply review_preview in EQ; rewrite EQ; reflexivity.
Defined.

(* Extends the supertype to the left
     A <-> B -> Z
-------------------------
 A <-> B' +' B -> Z +' B'
 *)

Instance View_L {A B B' Z} `{View A B Z} : View A (B' +' B) (Z +' B').
refine
  {|
    preview :=  fun _ X =>
                 match X with
                 | inl1 a =>  inr1 (inr1 a)
                 | inr1 b => match preview b with
                            | inl1 b => inl1 b
                            | inr1 z => inr1 (inl1 z)
                            end
                 end;
    review := fun _ x => inr1 (review x)
  |}.
Proof.
  - intros t x; cbn.
    rewrite preview_review; reflexivity.
  - intros t [x | y] x'; [intros abs; inversion abs |]; cbn. 
    destruct (preview y) eqn:EQ; [| intros abs; inversion abs].
    intros eq; inversion eq; subst.
    apply review_preview in EQ; rewrite EQ; reflexivity.
Defined.

(* Builds combined domains of subeffects.
   What is the right choice here for Z? Taking the sum of both domains is definitely sensible if
   the instance resolution is such that we always first build 'pure effect views', and then on top
   of it the view into the monad of interest.
   Otherwise, we might end up with views into 'itree E +' itree F', which might be a bit too funky.
     A1 <-> B1 -> Z1
     A2 <-> B2 -> Z2
-------------------------
 A1 +' A2 <-> B1 +' B2 -> Z1 +' Z2
 *)
Instance View_Sum {A1 A2 B1 B2 Z1 Z2} `{View A1 B1 Z1} `{View A2 B2 Z2} : View (A1 +' A2) (B1 +' B2) (Z1 +' Z2).
refine
  {|
    preview := fun _ ab => 
                 match ab with
                 | inl1 a => match preview a with
                            | inl1 a => inl1 (inl1 a)
                            | inr1 y => inr1 (inl1 y)
                            end
                 | inr1 b => match preview b with
                            | inl1 b => inl1 (inr1 b)
                            | inr1 z => inr1 (inr1 z)
                            end
                 end;
    review := fun _ ab =>
                match ab with
                | inl1 a => inl1 (review a)
                | inr1 b => inr1 (review b)
                end
  |}.
Proof.
  - intros t [xa | xb]; cbn;
      rewrite preview_review; reflexivity.
  - intros t [xA | xB] [xa | xb];
      match goal with
        |- context [match ?h with | _ => _ end] => destruct h eqn:EQh
      end; intros EQ; inv EQ; f_equal; apply review_preview; auto.
Defined.

(* We can always forget the domain into which we knew how to embed the complement
 A <-> B -> Z
------------------
 A <-> B -> unit1
 *)
Instance SubFromView {A B Z} `{View A B Z}: A -< B :=
  {|
    preview := fun _ a => match preview a with 
                       | inl1 b => inl1 b
                       | inr1 _ => inr1 tt
                       end;
    review := review
  |}.
Proof.
  intros; rewrite preview_review; reflexivity.
  let H := fresh "H" in intros ? ? ? H; match type of H with context[match ?x with | _ => _ end] => destruct x eqn: EQ end; inv H.
  apply review_preview; auto.
Defined.

(** Instances to call [over] into other monads *)

(*
 A <-> B -> Z
------------------
 A <-> B -> itree Z
 *)
Instance ViewToITree {A B Z} `{View A B Z}: View A B (itree Z) :=
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

(*
 A <-> B -> Z
------------------
 A <-> B -> stateT s Z
 *)

(* Instance ViewToStateT {S A Z B} `{V: View A B Z}: View A B (Monads.stateT S Z). *)
(* This instance seems impossible to write.
   It requires to build a [Z (S * T)] from a [Z T] which we cannot do in general.
   We can certainly build the specific instance for [Z ~ itree Y] for some Y.
 *)
Definition pure_state {S E} : E ~> Monads.stateT S (itree E)
  := fun _ e s => Vis e (fun x => Ret (s, x)).

Instance ViewToStateT {S A B Z} `{View A B Z}: View A B (Monads.stateT S (itree Z)) :=
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

(* We could define as many instances as we want to use nested monads in practice...
   Can we do better? Gets back to the idea of having a "triggerable" type class.
 *)

  (* void1 is annoying. This permits to extend with two recursive instances when the instance to the left is reflexive  *)
  Instance View_Sum' {A1 A2 B1 B2 Z} `{V1: View A1 B1 void1} `{V2:View A2 B2 Z} : View (A1 +' A2) (B1 +' B2) Z.
  refine
    {|
      preview := fun _ b => 
                   match b with
                   | inl1 b1 => match @preview _ _ _ V1 _ b1 with
                               | inl1 a1 => inl1 (inl1 a1)
                               | inr1 abs => match abs with end
                               end
                   | inr1 b2 => match preview b2 with
                               | inl1 a2 => inl1 (inr1 a2)
                               | inr1 z => inr1 z
                               end
                   end;
      review := 
        fun _ ab =>
          match ab with
          | inl1 a => inl1 (review a)
          | inr1 b => inr1 (review b)
          end
    |}.
  Proof.
    - intros t [xa | xb]; cbn;
        rewrite preview_review; reflexivity.
    - intros t [xA | xB] [xa | xb];
        match goal with
          |- context [match ?h with | _ => _ end] => destruct h eqn:EQh
        end; intros EQ; inv EQ; f_equal; ((inv v; fail) || (apply review_preview; auto)).
  Defined.

  (* Seems to work better with the second argument ordered this way, to double check *)
  Instance View_L' {A B B' Z} `{View A B Z} : View A (B' +' B) (B' +' Z).
  refine
    {|
      preview := fun _ X =>
                   match X with
                   | inl1 a => inr1 (inl1 a)
                   | inr1 b => match preview b with
                              | inl1 b => inl1 b
                              | inr1 z => inr1 (inr1 z)
                              end
                   end;
      review := fun _ x => inr1 (review x)
    |}.
  Proof.
    - intros t x; cbn.
      rewrite preview_review; reflexivity.
    - intros t [x | y] x'; [intros abs; inversion abs |]; cbn. 
      destruct (preview y) eqn:EQ; [| intros abs; inversion abs].
      intros eq; inversion eq; subst.
      apply review_preview in EQ; rewrite EQ; reflexivity.
  Defined.

  (* Seems to work better with the second argument ordered this way, to double check *)
  Instance View_R' {A B B' Z} `{View A B Z} : View A (B +' B') (B' +' Z).
  refine
    {|
      preview := fun _ X =>
                   match X with
                   | inl1 a => match preview a with
                              | inl1 a2 => inl1 a2
                              | inr1 z => inr1 (inr1 z)
                              end
                   | inr1 b => inr1 (inl1 b)
                   end;
      review := fun _ x => inl1 (review x)
    |}.
  Proof.
    - intros t x; cbn.
      rewrite preview_review; reflexivity.
    - intros t [x | y] x'; [| intros abs; inversion abs]; cbn. 
      destruct (preview x) eqn:EQ; [| intros abs; inversion abs].
      intros eq; inversion eq; subst.
      apply review_preview in EQ; rewrite EQ; reflexivity.
  Defined.

  (* Alternate base case needed *)
  Instance View_base {A B}: View A (A +' B) B.
  refine
    {|
      preview := fun _ ab => ab;
      review := inl1
    |}.
  Proof.
    - auto.
    - auto. 
  Defined.

End Instances.

Existing Instance View_id.
Existing Instance View_none.
Existing Instance View_inner.
Existing Instance View_inner_base.
Existing Instance View_comp.
Existing Instance View_comp_base.
Existing Instance View_Assoc1.
Existing Instance View_Assoc2.
Existing Instance View_Assoc3.

Section Test.

  (* Small stress test: can we infer a view instance picking event domains 1 and 3 in a list? *)
  Variable A B C D: Type -> Type.
  Goal View (A +' C) (A +' B +' C +' D) (B +' D).
    typeclasses eauto.
  Qed.

  Goal View (A +' C) ((A +' B) +' (C +' D)) (B +' D).
    typeclasses eauto.
  Qed.

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
