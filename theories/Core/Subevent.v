(** * Extensible effects *)

(** Notations to handle large sums and classes for extensible effects. *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
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

(* View XY Z X generalizes the Subevent relation.
   Should be thought as `X` is a subdomain of `XY`, and `Z` a view of the complement.
   Note that one could always chose to take Z = unit, but it is important to express operations.
 *)
Class View {XY Z X : Type -> Type} : Type :=
  { preview : XY ~> X +' Z
    ; review : X ~> XY
    ; preview_review : forall {t} (x : X t), preview (review x) = inl1 x
    ; review_preview : forall {t} (xy : XY t) x, preview xy = inl1 x -> review x = xy
  }.
Arguments View : clear implicits.
Arguments preview {_ _ _} _ [_].
Arguments review {_ _ _} _ [_].

(* Partial injection of the bigger domain of events back into the smaller one *)
Definition isa {X Z y} {V : View X Z y} : forall t, X t -> option (y t) :=
  fun t mx =>
    match V.(preview) mx with
    | inl1 x => Some x
    | inr1 _ => None
    end.

(* Embedding of the subdomain into the bigger one *)
Definition subeventV {X Z y} {V : View X Z y} : y ~> X := V.(review).

(* Generic lifting of an type-indexed function from the subdomain of effects `a`
   into the ambient one `A`.
   This is where we crucially need the `Z` argument to
   ̀View` for `preview` to also tell us how to embed the complement `A\a` into
   `B`. *)
Definition over {A B a} {z : View A B a} (f : a ~> B) : A ~> B :=
  fun t a => match z.(preview) a with
          | inl1 a => f _ a
          | inr1 b => b
          end.
Arguments over {_ _ _ _} _ [_] _.

Definition unit1: Type -> Type := fun _ => unit.
(* The less informative previous Subevent relation is recovered by dismissing the `Z` parameter *)
Notation Subevent A B := (View B unit1 A) (only parsing).
Notation "A -< B" := (Subevent A B) 
                       (at level 90, left associativity) : type_scope.

Definition subevent {E F : Type -> Type} `{E -< F} : E ~> F := subeventV.

(** A polymorphic version of [Vis]. *)
Notation vis e k := (Vis (subevent _ e) k).

(* Called [send] in Haskell implementations of Freer monads. *)
Notation trigger e := (ITree.trigger (subevent _ e)).

(*************** Instances ***************)

(** Event level instances *)

(* The subeffect relationship is reflexive
   A <-> A -> void1 *)
Instance View_id {A} : View A void1 A.
refine
  {| preview := inl1
     ; review := fun _ x => x
  |}.
auto.
intros ? ? ? H; inversion H; auto.
Defined.

(* void1 is a subeffect of any type
   void1 <-> A -> A *)
Instance View_none {A}: View A A void1.
refine
  {| preview := inr1
     ; review := fun t (x: void1 t) => match x with end
  |}.
intros ? x; inversion x.
intros ? ? x; inversion x.
Defined.

(* Extends the supertype to the right
     a <-> A -> Z
-------------------------
 a <-> A +' B -> Z +' B
 *)
Instance View_R {A B Z a} {_ : View A Z a} : View (A +' B) (Z +' B) a.
refine
  {|
    preview := fun _ X =>
                 match X with
                 | inl1 a => match preview _ a with
                            | inl1 a2 => inl1 a2
                            | inr1 z => inr1 (inl1 z)
                            end
                 | inr1 b => inr1 (inr1 b)
                 end;
    review := fun (T : Type) (x : a T) => inl1 (review X x)
  |}.
Proof.
  - intros t x; cbn.
    rewrite preview_review; reflexivity.
  - intros t [x | y] x'; [| intros abs; inversion abs]; cbn. 
    destruct (preview X x) eqn:EQ; [| intros abs; inversion abs].
    intros eq; inversion eq; subst.
    apply review_preview in EQ; rewrite EQ; reflexivity.
Defined.

(* Extends the supertype to the left
     b <-> B -> Z
-------------------------
 b <-> A +' B -> Z +' A
 *)

Instance View_L {A B Z b} {_ : View B Z b} : View (A +' B) (Z +' A) b.
refine
  {|
    preview :=  fun _ X =>
                 match X with
                 | inl1 a =>  inr1 (inr1 a)
                 | inr1 b => match preview _ b with
                            | inl1 b => inl1 b
                            | inr1 z => inr1 (inl1 z)
                            end
                 end;
    review := fun _ x => inr1 (review X x)
  |}.
Proof.
  - intros t x; cbn.
    rewrite preview_review; reflexivity.
  - intros t [x | y] x'; [intros abs; inversion abs |]; cbn. 
    destruct (preview X y) eqn:EQ; [| intros abs; inversion abs].
    intros eq; inversion eq; subst.
    apply review_preview in EQ; rewrite EQ; reflexivity.
Defined.

(* Builds combined domains of subeffects.
   What is the right choice here for Z? Taking the sum of both domains is definitely sensible if
   the instance resolution is such that we always first build 'pure effect views', and then on top
   of it the view into the monad of interest.
   Otherwise, we might end up with views into 'itree E +' itree F', which might be a bit too funky.
     a <-> A -> Y
     b <-> B -> Z
-------------------------
 a +' b <-> A' +' B' -> Y +' Z
 *)
Instance View_Sum {a A b B Y Z} {VA : View A Y a} {VB : View B Z b} : View (A +' B) (Y +' Z) (a +' b).
refine
  {|
    preview := fun _ ab => 
                 match ab with
                 | inl1 a => match preview VA a with
                            | inl1 a => inl1 (inl1 a)
                            | inr1 y => inr1 (inl1 y)
                            end
                 | inr1 b => match preview VB b with
                            | inl1 b => inl1 (inr1 b)
                            | inr1 z => inr1 (inr1 z)
                            end
                 end;
    review := fun _ ab =>
                match ab with
                | inl1 a => inl1 (review VA a)
                | inr1 b => inr1 (review VB b)
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
Instance SubFromView {A B Z} `{V:View A Z B}: B -< A :=
  {|
    preview := fun _ a => match V.(preview) a with 
                       | inl1 b => inl1 b
                       | inr1 _ => inr1 tt
                       end;
    review := V.(review)
  |}.
Proof.
  intros; rewrite preview_review; reflexivity.
  intros ? ? ? H; match type of H with context[match ?x with | _ => _ end] => destruct x eqn: EQ end; inv H.
  apply review_preview; auto.
Defined.

(** Instances to call [over] into other monads *)

(*
 A <-> B -> Z
------------------
 A <-> B -> itree Z
 *)
Instance ViewToITree {A B Z} `{V: View A Z B}: View A (itree Z) B :=
  {|
    preview := fun _ x =>
                 match V.(preview) x with
                 | inl1 e => inl1 e
                 | inr1 f => inr1 (ITree.trigger f)
                 end;
    review := V.(review)
  |}.
Proof.
  - intros; rewrite preview_review; reflexivity.
  - intros ? xy x; destruct (preview V xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
Defined.

(*
 A <-> B -> Z
------------------
 A <-> B -> stateT s Z
 *)

(* Instance ViewToStateT {S A Z B} `{V: View A Z B}: View A (Monads.stateT S Z) B. *)
(* This instance seems impossible to write.
   It requires to build a [Z (S * T)] from a [Z T] which we cannot do in general.
   We can certainly build the specific instance for [Z ~ itree Y] for some Y.
 *)
Definition pure_state {S E} : E ~> Monads.stateT S (itree E)
  := fun _ e s => Vis e (fun x => Ret (s, x)).

Instance ViewToStateT {S A Z B} `{V: View A Z B}: View A (Monads.stateT S (itree Z)) B :=
  {|
    preview := fun _ a =>
                 match preview V a with
                 | inl1 b => inl1 b
                 | inr1 z => inr1 (pure_state _ z)
                 end;
    review := review V
  |}.
Proof.
  intros; rewrite preview_review; reflexivity.
  - intros ? xy x; destruct (preview V xy) eqn:EQ; intros EQ'; inv EQ'; apply review_preview; auto.
Defined.  

(* We could define as many instances as we want to use nested monads in practice...
   Can we do better? Gets back to the idea of having a "triggerable" type class.
 *)

Section Test.

  (* Small stress test: can we infer a view instance picking event domains 1 and 3 in a list? *)
  Variable A B C D: Type -> Type.
  Goal View (A +' B +' C +' D) (B +' D) (A +' C).
    (* Not with the instances above *)
  Abort.

  (* void1 is annoying. This permits to extend with two recursive instances when the instance to the left is reflexive  *)
  Instance View_Sum' {a A b B Z} {VA : View A void1 a} {VB : View B Z b} : View (A +' B) Z (a +' b).
  refine
    {|
      preview := fun _ ab => 
                   match ab with
                   | inl1 a => match preview VA a with
                              | inl1 a => inl1 (inl1 a)
                              | inr1 y => match y with end
                              end
                   | inr1 b => match preview VB b with
                              | inl1 b => inl1 (inr1 b)
                              | inr1 z => inr1 z
                              end
                   end;
      review := fun _ ab =>
                  match ab with
                  | inl1 a => inl1 (review VA a)
                  | inr1 b => inr1 (review VB b)
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
  Instance View_L' {A B Z b} {_ : View B Z b} : View (A +' B) (A +' Z) b.
  refine
    {|
      preview := fun _ X =>
                   match X with
                   | inl1 a => inr1 (inl1 a)
                   | inr1 b => match preview _ b with
                              | inl1 b => inl1 b
                              | inr1 z => inr1 (inr1 z)
                              end
                   end;
      review := fun _ x => inr1 (review X x)
    |}.
  Proof.
    - intros t x; cbn.
      rewrite preview_review; reflexivity.
    - intros t [x | y] x'; [intros abs; inversion abs |]; cbn. 
      destruct (preview X y) eqn:EQ; [| intros abs; inversion abs].
      intros eq; inversion eq; subst.
      apply review_preview in EQ; rewrite EQ; reflexivity.
  Defined.

  (* Seems to work better with the second argument ordered this way, to double check *)
  Instance View_R' {A B Z a} {_ : View A Z a} : View (A +' B) (B +' Z) a.
  refine
    {|
      preview := fun _ X =>
                   match X with
                   | inl1 a => match preview _ a with
                              | inl1 a2 => inl1 a2
                              | inr1 z => inr1 (inr1 z)
                              end
                   | inr1 b => inr1 (inl1 b)
                   end;
      review := fun (T : Type) (x : a T) => inl1 (review X x)
    |}.
  Proof.
    - intros t x; cbn.
      rewrite preview_review; reflexivity.
    - intros t [x | y] x'; [| intros abs; inversion abs]; cbn. 
      destruct (preview X x) eqn:EQ; [| intros abs; inversion abs].
      intros eq; inversion eq; subst.
      apply review_preview in EQ; rewrite EQ; reflexivity.
  Defined.

  (* Alternate base case needed *)
  Instance View_base {A B}: View (A +' B) B A.
  refine
    {|
      preview := fun _ ab => ab;
      review := inl1
    |}.
  Proof.
    - auto.
    - auto. 
  Defined.

  Goal View (A +' B +' C +' D) (B +' D) (A +' C).
    (* Now yes. Needs some thinking, a bit of a mess right now *)
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
