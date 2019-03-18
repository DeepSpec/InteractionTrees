(** * Composition of [asm] programs *)

(** We develop in this file a theory of linking for [asm] programs.
    To this end, we will equip them with four main combinators:
    - [pure_asm], casting pure functions into [asm]. 
    - [app_asm], linking them vertically
    - [loop_asm], hiding internal links
    - [relabel_asm], allowing to rename labels
    Viewing [asm] units as diagrams, whose entry wires are the exposed labels of
    its blocks, and exit wires the external labels to which it may jump, this
    theory can be seen in particular as showing that they enjoy a structure of
    _traced monoidal category_.
    We do so by thinking of [ktree]s as a theory of linking at the denotational
    level. Each linking combinator is therefore proved correct by showing that
    the denotation of the resulting [asm], a [ktree],  can be swapped with the
    corresponding [ktree] combinator.
    It is interesting to notice that while the [ktree] theory, provided by the
    library, required heavy use of coinduction, it provides sufficient reasoning
    principles so that we do not need to write any cofix here.
 *)

(* begin hide *)
Require Import Imp Asm Utils_tutorial.

From Coq Require Import
     List
     Strings.String
     Program.Basics
     ZArith.
Import ListNotations.

From ITree Require Import
     Basics.Basics
     Basics.Function
     Basics.Category
     ITree
     KTree
     KTreeFacts.

From ExtLib Require Import
     Structures.Monad.

Typeclasses eauto := 5.
(* end hide *)

(* ================================================================= *)
(** ** Internal structures *)

(** A utility function to apply a renaming function [f] to the exit label of a [branch]. *)
Definition fmap_branch {A B : Type} (f: A -> B): branch A -> branch B :=
  fun b =>
    match b with
    | Bjmp a => Bjmp (f a)
    | Bbrz c a a' => Bbrz c (f a) (f a')
    | Bhalt => Bhalt
    end.

(** A utility function to apply a renaming function [f] to the exit label of a [block]. *)
Definition fmap_block {A B: Type} (f: A -> B): block A -> block B :=
  fix fmap b :=
    match b with
    | bbb a => bbb (fmap_branch f a)
    | bbi i b => bbi i (fmap b)
    end.

(** A utility function to apply renaming functions [f] and [g] respectively to
    the entry and exit labels of a [bks]. *)
Definition relabel_bks {A B C D : Type} (f : A -> B) (g : C -> D)
           (b : bks B C) : bks A D :=
  fun a => fmap_block g (b (f a)).

(** Simple combinator to build a [block] from its instructions and branch operation. *)
Fixpoint after {A: Type} (is : list instr) (bch : branch A) : block A :=
  match is with
  | nil => bbb bch
  | i :: is => bbi i (after is bch)
  end.

(* ================================================================= *)
(** ** Low-level interface with [asm] *)

(** Any collection of blocks forms an [asm] program with no hidden blocks. *)
Definition raw_asm {A B} (b : bks A B) : asm A B :=
  {| internal := void;
     code := fun a' =>
               match a' with
               | inl v => match v : void with end
               | inr a => fmap_block inr (b a)
               end;
  |}.

(** And so does a single [block] in particular. *)
Definition raw_asm_block {A} (b : block A) : asm unit A :=
  raw_asm (fun _ => b).

(** ** [asm] combinators *)

(** We now turn to the proper [asm] combinators. *)

(** An [asm] program made only of external jumps.
    This is useful to connect programs with [app_asm]. *)
Definition pure_asm {A B} (f : A -> B) : asm A B :=
  raw_asm (fun a => bbb (Bjmp (f a))).

Definition id_asm {A} : asm A A := pure_asm id.

(** The [app_asm] combinator joins two [asm] programs, 
    preserving their internal links.
    Since the three ambient domains of labels are extended,
    the only tricky part is to rename all labels appropriately.
    The two following functions take care of this internal
    relabelling.
 *)
Definition _app_B {I J B D} :
  block (I + B) -> block ((I + J) + (B + D)) :=
  fmap_block (fun l =>
                match l with
                | inl i => inl (inl i)
                | inr b => inr (inl b)
                end).

Definition _app_D {I J B D} :
  block (J + D) -> block ((I + J) + (B + D)) :=
  fmap_block (fun l =>
                match l with
                | inl j => inl (inr j)
                | inr d => inr (inr d)
                end).

(** Combinator to append two asm programs, preserving their internal links.
    Can be thought of as a "vertical composition", or a tensor product. 
 *)
Definition app_asm {A B C D} (ab : asm A B) (cd : asm C D) :
  asm (A + C) (B + D) :=
  {| internal := ab.(internal) + cd.(internal);
     code := fun l =>
               match l with
               | inl (inl ia) => _app_B (ab.(code) (inl ia))
               | inl (inr ic) => _app_D (cd.(code) (inl ic))
               | inr (inl  a) => _app_B (ab.(code) (inr  a))
               | inr (inr  c) => _app_D (cd.(code) (inr  c))
               end;
  |}.

(** Rename visible program labels.
    Having chosen to represent labels as binary trees encoded in [Type],
    we, for instance, typically need to rename our visible labels through
    associators.
    The following generic combinator allow any relabelling. 
 *)
Definition relabel_asm {A B C D} (f : A -> B) (g : C -> D)
           (bc : asm B C) : asm A D :=
  {| code := relabel_bks (bimap id f) (bimap id g) bc.(code);
  |}.

(** Labels that are exposed both as entry and exit points can be internalized.
    This operation can be seen as linking two programs internal to [ab] together.
 *)
Definition link_asm {I A B} (ab : asm (I + A) (I + B)) : asm A B :=
  {| internal := ab.(internal) + I;
     code := relabel_bks assoc_r assoc_l ab.(code);
  |}.

(* ================================================================= *)
(** ** Correctness *)
(** We show the combinators correct by proving that their denotation
    map to their [ktree] counterparts.
    Since these combinators are the basic blocks we'll use in the
    compiler to link compiled subterms, these correctness lemmas
    will provide an equational theory sufficient to conduct
    all needed reasoning.
    Interestingly, [ktree] provides a sufficiently rich theory to
    prove all these results involving [denote_asm], which is expressed
    as a [loop], equationally.
 *)

(* begin hide *)
Import MonadNotation.
Import ITreeNotations.
Import CatNotations.
Local Open Scope cat.
(* end hide *)

Section Correctness.

  (** We reason about the denotation of [asm] programs, we therefore
   need an appropriate domain of events [E]. *)
  Context {E : Type -> Type}.
  Context {HasLocals : Locals -< E}.
  Context {HasMemory : Memory -< E}.
  Context {HasExit : Exit -< E}.

  (** *** Internal structures *)

  (** Commutes denotation an [fmap] *)
  Lemma fmap_block_map:
    forall  {L L'} b (f: L -> L'),
      denote_block (fmap_block f b) ≅ ITree.map f (denote_block b).
  Proof.
    (* Induction over the structure of the [block b] *)
    induction b as [i b | br]; intros f.
    - (* If it contains an instruction (inductive case). *)
      simpl.
      unfold ITree.map; rewrite bind_bind.
      eapply eq_itree_eq_bind; [| reflexivity].
      intros []; apply IHb.
    - (* If it's a jump, we consider the three cases. *)
      simpl.
      destruct br; simpl.
      + unfold ITree.map; rewrite bind_ret; reflexivity.
      + unfold ITree.map; rewrite bind_bind. 
        eapply eq_itree_eq_bind; [| reflexivity].
        intros ?.
        flatten_goal; rewrite bind_ret; reflexivity.
      + rewrite (itree_eta (ITree.map _ _)).
        cbn. apply eq_itree_Vis. intros [].
  Qed.

  (** Denotes a list of instruction by binding the resulting trees. *)
  Definition denote_list: list instr -> itree E unit :=
    traverse_ denote_instr.

  (** Correctness of the [after] operator.
      Its denotation bind the denotation of the instructions
      with the one of the branch.
   *)
  Lemma after_correct :
    forall {label: Type} instrs (b: branch label),
      denote_block (after instrs b) ≅ (denote_list instrs ;; denote_branch b).
  Proof.
    induction instrs as [| i instrs IH]; intros b.
    - simpl; rewrite bind_ret; reflexivity.
    - simpl; rewrite bind_bind.
      eapply eq_itree_eq_bind; try reflexivity.
      intros []; apply IH.
  Qed.

  (** Utility: denoting the [app] of two lists of instructions binds the denotations. *)
  Lemma denote_list_app:
    forall is1 is2,
      @denote_list (is1 ++ is2) ≅ (@denote_list is1;; denote_list is2).
  Proof.
    intros is1 is2; induction is1 as [| i is1 IH]; simpl; intros; [rewrite bind_ret; reflexivity |].
    rewrite bind_bind; setoid_rewrite IH; reflexivity.
  Qed.

  (** Correctness of the [raw_asm] operator.
      Its denotation is the same as the denotation of the block.
      Since it is hybrid between the level of [ktree]s (asm) and
      [itree]s (block), the correctness is established at both
      level for convenience.
      Note that the ⩯ notation in the scope of [ktree] desugars to [eutt_ktree],
      i.e. pointwise [eutt eq].
   *)
  Lemma raw_asm_block_correct_lifted {A} (b : block A) :
    denote_asm (raw_asm_block b) ⩯
               ((fun _ : unit => denote_block b) : ktree _ _ _).
  Proof.
    unfold denote_asm.
    rewrite vanishing_ktree.
    rewrite case_l_ktree', case_l_ktree.
    unfold denote_b; simpl.
    intros [].
    rewrite fmap_block_map, map_map.
    unfold ITree.map.
    rewrite <- (bind_ret2 (denote_block b)) at 2.
    reflexivity.
  Qed.

  Lemma raw_asm_block_correct {A} (b : block A) :
    (denote_asm (raw_asm_block b) tt) ≈ (denote_block b).
  Proof.
    apply raw_asm_block_correct_lifted.
  Qed.

  (** *** [asm] combinators *)

  (** Correctness of the [pure_asm] combinator.
      Its denotation is the lifting of a pure function
      into a [ktree].
   *)
  Theorem pure_asm_correct {A B} (f : A -> B) :
    denote_asm (pure_asm f) ⩯ @lift_ktree E _ _ f.
  Proof.
    unfold denote_asm .
    rewrite vanishing_ktree. (* a pure_asm contains no internal label: we can remove them from the loop *)
    rewrite case_l_ktree', case_l_ktree.
    unfold denote_b; simpl.
    intros ?.
    rewrite map_ret.
    reflexivity.
  Qed.

  (** The identity gets denoted as the identity. *)
  Theorem id_asm_correct {A} :
    denote_asm (pure_asm id)
               ⩯ id_ A.
  Proof.
    rewrite pure_asm_correct; reflexivity.
  Defined.

  (** Correctness of the [app_asm] combinator.
      The resulting [asm] gets denoted to the bimap of its subcomponent.
      The proof is a bit more complicated. It makes a lot more sense if drawn.
   *)
  Theorem app_asm_correct {A B C D} (ab : asm A B) (cd : asm C D) :
    denote_asm (app_asm ab cd)
               ⩯ bimap (denote_asm ab) (denote_asm cd).
  Proof.
    unfold denote_asm.
    (*
      On the left-hand-side, we have a [loop] of two [asm] mashed together.
      On the right-hand-side however we have two [loop]s combined together.
      The game is to massage them through successive rewriting until they
      line up.
     *)

    (* We first work on the rhs to reduce it to a single loop.
       The textual explanations are fairly cryptic. The key intuition comes
       by drawing the state of the circuit and using the rewiring laws
       the categorical structure provides, as represented for instance here:
       https://en.wikipedia.org/wiki/Traced_monoidal_category
       [bimap_ktree_loop] and [loop_bimap_ktree] are the _superposing_ laws.
       [compose_loop] and [loop_compose] are the _naturality_ in _X_ and _Y_.
       [loop_loop] is the second _vanishing_ law.
     *)
    match goal with | |- ?x ⩯ _ => set (lhs := x) end.
    rewrite bimap_ktree_loop. (* a loop superposed atop another diagram can englob the latter *)
    rewrite loop_bimap_ktree. (* as well as if the loop is under... But it takes a bit more rewiring! *)
    rewrite <- compose_loop.   (* a loop append to diagrams can swallow them... *)
    rewrite <- loop_compose.   (* ... from either side. *)
    rewrite loop_loop.        (* Finally, two nested loop can be combined. *)

    subst lhs.
    (* Remain now to relate the bodies of the loops on each side. *)
    (* First by some more equational reasoning. *)
    rewrite <- (loop_rename_internal' swap swap).
    2: apply swap_involutive; typeclasses eauto.
    apply eq_ktree_loop.
    rewrite !cat_assoc; try typeclasses eauto.
    rewrite <- !sym_ktree_unfold, !assoc_l_ktree, !assoc_r_ktree, !bimap_lift_id, !bimap_id_lift, !compose_lift_ktree_l, compose_lift_ktree.

    (* And finally a case analysis on the label provided. *)
    unfold cat, Cat_ktree, ITree.cat, lift_ktree.
    intro x. rewrite bind_ret; simpl.
    destruct x as [[|]|[|]]; cbn.
    (* ... *)
    all: unfold cat, Cat_ktree, ITree.cat.
    all: try rewrite bind_bind.
    all: unfold _app_B, _app_D.
    all: rewrite fmap_block_map.
    all: unfold ITree.map.
    all: apply eutt_bind; try reflexivity.
    all: intros []; rewrite (itree_eta (ITree.bind _ _)); cbn; reflexivity.
  Qed.

  (** Correctness of the [relabel_asm] combinator.
      Its denotation is the same as denoting the original [asm],
      and composing it on both sides with the renaming functions
      lifted as [ktree]s.
   *)
  Lemma relabel_bks_correct {A B C D} (f : A -> B) (g : C -> D)
             (bc : bks B C) :
    denote_b (relabel_bks f g bc)
             ⩯ lift_ktree f >>> denote_b bc >>> lift_ktree g.
  Proof.
    rewrite lift_compose_ktree.
    rewrite compose_ktree_lift.
    intro a.
    unfold denote_b, relabel_bks.
    rewrite fmap_block_map.
    reflexivity.
  Qed.

  Theorem relabel_asm_correct {A B C D} (f : A -> B) (g : C -> D)
             (bc : asm B C) :
    denote_asm (relabel_asm f g bc)
               ⩯ lift_ktree f >>> denote_asm bc >>> lift_ktree g.
  Proof.
    unfold denote_asm.
    simpl.
    rewrite relabel_bks_correct.
    rewrite <- compose_loop.
    rewrite <- loop_compose.
    apply eq_ktree_loop.
    rewrite !bimap_id_lift.
    reflexivity.
  Qed.

  (** Correctness of the [link_asm] combinator.
      Linking is exactly looping, it hides internal labels/wires.
   *)
  Theorem link_asm_correct {I A B} (ab : asm (I + A) (I + B)) :
    denote_asm (link_asm ab) ⩯ loop (denote_asm ab).
  Proof.
    unfold denote_asm.
    rewrite loop_loop.
    apply eq_ktree_loop.
    simpl.
    rewrite relabel_bks_correct.
    rewrite <- assoc_l_ktree, <- assoc_r_ktree.
    reflexivity.
  Qed.

End Correctness.

(** We have defined four low-level combinators allowing us to combine [asm]
    programs together. These combinators are correct in the sense that
    their denotation is bisimilar to their denotational counterparts at the
    [ktree] level.
    This theory of linking is only tied to _Asm_, and can therefore be reused
    either for other compilers targetting Asm, or for optimizations over Asm. 
    We now turn to its specific use to finally define our compiler, defined
    in [Imp2Asm.v].
 *)