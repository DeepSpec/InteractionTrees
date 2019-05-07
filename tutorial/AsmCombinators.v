(** * Composition of [asm] programs *)

(** We develop in this file a theory of linking for [asm] programs.
    To this end, we will equip them with four main combinators:
    - [pure_asm], casting pure functions into [asm]. 
    - [app_asm], linking them vertically
    - [link_asm], hiding internal links
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
Require Import Asm Utils_tutorial Label.

From Coq Require Import
     List
     Strings.String
     Program.Basics
     Vectors.Fin
     ZArith.
Import ListNotations.

From ITree Require Import
     ITree
     ITreeFacts
     SubKTree
     SubKTreeFacts.

From ExtLib Require Import
     Structures.Monad.

Typeclasses eauto := 5.
Import CatNotations.
Local Open Scope cat_scope.
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
Definition relabel_bks {A B X D : nat} (f : F A -> F B) (g : F X -> F D)
           (b : bks B X) : bks A D :=
  fun a => fmap_block g (b (f a)).

Definition app_bks {A B C D : nat} (ab : bks A B) (cd : bks C D)
  : bks (A + C) (B + D) :=
  fun ac =>
    match split_fin_sum ac with
    | inl a => fmap_block (L _) (ab a)
    | inr c => fmap_block (R _) (cd c)
    end.

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
  {| internal := 0;
     code := fun l => b l
  |}.

(** And so does a single [block] in particular. *)
Definition raw_asm_block {A: nat} (b : block (F A)) : asm 1 A :=
  raw_asm (fun _ => b).

(** ** [asm] combinators *)

(** We now turn to the proper [asm] combinators. *)

(** An [asm] program made only of external jumps.
    This is useful to connect programs with [app_asm]. *)
Definition pure_asm {A B: nat} (f : F A -> F B) : asm A B :=
  raw_asm (fun a => bbb (Bjmp (f a))).

Definition id_asm {A} : asm A A := pure_asm id.

(** The [app_asm] combinator joins two [asm] programs, 
    preserving their internal links.
    Since the three ambient domains of labels are extended,
    the only tricky part is to rename all labels appropriately.
    The two following functions take care of this internal
    relabelling.
 *)
Definition _app_B {I J B D: nat} :
  block (F (I + B)) -> block (F ((I + J) + (B + D))) :=
  fmap_block (case_ (inl_ >>> inl_) (inl_ >>> inr_)).

Definition _app_D {I J B D} :
  block (F (J + D)) -> block (F ((I + J) + (B + D))) :=
  fmap_block (case_ (inr_ >>> inl_) (inr_ >>> inr_)).

Notation Foo :=
(assoc_r >>> bimap (id_ _) (assoc_l >>> bimap swap (id_ _) >>> assoc_r) >>> assoc_l : iFun _ _).

(** Combinator to append two asm programs, preserving their internal links.
    Can be thought of as a "vertical composition", or a tensor product. 
 *)
(* We build a function from F X into block (F Y), we hence cannot use case_ whether over iFun or sktree.
   Can we do better?
 *)
Definition app_asm {A B C D} (ab : asm A B) (cd : asm C D) :
  asm (A + C) (B + D) :=
  {| internal := ab.(internal) + cd.(internal);
     code := relabel_bks Foo Foo (app_bks ab.(code) cd.(code))
  |}.

(** Rename visible program labels.
    Having chosen to represent labels as binary trees encoded in [Type],
    we, for instance, typically need to rename our visible labels through
    associators.
    The following generic combinator allow any relabelling. 
 *)
Definition relabel_asm {A B C D} (f : F A -> F B) (g : F C -> F D)
           (bc : asm B C) : asm A D :=
  {| code := relabel_bks (bimap id f) (bimap id g)  bc.(code); |}.

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
Import Imp.
Section Correctness.

  Context {E : Type -> Type}.
  Context {HasLocals : Locals -< E}.
  Context {HasMemory : Memory -< E}.
  Context {HasExit : Exit -< E}.

  (** *** Internal structures *)

  Lemma fmap_block_map:
    forall  {L L'} b (f: F L -> F L'),
      denote_block (fmap_block f b) ≅ ITree.map f (denote_block b).
  Proof.
    (* Induction over the structure of the [block b] *)
    induction b as [i b | br]; intros f.
    - (* If it contains an instruction (inductive case). *)
      simpl.
      unfold ITree.map; rewrite bind_bind.
      eapply eq_itree_bind; [| reflexivity].
      intros []; apply IHb.
    - (* If it's a jump, we consider the three cases. *)
      simpl.
      destruct br; simpl.
      + unfold ITree.map; rewrite bind_ret; reflexivity.
      + unfold ITree.map; rewrite bind_bind. 
        eapply eq_itree_bind; [| reflexivity].
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
    forall {label: nat} instrs (b: branch (F label)),
      denote_block (after instrs b) ≅ (denote_list instrs ;; denote_branch b).
  Proof.
    induction instrs as [| i instrs IH]; intros b.
    - simpl; rewrite bind_ret; reflexivity.
    - simpl; rewrite bind_bind.
      eapply eq_itree_bind; try reflexivity.
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

  Lemma lift_ktree_inr {A B} : @lift_ktree E A (B + A) inr = inr_.
  Proof. reflexivity. Qed.

  Lemma unit_l'_id_sktree {n : nat} : (@unit_l' _ (sktree E) plus 0 _ n) ⩯ id_ n.
  Proof.
    intros ?. tau_steps; symmetry; tau_steps. reflexivity.
  Qed.

  Lemma unit_l_id_sktree {n : nat} : (@unit_l _ (sktree E) plus 0 _ n) ⩯ id_ n.
  Proof.
    intros ?. tau_steps; symmetry; tau_steps. reflexivity.
  Qed.

  (** Correctness of the [raw_asm] operator.
      Its denotation is the same as the denotation of the block.
      Since it is hybrid between the level of [ktree]s (asm) and
      [itree]s (block), the correctness is established at both
      level for convenience.
      Note that the ⩯ notation in the scope of [ktree] desugars to [eutt_ktree],
      i.e. pointwise [eutt eq].
   *)
  Lemma raw_asm_block_correct_lifted {A} (b : block (F A)) :
    denote_asm (raw_asm_block b) ⩯
               ((fun _  => denote_block b) : sktree _ _ _).
  Proof.
    unfold denote_asm; cbn.
    unfold denote_asm.
    rewrite vanishing_sktree.
    rewrite unit_l'_id_sktree, unit_l_id_sktree, cat_id_r, cat_id_l.
    reflexivity.
    all: typeclasses eauto.
  Qed.

  Lemma raw_asm_block_correct {A} (b : block (F A)) :
    (denote_asm (raw_asm_block b) F1) ≈ (denote_block b).
  Proof.
    apply raw_asm_block_correct_lifted.
  Qed.

  (** *** [asm] combinators *)

  (** Correctness of the [pure_asm] combinator.
      Its denotation is the lifting of a pure function
      into a [ktree].
   *)
  Theorem pure_asm_correct {A B} (f : F A -> F B) :
    denote_asm (pure_asm f) ⩯ lift_sktree f.
  Proof.
    unfold denote_asm.
    rewrite vanishing_sktree. (* a pure_asm contains no internal label: we can remove them from the loop *)
    rewrite unit_l'_id_sktree, unit_l_id_sktree, cat_id_r, cat_id_l.
    reflexivity.
    all: typeclasses eauto.
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
    rewrite bimap_sktree_loop. (* a loop superposed atop another diagram can englob the latter *)
    rewrite loop_bimap_sktree. (* as well as if the loop is under... But it takes a bit more rewiring! *)
    rewrite <- compose_sloop.   (* a loop append to diagrams can swallow them... *)
    rewrite <- sloop_compose.   (* ... from either side. *)
    rewrite sloop_sloop.       (* Finally, two nested loop can be combined. *)

    subst lhs.
    (* Remain now to relate the bodies of the loops on each side. *)
    (* First by some more equational reasoning. *)
    rewrite <- (sloop_rename_internal' swap swap).
    2: apply swap_involutive; typeclasses eauto.
    apply eq_sktree_sloop.
    rewrite !cat_assoc; try typeclasses eauto.
    rewrite <- !sym_sktree_unfold, !assoc_l_sktree, !assoc_r_sktree, !bimap_slift_id, !bimap_id_slift, !compose_lift_sktree_l, compose_lift_sktree.
    cbn.

(*
    (* And finally a case analysis on the label provided. *)
    (* TODO Things get wonky here with sktrees *)
    unfold cat, Cat_sktree, cat, Cat_ktree, Cat_iFun, ITree.cat, lift_sktree, lift_ktree.
    intro x; unfold denote_b; simpl.
    rewrite bind_ret; simpl.
    repeat match goal with
           | |- context[match ?pat with | _ => _ end] => destruct pat eqn:?EQ
           end; cbn.
*)
    (*
    {
      all: unfold _app_B, _app_D.
      all: rewrite fmap_block_map.
      all: unfold ITree.map.
      unfold compose.
      rewrite !unfold_bimap_iFun.
      rewrite !unfold_assoc_r_iFun.
      rewrite !unfold_assoc_l_iFun.
      unfold case_, case_isum.
      unfold inl_, isum_inl.
      unfold inr_, isum_inr.
      cbn.
      Set Printing Implicit.
      unfold bimap, Bimap_Coproduct.
      unfold case_, Case_sktree_, Case_sktree, case_isum; cbn.
     *)      
    (* (* ... *) *)
    (* all: unfold cat, Cat_ktree, ITree.cat. *)
    (* (* all: try rewrite bind_bind. *) *)
    (* all: unfold _app_B, _app_D. *)
    (* all: rewrite fmap_block_map. *)
    (* all: unfold ITree.map. *)
    (* all: apply eutt_bind; try reflexivity. *)
    (* all: intros []; rewrite (itree_eta (ITree.bind _ _)); cbn; reflexivity. *)
  Admitted.

  (** Correctness of the [relabel_asm] combinator.
      Its denotation is the same as denoting the original [asm],
      and composing it on both sides with the renaming functions
      lifted as [ktree]s.
   *)
  Lemma relabel_bks_correct {A B C D} (f : F A -> F B) (g : F C -> F D)
             (bc : bks B C) :
    denote_b (relabel_bks f g bc)
             ⩯ lift_sktree f >>> denote_b bc >>> lift_sktree g.
  Proof.
    rewrite lift_compose_sktree.
    rewrite compose_sktree_lift.
    intro a.
    unfold denote_b, relabel_bks.
    rewrite fmap_block_map.
    reflexivity.
  Qed.

  Theorem relabel_asm_correct {A B C D} (f : F A -> F B) (g : F C -> F D)
             (bc : asm B C) :
    denote_asm (relabel_asm f g bc)
               ⩯ lift_sktree f >>> denote_asm bc >>> lift_sktree g.
  Proof.
    unfold denote_asm.
    simpl.
    rewrite relabel_bks_correct.
    rewrite <- compose_sloop.
    rewrite <- sloop_compose.
    apply eq_sktree_sloop.
    rewrite !bimap_id_slift.
    reflexivity.
  Qed.

  (** Correctness of the [link_asm] combinator.
      Linking is exactly looping, it hides internal labels/wires.
   *)
  Theorem link_asm_correct {I A B} (ab : asm (I + A) (I + B)) :
    denote_asm (link_asm ab) ⩯ sloop (denote_asm ab).
  Proof.
    unfold denote_asm.
    rewrite sloop_sloop.
    apply eq_sktree_sloop.
    simpl.
    rewrite relabel_bks_correct.
    rewrite <- assoc_l_sktree, <- assoc_r_sktree.
    reflexivity.
  Qed.

End Correctness.

(** We have defined four low-level combinators allowing us to combine [asm]
    programs together. These combinators are correct in the sense that
    their denotation is bisimilar to their denotational counterparts at the
    [ktree] level.
    This theory of linking is only tied to _Asm_, and can therefore be reused
    either for other compilers targeting Asm, or for optimizations over Asm. 
    We now turn to its specific use to finally define our compiler, defined
    in [Imp2Asm.v].
 *)
