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
Require Import Asm Utils_tutorial Label SubKTree SubKTreeFacts.

From Coq Require Import
     List
     Strings.String
     Program.Basics
     Vectors.Fin
     ZArith.
Import ListNotations.

From ITree Require Import
     ITree
     ITreeFacts.

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

(** Combinator to append two asm programs, preserving their internal links.
    Can be thought of as a "vertical composition", or a tensor product. 
 *)
(* We build a function from F X into block (F Y), we hence cannot use case_ whether over iFun or sktree.
   Can we do better?
 *)
Definition app_asm {A B C D} (ab : asm A B) (cd : asm C D) :
  asm (A + C) (B + D) :=
  {| internal := ab.(internal) + cd.(internal);
     code := fun l => match isum_sum l with
                   | inl iac => match isum_sum iac with
                               | inl ia => _app_B (ab.(code) (@inl_ _ iFun _ _ _ _ ia))
                               | inr ic => _app_D (cd.(code) (@inl_ _ iFun _ _ _ _ ic))
                               end
                   | inr ac => match isum_sum ac with
                              | inl a => _app_B (ab.(code) (@inr_ _ iFun _ _ _ _ a))
                              | inr c => _app_D (cd.(code) (@inr_ _ iFun _ _ _ _ c))
                              end
                   end
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
    induction b as [i b | br]; intros f.
    - simpl.
      unfold ITree.map; rewrite bind_bind.
      eapply eq_itree_eq_bind; try reflexivity.
      intros []; apply IHb.
    - simpl.
      destruct br; simpl.
      + unfold ITree.map; rewrite bind_ret; reflexivity.
      + unfold ITree.map; rewrite bind_bind. 
        eapply eq_itree_eq_bind; try reflexivity.
        intros ?.
        flatten_goal; rewrite bind_ret; reflexivity.
      + rewrite (itree_eta (ITree.map _ _)).
        cbn. apply eq_itree_Vis. intros [].
  Qed.

  Definition denote_list: list instr -> itree E unit :=
    traverse_ denote_instr.

  Lemma after_correct :
    forall {label: nat} instrs (b: branch (F label)),
      denote_block (after instrs b) ≅ (denote_list instrs ;; denote_branch b).
  Proof.
    induction instrs as [| i instrs IH]; intros b.
    - simpl; rewrite bind_ret; reflexivity.
    - simpl; rewrite bind_bind.
      eapply eq_itree_eq_bind; try reflexivity.
      intros []; apply IH.
  Qed.

  Lemma denote_list_app:
    forall is1 is2,
      @denote_list (is1 ++ is2) ≅
                   (@denote_list is1;; denote_list is2).
  Proof.
    intros is1 is2; induction is1 as [| i is1 IH]; simpl; intros; [rewrite bind_ret; reflexivity |].
    rewrite bind_bind; setoid_rewrite IH; reflexivity.
  Qed.


  Lemma raw_asm_block_correct_lifted {A} (b : block (F A)) :
    denote_asm (raw_asm_block b) ⩯
               ((fun _ => denote_block b) : ktree _ _ _).
  Proof.
    (*
    unfold denote_asm. simpl.
    rewrite vanishing_Label.
    rewrite case_l_Label'.
    setoid_rewrite case_l_Label .
    unfold denote_b; simpl.
    reflexivity.
  Qed.
     *)
  Admitted.

  Lemma raw_asm_block_correct {A} (b : block (t A)) :
    eutt eq (denote_asm (raw_asm_block b) F1)
         (denote_block b).
  Proof.
    apply raw_asm_block_correct_lifted.
  Qed.

  (** *** [asm] combinators *)

  Theorem pure_asm_correct {A B} (f : FinC A B) :
    denote_asm (pure_asm f)
               ⩯ @lift_ktree E _ _ f.
  Proof.
    unfold denote_asm .
  (*
    rewrite vanishing_Label.
    rewrite case_l_Label'.
    setoid_rewrite case_l_Label.
    unfold denote_b; simpl.
    intros ?.
    reflexivity.
  Qed.
     *)
  Admitted.


  Definition id_asm_correct {A} :
    denote_asm (pure_asm id)
               ⩯ id_ A.
  Proof.
    rewrite pure_asm_correct; reflexivity.
  Defined.

  Lemma fwd_eqn {a b : Type} (f g : ktree E a b) :
    (forall h, h ⩯ f -> h ⩯ g) -> f ⩯ g.
  Proof.
    intro H; apply H; reflexivity.
  Qed.

  Lemma cat_eq2_l {a b c : Type} (h : ktree E a b) (f g : ktree E b c) :
    f ⩯ g -> h >>> f ⩯ h >>> g.
  Proof.
    intros H; rewrite H; reflexivity.
  Qed.

  Lemma cat_eq2_r {a b c : Type} (h : ktree E b c) (f g : ktree E a b) :
    f ⩯ g -> f >>> h ⩯ g >>> h.
  Proof.
    intros H; rewrite H; reflexivity.
  Qed.

  Lemma local_rewrite1 {a b c : Type}:
    bimap (id_ a) (@swap _ (ktree E) _ _ b c) >>> assoc_l >>> swap
          ⩯ assoc_l >>> bimap swap (id_ c) >>> assoc_r.
  Proof.
    symmetry.
    apply fwd_eqn; intros h Eq.
    do 2 apply (cat_eq2_l (bimap (id_ _) swap)) in Eq.
    rewrite <- cat_assoc, bimap_cat, swap_involutive, cat_id_l,
    bimap_id, cat_id_l in Eq.
    rewrite <- (cat_assoc _ _ _ assoc_r), <- (cat_assoc _ _ assoc_l _)
      in Eq.
    rewrite <- swap_assoc_l in Eq.
    rewrite (cat_assoc _ _ _ assoc_r) in Eq.
    rewrite assoc_l_mono in Eq.
    rewrite cat_id_r in Eq.
    rewrite cat_assoc.
    assumption.
    all: typeclasses eauto.
  Qed.

  Lemma local_rewrite2 {a b c : Type}:
    swap >>> assoc_r >>> bimap (id_ _) swap
         ⩯ @assoc_l _ (ktree E) _ _ a b c >>> bimap swap (id_ _) >>> assoc_r.
  Proof.
    symmetry.
    apply fwd_eqn; intros h Eq.
    do 2 apply (cat_eq2_r (bimap (id_ _) swap)) in Eq.
    rewrite cat_assoc, bimap_cat, swap_involutive, cat_id_l,
    bimap_id, cat_id_r in Eq.
    rewrite 2 (cat_assoc _ assoc_l) in Eq.
    rewrite <- swap_assoc_r in Eq.
    rewrite <- 2 (cat_assoc _ assoc_l) in Eq.
    rewrite assoc_l_mono, cat_id_l in Eq.
    assumption.
    all: try typeclasses eauto.
  Qed.

  Lemma loop_bimap_ktree {I A B C D}
        (ab : ktree E A B) (cd : ktree E (I + C) (I + D)) :
    bimap ab (loop cd)
          ⩯ loop (assoc_l >>> bimap swap (id_ _)
                          >>> assoc_r
                          >>> bimap ab cd
                          >>> assoc_l >>> bimap swap (id_ _) >>> assoc_r).
  Proof.
    rewrite swap_bimap, bimap_ktree_loop.
    rewrite <- compose_loop, <- loop_compose.
    rewrite (swap_bimap _ _ cd ab).
    rewrite <- !cat_assoc.
    rewrite local_rewrite1.
    rewrite 2 cat_assoc.
    rewrite <- (cat_assoc _ swap assoc_r).
    rewrite local_rewrite2.
    rewrite <- !cat_assoc.
    reflexivity.
    all: typeclasses eauto.
  Qed.

  Definition app_asm_correct {A B C D} (ab : asm A B) (cd : asm C D) :
    denote_asm (app_asm ab cd)
               ⩯ bimap (denote_asm ab) (denote_asm cd).
  Proof.
    unfold denote_asm.

    match goal with | |- ?x ⩯ _ => set (lhs := x) end.
  (*
  rewrite loop_bimap_ktree.
  rewrite <- compose_loop.
  rewrite <- loop_compose.
  rewrite loop_loop.
  subst lhs.
  rewrite <- (loop_rename_internal' swap swap).
  2: apply swap_involutive; typeclasses eauto.
  apply eq_ktree_loop.
  rewrite !cat_assoc.
  rewrite <- !sym_ktree_unfold, !assoc_l_ktree, !assoc_r_ktree, !bimap_lift_id, !bimap_id_lift, !compose_lift_ktree_l, compose_lift_ktree.
  unfold cat, Cat_ktree, ITree.cat, lift_ktree.
  intro x. rewrite bind_ret; simpl.
  destruct x as [[|]|[|]]; cbn.
  (* ... *)
  all: unfold cat, Cat_ktree, ITree.cat.
  all: try typeclasses eauto.
  all: try rewrite bind_bind.
  all: unfold _app_B, _app_D.
  all: rewrite fmap_block_map.
  all: unfold ITree.map.
  all: apply eutt_bind; try reflexivity.
  all: intros []; rewrite (itree_eta (ITree.bind _ _)); cbn; reflexivity.
Qed.
   *)
  Admitted.

  Definition relabel_bks_correct {A B C D} (f : FinC A B) (g : FinC C D)
             (bc : bks B C) :
    denote_b (relabel_bks f g bc)
             ⩯ lift_ktree f >>> denote_b bc >>> lift_ktree g.
  Proof.
  (*
  rewrite lift_compose_ktree.
  rewrite compose_ktree_lift.
  intro a.
  unfold denote_b, relabel_bks.
  rewrite fmap_block_map.
  reflexivity.
Qed.
   *)
  Admitted.

  Definition relabel_asm_correct {A B C D} (f : FinC A B) (g : FinC C D)
             (bc : asm B C) :
    denote_asm (relabel_asm f g bc)
               ⩯ lift_ktree f >>> denote_asm bc >>> lift_ktree g.
  Proof.
  (*
  unfold denote_asm.
  simpl.
  rewrite relabel_bks_correct.
  rewrite <- compose_loop.
  rewrite <- loop_compose.
  apply eq_ktree_loop.
  rewrite !bimap_id_lift.
  reflexivity.
Qed.
   *)
  Admitted.

  Definition link_asm_correct {I A B} (ab : asm (I + A) (I + B)) :
    denote_asm (link_asm ab) ⩯ loop_Label (denote_asm ab).
  Proof.
    unfold denote_asm.
  (*
  rewrite loop_loop.
  apply eq_ktree_loop.
  simpl.
  rewrite relabel_bks_correct.
  rewrite <- assoc_l_ktree, <- assoc_r_ktree.
  reflexivity.
Qed.
   *)
  Admitted.
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
