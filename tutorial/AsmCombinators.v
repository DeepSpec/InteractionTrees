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
     ZArith
     Morphisms.
Import ListNotations.

From ITree Require Import
     ITree
     ITreeFacts
     SubKTree
     SubKTreeFacts
     Basics.Category.

From ExtLib Require Import
     Structures.Monad.

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
Definition relabel_bks {A B C D : nat} (f : F A -> F B) (g : F C -> F D)
           (b : bks B C) : bks A D :=
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

(* SAZ: rationalize the names of the combinators? *)
(** Another combinator that appends a list of instructions to the beginning of a
    block *)
Fixpoint blk_append {lbl} (l:list instr) (b:block lbl) : block lbl :=
  match l with
  | [] => b
  | i :: l' => bbi i (blk_append l' b)
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
 *)

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
Section Correctness.

  Context {E : Type -> Type}.
  Context {HasRegs : Reg -< E}.
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
      eapply eqit_bind; [| reflexivity].
      intros []; apply IHb.
    - (* If it's a jump, we consider the three cases. *)
      simpl.
      destruct br; simpl.
      + unfold ITree.map; rewrite bind_ret; reflexivity.
      + unfold ITree.map; rewrite bind_bind. 
        eapply eqit_bind; [| reflexivity].
        intros ?.
        flatten_goal; rewrite bind_ret; reflexivity.
      + rewrite (itree_eta (ITree.map _ _)).
        cbn. apply eqit_Vis. intros [].
  Qed.

  (** Denotes a list of instruction by binding the resulting trees. *)
  Definition denote_list: list instr -> itree E unit :=
    traverse_ denote_instr.

  (** Correctness of the [after] operator.
      Its denotation bind the denotation of the instructions
      with the one of the branch.
   *)

  Lemma denote_after :
    forall {label} instrs (b: branch (F label)),
      denote_block (after instrs b) ≅ (denote_list instrs ;; denote_branch b).
  Proof.
    induction instrs as [| i instrs IH]; intros b.
    - simpl; rewrite bind_ret; reflexivity.
    - simpl; rewrite bind_bind.
      eapply eqit_bind; try reflexivity.
      intros []; apply IH.
  Qed.

  Lemma denote_blk_append : forall lbl (l:list instr) (b:block (F lbl)),
      denote_block (blk_append l b) ≈ (x <- denote_list l ;; denote_block b).
  Proof.
    intros lbl.
    induction l; intros b; simpl.
    - rewrite bind_ret. reflexivity.
    - rewrite bind_bind.
      eapply eutt_clo_bind. reflexivity. red. intros. apply IHl. 
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

  Lemma raw_asm_correct {A B} (b : bks A B) :
    denote_asm (raw_asm b) ⩯ (fun a => denote_block (b a)).
  Proof.
    unfold denote_asm; cbn.
    rewrite loop_vanishing_1.
    rewrite unit_l'_id_sktree.
    rewrite unit_l_id_sktree.
    rewrite cat_id_l, cat_id_r.
    reflexivity.
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
    unfold raw_asm_block.
    rewrite raw_asm_correct.
    reflexivity.
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
    unfold pure_asm.
    rewrite raw_asm_correct.
    reflexivity.
  Qed.

  (** The identity gets denoted as the identity. *)
  Theorem id_asm_correct {A} :
    denote_asm (pure_asm id)
               ⩯ id_ A.
  Proof.
    rewrite pure_asm_correct; reflexivity.
  Defined.

  (** Correctness of the [relabel_asm] combinator.
      Its denotation is the same as denoting the original [asm],
      and composing it on both sides with the renaming functions
      lifted as [ktree]s.
   *)
  Lemma relabel_bks_correct: forall {A B C D: nat} (f: iFun A B) (g: iFun C D) k,
      denote_b (relabel_bks f g k) ⩯
               lift_sktree f >>> denote_b k >>> lift_sktree g. 
  Proof.
    intros.
    rewrite lift_compose_sktree, compose_sktree_lift.
    unfold relabel_bks, denote_b.
    intros a; rewrite fmap_block_map; reflexivity.
  Qed.

  Lemma app_bks_correct: forall {A B C D: nat} (ab: bks A B) (cd: bks C D),
    denote_b (app_bks ab cd) ⩯ bimap (denote_b ab) (denote_b cd).
  Proof.
    intros.
    rewrite unfold_bimap.
    unfold app_bks, denote_b.
    intros ?.
    unfold bimap, Bimap_Coproduct, case_, Case_ktree, case_sum.
    unfold cat, Cat_ktree, ITree.cat, isum_suml, isum_sum, sum_isuml, sum_isum, FinSum, merge_fin_sum, lift_ktree.
    cbn.
    rewrite bind_bind, bind_ret.
    destruct (split_fin_sum a).

    {
    rewrite bind_bind.
    rewrite (fmap_block_map (ab t)).
    unfold ITree.map.
    apply eqit_bind; [intros ? | reflexivity].
    unfold inl_, Inl_ktree, lift_ktree.
    rewrite bind_ret; reflexivity.
    }
    {
    rewrite bind_bind.
    rewrite (fmap_block_map (cd t)).
    unfold ITree.map.
    apply eqit_bind; [intros ? | reflexivity].
    unfold inr_, Inr_ktree, lift_ktree.
    rewrite bind_ret; reflexivity.
    }
  Qed.

    Global Instance CatAssoc_iFun : CatAssoc iFun.
    Proof with try typeclasses eauto.
      intros A B C D f g h.
      unfold cat, Cat_iFun.
      apply cat_Fun_assoc.
    Qed.

    Lemma bimap_inl
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif} {CaseInl_C : CaseInl C bif}:
      forall (a b c d : obj) (f : C a c) (g : C b d), inl_ >>> bimap f g ⩯ f >>> inl_.
    Proof.
      intros; unfold bimap, Bimap_Coproduct.
      apply case_inl; typeclasses eauto.
    Qed.

    Lemma bimap_inr
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif} {CaseInr_C : CaseInr C bif}:
      forall (a b c d : obj) (f : C a c) (g : C b d), inr_ >>> bimap f g ⩯ g >>> inr_.
    Proof.
      intros; unfold bimap, Bimap_Coproduct.
      apply case_inr; typeclasses eauto.
    Qed.
    
    Lemma assoc_r_inl
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
          {CaseInl_C : CaseInl C bif}:
      forall (a b c : obj), inl_ >>> @assoc_r _ _ _ _ a b c ⩯ case_ inl_ (inl_ >>> inr_).
    Proof.
      intros; unfold assoc_r, AssocR_Coproduct; apply case_inl; typeclasses eauto.
    Qed.

    Lemma assoc_r_inr
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
          {CaseInr_C : CaseInr C bif}:
      forall (a b c : obj), inr_ >>> @assoc_r _ _ _ _ a b c ⩯ inr_ >>> inr_.
    Proof.
      intros; unfold assoc_r, AssocR_Coproduct; apply case_inr; typeclasses eauto.
    Qed.

    Lemma assoc_l_inl
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
          {CaseInl_C : CaseInl C bif}:
      forall (a b c : obj), inl_ >>> @assoc_l _ _ _ _ a b c ⩯ inl_ >>> inl_.
    Proof.
      intros; unfold assoc_l, AssocR_Coproduct; apply case_inl; typeclasses eauto.
    Qed.

    Lemma assoc_l_inr
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
          {CaseInr_C : CaseInr C bif}:
      forall (a b c : obj), inr_ >>> @assoc_l _ _ _ _ a b c ⩯ case_ (inr_ >>> inl_) inr_.
    Proof.
      intros; unfold assoc_l, AssocR_Coproduct; apply case_inr; typeclasses eauto.
    Qed.

    Lemma swap_inl
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
          {CaseInl_C : CaseInl C bif}:
      forall (a b : obj), @inl_ _ _ _ _ a b >>> swap ⩯ inr_.
    Proof.
      intros; unfold swap, Swap_Coproduct; apply case_inl; typeclasses eauto. 
    Qed.

    Lemma swap_inr
          {obj : Type} {C : obj -> obj -> Type} {Eq2_C : Eq2 C} {Cat_C : Cat C} {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
          {CaseInr_C : CaseInr C bif}:
      forall (a b : obj), @inr_ _ _ _ _ a b >>> swap ⩯ inl_.
    Proof.
      intros; unfold swap, Swap_Coproduct; apply case_inr; typeclasses eauto. 
    Qed.


    Lemma swap_case
          {obj : Type} {C : obj -> obj -> Type}
          {Eq2_C : Eq2 C} {Eq2_Eq: forall a b : obj, @Equivalence (C a b) eq2}
          {Id_C : Id_ C} {Cat_C : Cat C}
          {Proper_cat : forall a b c, @Proper (C a b -> C b c -> C a c) (eq2 ==> eq2 ==> eq2) cat}
          {Category_C : Category C}
          {bif : obj -> obj -> obj}
          {CoprodCase_C : CoprodCase C bif} {CoprodInl_C : CoprodInl C bif} {CoprodInr_C : CoprodInr C bif}
          {Coproduct_C : Coproduct C bif}
          {CaseInr_C : CaseInr C bif}
          {Proper_case_ : forall a b c, @Proper (C a c -> C b c -> C _ c) (eq2 ==> eq2 ==> eq2) case_}:
      forall (a b c: obj) (f: C a c) (g: C b c), swap >>> case_ f g ⩯ case_ g f.
    Proof.
      intros; unfold swap, Swap_Coproduct.
      rewrite cat_case, inr_case, inl_case.
      reflexivity.
    Qed.

    Ltac inl_left := rewrite <- (cat_assoc _ inl_).
    Ltac inl_right := rewrite (cat_assoc _ inl_).
    Ltac inr_left := rewrite <- (cat_assoc _ inr_).
    Ltac inr_right := rewrite  (cat_assoc _ inr_).

  Ltac run_in :=
    repeat (
        rewrite cat_id_l
      + rewrite <- (cat_assoc inl_ assoc_l), assoc_l_inl
      + rewrite <- (cat_assoc inl_ assoc_r), assoc_r_inl
      + rewrite <- (cat_assoc inr_ assoc_r), assoc_r_inr
      + rewrite <- (cat_assoc inr_ assoc_l), assoc_l_inr
      + rewrite <- (cat_assoc inl_ (bimap _ _)), bimap_inl
      + rewrite <- (cat_assoc inr_ (bimap _ _)), bimap_inr
      + rewrite <- (cat_assoc inl_ (case_ _ _)), case_inl
      + rewrite <- (cat_assoc inr_ (case_ _ _)), case_inr
      + rewrite <- (cat_assoc inl_ swap), swap_inl
      + rewrite <- (cat_assoc inr_ swap), swap_inr
      + rewrite <- (cat_assoc swap (case_ _ _)), swap_case
      + rewrite ?assoc_l_inl, ?assoc_l_inr, ?assoc_r_inl, ?assoc_r_inr,
        ?bimap_inl, ?bimap_inr, ?case_inl, ?case_inr
      ).

  Local Lemma aux_app_asm_correct1 I J A C :
      (assoc_r >>>
       bimap (id_ I) (assoc_l >>> bimap swap (id_ C) >>> assoc_r) >>>
       assoc_l : sktree E ((I + J) + (A + C)) _)
    ⩯ bimap swap (id_ (A + C)) >>>
      (assoc_r >>>
      (bimap (id_ J) assoc_l >>>
      (assoc_l >>> (bimap swap (id_ C) >>> assoc_r)))).
  Proof.
    rewrite cat_assoc.
    apply coprod_split.
    - run_in. symmetry. rewrite cat_assoc. run_in.
      (* TODO: [rewrite cat_assoc] seems to loop on one side, hence [symmetry]...
         this is what prevents us from just adding [rewrite !cat_assoc] to
         [run_in] *)
      apply coprod_split.
      + run_in. repeat (rewrite cat_assoc; run_in).
        reflexivity.
      + run_in. repeat (rewrite cat_assoc; run_in).
        reflexivity.
    - run_in. rewrite cat_assoc. symmetry.
      repeat (rewrite cat_assoc; run_in).
      apply coprod_split.
      + run_in. repeat (rewrite cat_assoc; run_in).
        reflexivity.
      + run_in. repeat (rewrite cat_assoc; run_in).
        reflexivity.
  Qed.

  Local Lemma aux_app_asm_correct2 I J B D :
      (assoc_r >>>
       bimap (id_ I) (assoc_l >>> bimap swap (id_ D) >>> assoc_r) >>>
       assoc_l : sktree E _ ((I + J) + (B + D)))
    ⩯ assoc_l >>>
      (bimap swap (id_ D) >>>
      (assoc_r >>>
      (bimap (id_ J) assoc_r >>>
      (assoc_l >>> bimap swap (id_ (B + D)))))).
  Proof.
    simpl.
    rewrite cat_assoc.
    apply (coprod_split _ _).
    - run_in.
      symmetry. rewrite cat_assoc.
      run_in.
      rewrite cat_assoc.
      run_in.
      apply (coprod_split _ _).
      + repeat (rewrite cat_assoc; run_in).
        reflexivity.
      + repeat (rewrite cat_assoc; run_in).
        reflexivity.
    - run_in.
      rewrite cat_assoc. run_in.
      rewrite !cat_assoc; run_in.
      apply (coprod_split _ _).
      + run_in. repeat (rewrite !cat_assoc; run_in).
        reflexivity.
      + run_in. repeat (rewrite !cat_assoc; run_in).
        reflexivity.
  Qed.

  (** Correctness of the [app_asm] combinator.
      The resulting [asm] gets denoted to the bimap of its subcomponent.
      The proof is a bit more complicated. It makes a lot more sense if drawn.
   *)
  Theorem app_asm_correct {A B C D} (ab : asm A B) (cd : asm C D) :
    denote_asm (app_asm ab cd)
               ⩯ bimap (denote_asm ab) (denote_asm cd).
  Proof with try typeclasses eauto.
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
    rewrite loop_superposing.   (* a loop superposed atop another diagram can englob the latter *)
    rewrite loop_superposing_2. (* as well as if the loop is under... But it takes a bit more rewiring! *)
    rewrite loop_natural_left.  (* a loop append to diagrams can swallow them... *)
    rewrite loop_natural_right. (* ... from either side. *)
    rewrite loop_vanishing_2.   (* Finally, two nested loop can be combined. *)

    (* Remain now to relate the bodies of the loops on each side. *)
    (* First by some more equational reasoning. *)

    rewrite <- (loop_dinatural' swap swap) by apply swap_involutive.
    subst lhs.
    apply Proper_loop.
    rewrite !cat_assoc.
    repeat rewrite <- (cat_assoc _ _ (bimap (denote_b _) (denote_b _) >>> _)).
    cbn. rewrite relabel_bks_correct, app_bks_correct.
    rewrite cat_assoc.

    rewrite <- aux_app_asm_correct1, <- aux_app_asm_correct2.

    rewrite <- !compose_lift_sktree.
    rewrite <- !bimap_id_slift.
    rewrite <- !compose_lift_sktree.
    rewrite <- !bimap_slift_id.
    rewrite <- !assoc_r_sktree, <- !assoc_l_sktree, !sym_sktree_unfold.
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
    (* rewrite loop_natural_left, loop_natural_right.
    apply Proper_loop.
    *)
    rewrite loop_natural_left, loop_natural_right.
    apply Proper_loop.
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
    rewrite loop_vanishing_2.
    apply Proper_loop.
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
