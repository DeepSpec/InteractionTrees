(** * Composition of [asm] programs *)

Require Import Asm.

From Coq Require Import
     List
     Strings.String
     Program.Basics.
Import ListNotations.
From ITree Require Import Basics_Functions.
Require Import ZArith.

Typeclasses eauto := 5.

(** ** Internal structures *)

Definition fmap_branch {A B : Type} (f: A -> B): branch A -> branch B :=
  fun b =>
    match b with
    | Bjmp a => Bjmp (f a)
    | Bbrz c a a' => Bbrz c (f a) (f a')
    | Bhalt => Bhalt
    end.

Definition fmap_block {A B: Type} (f: A -> B): block A -> block B :=
  fix fmap b :=
    match b with
    | bbb a => bbb (fmap_branch f a)
    | bbi i b => bbi i (fmap b)
    end.

Definition relabel_bks {A B C D : Type} (f : A -> B) (g : C -> D)
           (b : bks B C) : bks A D :=
  fun a => fmap_block g (b (f a)).

Section after.
Context {A : Type}.
Fixpoint after (is : list instr) (bch : branch A) : block A :=
  match is with
  | nil => bbb bch
  | i :: is => bbi i (after is bch)
  end.
End after.

(** ** Low-level interface with [asm] *)

(** Any collection of blocks forms an [asm] program with
      no hidden blocks. *)
Definition raw_asm {A B} (b : bks A B) : asm A B :=
  {| internal := Empty_set;
     code := fun a' =>
               match a' with
               | inl v => match v : Empty_set with end
               | inr a => fmap_block inr (b a)
               end;
  |}.

(** Wrap a single block as [asm]. *)
Definition raw_asm_block {A} (b : block A) : asm unit A :=
  raw_asm (fun _ => b).

(** ** [asm] combinators *)

(** An [asm] program made only of external jumps. This is
      useful to connect programs with [app_asm]. *)
Definition pure_asm {A B} (f : A -> B) : asm A B :=
  raw_asm (fun a => bbb (Bjmp (f a))).

Definition id_asm {A} : asm A A := pure_asm id.

(* Internal relabeling functions for [app_asm] *)
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

(** Append two asm programs, preserving their internal links. *)
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

(** Rename visible program labels. *)
Definition relabel_asm {A B C D} (f : A -> B) (g : C -> D)
           (bc : asm B C) : asm A D :=
  {| code := relabel_bks (sum_bimap id f) (sum_bimap id g) bc.(code);
  |}.

(** Link labels from two programs together. *)
Definition link_asm {I A B} (ab : asm (I + A) (I + B)) : asm A B :=
  {| internal := ab.(internal) + I;
     code := relabel_bks sum_assoc_r sum_assoc_l ab.(code);
  |}.

(** ** Correctness *)
(** The combinators above map to their denotational counterparts. *)

From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.
From ITree Require Import
     ITree KTree.
Require Import Imp.

Section Correctness.

Context {E : Type -> Type}.
Context {HasLocals : Locals -< E}.
Context {HasMemory : Memory -< E}.
Context {HasExit : Exit -< E}.

(** *** Internal structures *)

Lemma fmap_block_map:
  forall  {L L'} b (f: L -> L'),
    denote_block (fmap_block f b) ≅ ITree.map f (denote_block b).
Proof.
  induction b as [i b | br]; intros f.
  - simpl.
    unfold ITree.map; rewrite bind_bind.
    eapply eq_itree_eq_bind; [reflexivity | intros []; apply IHb].
  - simpl.
    destruct br; simpl.
    + unfold ITree.map; rewrite ret_bind; reflexivity.
    + unfold ITree.map; rewrite bind_bind.
      eapply eq_itree_eq_bind; [reflexivity | intros []; rewrite ret_bind; reflexivity].
    + rewrite (itree_eta (ITree.map _ _)).
      cbn. apply eq_itree_vis. intros [].
Qed.

Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
  fix traverse__ l: M unit :=
    match l with
    | [] => ret tt
    | a::l => (f a;; traverse__ l)%monad
    end.

Definition denote_list: list instr -> itree E unit :=
  traverse_ denote_instr.

Lemma after_correct :
  forall {label: Type} instrs (b: branch label),
    denote_block (after instrs b) ≅ (denote_list instrs ;; denote_branch b).
Proof.
  induction instrs as [| i instrs IH]; intros b.
  - simpl; rewrite ret_bind; reflexivity.
  - simpl; rewrite bind_bind.
    eapply eq_itree_eq_bind; [reflexivity | intros []; apply IH].
Qed.

Lemma denote_list_app:
  forall is1 is2,
    @denote_list (is1 ++ is2) ≅
                 (@denote_list is1;; denote_list is2).
Proof.
  intros is1 is2; induction is1 as [| i is1 IH]; simpl; intros; [rewrite ret_bind; reflexivity |].
  rewrite bind_bind; setoid_rewrite IH; reflexivity.
Qed.

(* TO MOVE *)
Lemma map_ret {X Y: Type}:
  forall (f: X -> Y) x,
    @ITree.map E _ _ f (Ret x) ≅ Ret (f x).
Proof.
  intros.
  unfold ITree.map.
  rewrite ret_bind; reflexivity.
Qed.

Lemma raw_asm_block_correct_lifted {A} (b : block A) :
   denote_asm (raw_asm_block b) ⩯
          (fun _ => denote_block b).
Proof.
  unfold denote_asm.
  rewrite vanishing_ktree.
  rewrite elim_l_ktree', elim_l_ktree.
  unfold denote_b; simpl.
  intros [].
  rewrite fmap_block_map, map_map.
  unfold ITree.map.
  rewrite <- (bind_ret (denote_block b)) at 2.
  reflexivity.
Qed.

Lemma raw_asm_block_correct {A} (b : block A) :
  eutt eq (denote_asm (raw_asm_block b) tt)
          (denote_block b).
Proof.
  apply raw_asm_block_correct_lifted.
Qed.

(** *** [asm] combinators *)

Theorem pure_asm_correct {A B} (f : A -> B) :
    denote_asm (pure_asm f)
  ⩯ @lift_ktree E _ _ f.
Proof.
  unfold denote_asm .
  rewrite vanishing_ktree.
  rewrite elim_l_ktree', elim_l_ktree.
  unfold denote_b; simpl.
  intros ?.
  rewrite map_ret.
  reflexivity.
Qed.

Definition id_asm_correct {A} :
    denote_asm (pure_asm id)
  ⩯ @id_ktree E A.
Proof.
  rewrite pure_asm_correct; reflexivity.
Defined.

Lemma tensor_ktree_slide_right {A B C D}:
  forall (ac: ktree E A C) (bd: ktree E B D),
    ac ⊗ bd ⩯ id_ktree ⊗ bd >=> ac ⊗ id_ktree.
Proof.
  intros.
  unfold tensor_ktree.
  repeat rewrite id_ktree_left.
  rewrite sum_elim_compose.
  rewrite compose_ktree_assoc.
  rewrite inl_sum_elim, inr_sum_elim.
  reflexivity.
Qed.

Lemma local_rewrite1 {A B C: Type}:
  id_ktree ⊗ sym_ktree >=> assoc_ktree_l >=> sym_ktree ⩯
         @assoc_ktree_l E A B C >=> sym_ktree ⊗ id_ktree >=> assoc_ktree_r.
Proof.
  unfold id_ktree, tensor_ktree,sym_ktree, assoc_ktree_l, ITree.cat, assoc_ktree_r, lift_ktree.
  intros [| []]; simpl;
    repeat (rewrite bind_bind; simpl) || (rewrite ret_bind_; simpl); reflexivity.
Qed.

Lemma local_rewrite2 {A B C: Type}:
  sym_ktree >=> assoc_ktree_r >=> id_ktree ⊗ sym_ktree ⩯
          @assoc_ktree_l E A B C >=> sym_ktree ⊗ id_ktree >=> assoc_ktree_r.
Proof.
  unfold id_ktree, tensor_ktree,sym_ktree, assoc_ktree_l, ITree.cat, assoc_ktree_r, lift_ktree.
  intros [| []]; simpl;
    repeat (rewrite bind_bind; simpl) || (rewrite ret_bind_; simpl); reflexivity.
Qed.

Lemma loop_tensor_ktree {I A B C D}
      (ab : ktree E A B) (cd : ktree E (I + C) (I + D)) :
  ab ⊗ loop cd ⩯
     loop (assoc_ktree_l >=> sym_ktree ⊗ id_ktree >=> assoc_ktree_r
                           >=> ab ⊗ cd
                           >=> assoc_ktree_l >=> sym_ktree ⊗ id_ktree >=> assoc_ktree_r).
Proof.
  rewrite tensor_swap, tensor_ktree_loop.
  rewrite <- compose_loop.
  rewrite <- loop_compose.
  rewrite (tensor_swap cd ab).
  repeat rewrite <- compose_ktree_assoc.
  rewrite local_rewrite1.
  do 2 rewrite compose_ktree_assoc.
  rewrite <- (compose_ktree_assoc sym_ktree assoc_ktree_r _).
  rewrite local_rewrite2.
  repeat rewrite <- compose_ktree_assoc.
  reflexivity.
Qed.

Lemma foo {A B C: Type}:
  forall (f: bks A C) (g: bks B C),
    denote_b (fun a => match a with
                      | inl x => f x
                      | inr x => g x
                      end) ⩯
             fun a => match a with
                   | inl x => denote_block (f x)
                   | inr x => denote_block (g x)
                   end.
Proof.
  intros.
  unfold denote_b; intros []; reflexivity.
Qed.  

Lemma bar {A B C: Type}:
  forall (f: bks A C) (g: bks B C) a,
    denote_block match a with
                   | inl x => f x
                   | inr x => g x
                   end ≈ 
     match a with
     | inl x => denote_block (f x)
     | inr x => denote_block (g x)
     end.
Proof.
  intros.
  destruct a; reflexivity.
Qed.

Lemma foo_assoc_l {A B C D D'} (f : ktree E _ D') :
    @id_ktree E A ⊗ @assoc_ktree_l E B C D >=> (assoc_ktree_l >=> f)
   ⩯ assoc_ktree_l >=> (assoc_ktree_l >=> (assoc_ktree_r ⊗ id_ktree >=> f)).
Proof.
  rewrite <- !compose_ktree_assoc.
  rewrite <- assoc_coherent_l.
  rewrite (compose_ktree_assoc _ _ (_ ⊗ id_ktree)).
  rewrite cat_tensor, id_ktree_left, assoc_lr, tensor_id.
  rewrite id_ktree_right.
  reflexivity.
Qed.

Lemma foo_assoc_r {A' A B C D} (f : ktree E A' _) :
    f >=> assoc_ktree_r >=> @id_ktree E A ⊗ @assoc_ktree_r E B C D
  ⩯ f >=> assoc_ktree_l ⊗ id_ktree >=> assoc_ktree_r >=> assoc_ktree_r.
Proof.
  rewrite (compose_ktree_assoc _ _ assoc_ktree_r).
  rewrite <- assoc_coherent_r.
  rewrite (compose_ktree_assoc (tensor_ktree _ _)).
  rewrite (compose_ktree_assoc _ (tensor_ktree _ _)).
  rewrite <- (compose_ktree_assoc (tensor_ktree _ _)).
  rewrite cat_tensor, id_ktree_left, assoc_lr, tensor_id.
  rewrite id_ktree_left.
  rewrite compose_ktree_assoc.
  reflexivity.
Qed.

Definition app_asm_correct {A B C D} (ab : asm A B) (cd : asm C D) :
  @eq_ktree E _ _
          (denote_asm (app_asm ab cd))
          (tensor_ktree (denote_asm ab) (denote_asm cd)).
Proof.
  unfold denote_asm.

  match goal with | |- ?x ⩯ _ => set (lhs := x) end.
  rewrite tensor_ktree_loop.
  rewrite loop_tensor_ktree.
  rewrite <- compose_loop.
  rewrite <- loop_compose.
  rewrite loop_loop.
  subst lhs.
  rewrite <- (loop_rename_internal' sym_ktree sym_ktree)
    by apply sym_nilpotent.
  apply eq_ktree_loop.
  rewrite ! compose_ktree_assoc.
  unfold tensor_ktree, sym_ktree, ITree.cat, assoc_ktree_l, assoc_ktree_r, id_ktree, lift_ktree.
  intros [[|]|[|]]; cbn.
  (* ... *)
  all: repeat (rewrite ret_bind; simpl).
  all: rewrite bind_bind.
  all: unfold _app_B, _app_D.
  all: rewrite fmap_block_map.
  all: unfold ITree.map.
  all: apply eutt_bind; try reflexivity.
  all: intros []; rewrite (itree_eta (ITree.bind _ _)); cbn; reflexivity.
Qed.

Definition relabel_bks_correct {A B C D} (f : A -> B) (g : C -> D)
           (bc : bks B C) :
  @eq_ktree E _ _
     (denote_b (relabel_bks f g bc))
     (lift_ktree f >=> denote_b bc >=> lift_ktree g).
Proof.
  rewrite lift_compose_ktree.
  rewrite compose_ktree_lift.
  intro a.
  unfold denote_b, relabel_bks.
  rewrite fmap_block_map.
  reflexivity.
Qed.

Definition relabel_asm_correct {A B C D} (f : A -> B) (g : C -> D)
           (bc : asm B C) :
  @eq_ktree E _ _
     (denote_asm (relabel_asm f g bc))
     (lift_ktree f >=> denote_asm bc >=> lift_ktree g).
Proof.
  unfold denote_asm.
  simpl.
  rewrite relabel_bks_correct.
  rewrite <- compose_loop.
  rewrite <- loop_compose.
  apply eq_ktree_loop.
  rewrite !tensor_id_lift.
  reflexivity.
Qed.

Definition link_asm_correct {I A B} (ab : asm (I + A) (I + B)) :
  @eq_ktree E _ _
     (denote_asm (link_asm ab))
     (loop (denote_asm ab)).
Proof.
  unfold denote_asm.
  rewrite loop_loop.
  apply eq_ktree_loop.
  simpl.
  rewrite relabel_bks_correct.
  reflexivity.
Qed.

End Correctness.
