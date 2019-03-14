(** * Composition of [asm] programs *)

Require Import Asm.
Require Import Utils_tutorial.
From Coq Require Import
     List
     Strings.String
     Program.Basics
     ZArith.
Import ListNotations.

From ITree Require Import
     Basics.Basics
     Basics.Function
     Basics.Category.

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
  {| internal := void;
     code := fun a' =>
               match a' with
               | inl v => match v : void with end
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
  {| code := relabel_bks (bimap id f) (bimap id g) bc.(code);
  |}.

(** Link labels from two programs together. *)
Definition link_asm {I A B} (ab : asm (I + A) (I + B)) : asm A B :=
  {| internal := ab.(internal) + I;
     code := relabel_bks assoc_r assoc_l ab.(code);
  |}.

(** ** Correctness *)
(** The combinators above map to their denotational counterparts. *)

(* TODO: don't import stuff in the middle of modules *)
From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.
From ITree Require Import
     ITree KTree KTreeFacts.
Import ITreeNotations.
Import CatNotations.
Local Open Scope cat.

Require Import Imp. (* TODO: remove this *)

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
    eapply eq_itree_eq_bind; try reflexivity.
    intros []; apply IHb.
  - simpl.
    destruct br; simpl.
    + unfold ITree.map; rewrite ret_bind; reflexivity.
    + unfold ITree.map; rewrite bind_bind. 
      eapply eq_itree_eq_bind; try reflexivity.
      intros ?.
      flatten_goal; rewrite ret_bind; reflexivity.
    + rewrite (itree_eta (ITree.map _ _)).
      cbn. apply eq_itree_Vis. intros [].
Qed.

(* TODO: send to ext-lib *)
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
    eapply eq_itree_eq_bind; try reflexivity.
    intros []; apply IH.
Qed.

Lemma denote_list_app:
  forall is1 is2,
    @denote_list (is1 ++ is2) ≅
                 (@denote_list is1;; denote_list is2).
Proof.
  intros is1 is2; induction is1 as [| i is1 IH]; simpl; intros; [rewrite ret_bind; reflexivity |].
  rewrite bind_bind; setoid_rewrite IH; reflexivity.
Qed.

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
  rewrite case_l_ktree', case_l_ktree.
  unfold denote_b; simpl.
  intros ?.
  rewrite map_ret.
  reflexivity.
Qed.

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
  f ⩯ g -> h >=> f ⩯ h >=> g.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Lemma cat_eq2_r {a b c : Type} (h : ktree E b c) (f g : ktree E a b) :
  f ⩯ g -> f >=> h ⩯ g >=> h.
Proof.
  intros H; rewrite H; reflexivity.
Qed.

Lemma local_rewrite1 {a b c : Type}:
    bimap (id_ a) (@swap _ (ktree E) _ _ b c) >=> assoc_l >=> swap
  ⩯ assoc_l >=> bimap swap (id_ c) >=> assoc_r.
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
    swap >=> assoc_r >=> bimap (id_ _) swap
  ⩯ @assoc_l _ (ktree E) _ _ a b c >=> bimap swap (id_ _) >=> assoc_r.
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
  ⩯ loop (assoc_l >=> bimap swap (id_ _)
                  >=> assoc_r
                  >=> bimap ab cd
                  >=> assoc_l >=> bimap swap (id_ _) >=> assoc_r).
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
    bimap (id_ A) (@assoc_l _ _ _ _ B C D) >=> (assoc_l >=> f)
   ⩯ assoc_l >=> (assoc_l >=> (bimap assoc_r (id_ _) >=> f)).
Proof.
  rewrite <- !cat_assoc.
  rewrite <- assoc_l_assoc_l.
  rewrite (cat_assoc _ _ _ (bimap _ (id_ _))).
  rewrite bimap_cat, cat_id_l, assoc_l_mono, bimap_id, cat_id_r.
  reflexivity.
  all: typeclasses eauto.
Qed.

Lemma foo_assoc_r {A' A B C D} (f : ktree E A' _) :
    f >=> assoc_r >=> bimap (id_ A) (@assoc_r _ _ _ _ B C D)
  ⩯ f >=> bimap assoc_l (id_ _) >=> assoc_r >=> assoc_r.
Proof.
  rewrite (cat_assoc _ _ _ assoc_r).
  rewrite <- assoc_r_assoc_r.
  rewrite (cat_assoc _ (bimap _ _)), (cat_assoc _ _ (bimap _ _)).
  rewrite <- (cat_assoc _ (bimap _ _)).
  rewrite bimap_cat, cat_id_l, assoc_l_mono, bimap_id, cat_id_l.
  rewrite cat_assoc.
  reflexivity.
  all: typeclasses eauto.
Qed.

Definition app_asm_correct {A B C D} (ab : asm A B) (cd : asm C D) :
     denote_asm (app_asm ab cd)
  ⩯ bimap (denote_asm ab) (denote_asm cd).
Proof.
  unfold denote_asm.

  match goal with | |- ?x ⩯ _ => set (lhs := x) end.
  rewrite bimap_ktree_loop.
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
  intro x. rewrite ret_bind; simpl.
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

Definition relabel_bks_correct {A B C D} (f : A -> B) (g : C -> D)
           (bc : bks B C) :
    denote_b (relabel_bks f g bc)
  ⩯ lift_ktree f >=> denote_b bc >=> lift_ktree g.
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
    denote_asm (relabel_asm f g bc)
  ⩯ lift_ktree f >=> denote_asm bc >=> lift_ktree g.
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

Definition link_asm_correct {I A B} (ab : asm (I + A) (I + B)) :
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
