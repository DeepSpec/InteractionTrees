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
     ITree OpenSum Fix.
Require Import Imp Den.

Section Correctness.

Context {E : Type -> Type}.
Context {HasLocals : Locals -< E}.
Context {HasMemory : Memory -< E}.

(** *** Internal structures *)

Lemma fmap_block_map:
  forall  {L L'} b (f: L -> L'),
    denote_block E (fmap_block f b) ≅ ITree.map (sum_bimap f id) (denote_block E b).
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
    + unfold ITree.map; rewrite ret_bind; reflexivity.
Qed.

Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
  fix traverse__ l: M unit :=
    match l with
    | [] => ret tt
    | a::l => (f a;; traverse__ l)%monad
    end.

Definition denote_list: list instr -> itree E unit :=
  traverse_ (denote_instr E).

Lemma after_correct :
  forall {label: Type} instrs (b: branch label),
    denote_block E (after instrs b) ≅ (denote_list instrs ;; denote_branch E b).
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
   denote_asm (raw_asm_block b) ⩰
          (fun _ => (denote_block _ b)).
Proof.
  unfold denote_asm.
  rewrite vanishing_den.
  rewrite elim_λ_den', elim_λ_den.
  unfold denote_b; simpl.
  intros [].
  rewrite fmap_block_map, map_map.
  unfold ITree.map.
  rewrite <- (bind_ret (denote_block E b)) at 2. 
  apply eutt_bind; [reflexivity | intros []; reflexivity].
Qed.

Lemma raw_asm_block_correct {A} (b : block A) :
  eutt eq (denote_asm (raw_asm_block b) tt)
          (denote_block _ b).
Proof.
  apply raw_asm_block_correct_lifted.
Qed.

(** *** [asm] combinators *)

Theorem pure_asm_correct {A B} (f : A -> B) :
  eq_den (denote_asm (pure_asm f))
         (@lift_den E _ _ f).
Proof.
  unfold denote_asm .
  rewrite vanishing_den.
  rewrite elim_λ_den', elim_λ_den.
  unfold denote_b; simpl.
  intros ?.
  rewrite map_ret.
  reflexivity.
Qed.

Definition id_asm_correct {A} :
  eq_den (denote_asm (pure_asm id)) (@id_den E A).
Proof.
  rewrite pure_asm_correct; reflexivity.
Defined.

Definition app_asm_correct {A B C D} (ab : asm A B) (cd : asm C D) :
  @eq_den E _ _
     (denote_asm (app_asm ab cd))
     (tensor_den (denote_asm ab) (denote_asm cd)).
Proof.
Admitted.

Definition relabel_asm_correct {A B C D} (f : A -> B) (g : C -> D)
           (bc : asm B C) :
  @eq_den E _ _
     (denote_asm (relabel_asm f g bc))
     (lift_den f >=> denote_asm bc >=> lift_den g).
Proof.
Admitted.

Definition link_asm_correct {I A B} (ab : asm (I + A) (I + B)) :
  @eq_den E _ _
     (denote_asm (link_asm ab))
     (loop_den (denote_asm ab)).
Proof.
Admitted.

End Correctness.
