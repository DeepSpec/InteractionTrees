From ITree Require Import
     Basics.Basics
     Basics.Function
     Basics.FunctionFacts
     Basics.Category
     ITree
     KTree
     KTreeFacts
     Eq.UpToTausEquivalence.
From Coq Require Import
     Morphisms.

Require Import SubKTree.

Section Facts.

  (* We consider a subdomain of Type given by a Type [i] and its injection into Type [F] *)
  Context {i: Type}.
  Context {F: i -> Type}.

  (* We assume that we have an initial element and a bifunctor over i *)
  Context {iI: i}.
  Context {isum: i -> i -> i}.

  Definition iFun (A B: i) := F A -> F B.

  (* The unit and the bifunctor must be faithfully transported into [Type] by F *)
  Context {iI_void: F iI -> void}.
  Context {void_iI: void -> F iI}.
  Context {iI_void_iso: Iso Fun iI_void void_iI}.

  Context {isum_sum: forall {A B: i}, F (isum A B) -> (F A) + (F B)}.
  Context {sum_isum: forall {A B: i}, (F A) + (F B) -> F (isum A B)}.
  Arguments isum_sum {A B}.
  Arguments sum_isum {A B}.

  Context {isum_sum_iso: forall A B, Iso Fun (@isum_sum A B) (@sum_isum A B)}.

  Context {E: Type -> Type}.

  Notation sktree := (@sktree i F E).

  Global Instance CatAssoc_sktree : CatAssoc sktree.
  Proof.
    intros A B C D f g h a.
    unfold cat, Cat_sktree.
    (* Can we make [cat_assoc] work here despite the specialization of the equation? *)
    rewrite CatAssoc_ktree.
    reflexivity.
  Qed.

  (** *** [id_sktree] respect identity laws *)
  Global Instance CatIdL_sktree : CatIdL sktree.
  Proof.
    intros A B f a; unfold cat, Cat_sktree.
    (* We cannot derive this result from the same over ktree, or so it semes.
         Indeed, the identity is obviously not the same, it does not even have the same type.
         Of course, we can always redo the proof...
     *)
    unfold cat, Cat_ktree, ITree.cat, id_, Id_sktree.
    rewrite bind_ret; reflexivity.
  Qed.

  Global Instance CatIdR_sktree : CatIdR sktree.
  Proof.
    intros A B f a; unfold cat, Cat_sktree, cat, Cat_ktree, ITree.cat, id_, Id_sktree.
    rewrite <- (bind_ret2 (f a)) at 2.
    reflexivity.
  Qed.

  Global Instance Category_sktree : Category sktree.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  (*
  Global Instance InitialObject_sktree : @InitialObject _ sktree _ iI (@Initial_iI_sktree _ _ _ iI_void E).
  Proof.
    intros A f.
    intros ?.
    
    Qed.
   *)

End Facts.