From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     ITree
     FixFacts
     Basics_Functions.

Require Import Program.Basics. (* ∘ *)

Require Import Den.

Section Linking.

  Variable E : Type -> Type.

  Definition link_seq_den {A B C}
             (ab: @den E A B)
             (bc: den B C): den A C :=
    loop_den (sym_den >=> ab ⊗ bc).

  Theorem seq_correct {A B C} (ab : den A B) (bc : den B C) :
     (link_seq_den ab bc) ⩰ ab >=> bc.
  Proof.
    unfold link_seq_den.
    rewrite tensor_den_slide.
    rewrite <- compose_den_assoc.
    rewrite loop_compose.
    rewrite tensor_swap.
    repeat rewrite <- compose_den_assoc.
    rewrite sym_nilpotent, id_den_left.
    rewrite compose_loop.
    erewrite yanking_den.
    rewrite id_den_right.
    reflexivity.
  Qed.

End Linking.
