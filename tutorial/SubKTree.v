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

Import CatNotations.
Local Open Scope cat_scope.
(* We consider the transport of the symmetric traced monoidal structure of [ktree]s to a subcategory *)

Section SubK.

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
  Context {iI_voi_iso: Iso Fun iI_void void_iI}.
 
  Context {isum_sum: forall {A B: i}, F (isum A B) -> (F A) + (F B)}.
  Context {sum_isum: forall {A B: i}, (F A) + (F B) -> F (isum A B)}.
  Context {isum_sum_iso: forall A B, Iso Fun (@isum_sum A B) (@sum_isum A B)}.
  Arguments isum_sum {A B}.
  Arguments sum_isum {A B}.

  Definition iI_voidl {E} := @lift_ktree E _ _ iI_void.
  Definition void_iIl {E} := @lift_ktree E _ _ void_iI.

  Definition isum_suml {E A B} := @lift_ktree E _ _ (@isum_sum A B).
  Definition sum_isuml {E A B} := @lift_ktree E _ _ (@sum_isum A B).
  
  Definition sktree (E: Type -> Type) (A B: i) := F A -> itree E (F B).

  (** ** Categorical operations *)

  Section Operations.

    Context {E : Type -> Type}.

    Let sktree := sktree E.

    (* Utility function to lift a pure computation into ktree *)
    Definition lift_sktree {A B: i} (f : F A -> F B) : sktree A B := lift_ktree f. 

    (** *** Category *)

    Definition eutt_sktree {A B} (d1 d2 : sktree A B) := @eq2 _ (ktree E) _ _ _ d1 d2.

    Global Instance Eq2_sktree : Eq2 sktree := @eutt_sktree.

    (** Composition is [ITree.cat], denoted as [>>>]. *)
    Global Instance Cat_sktree : Cat sktree :=
      fun (A B C: i) (k: ktree E (F A) (F B)) (k': ktree E (F B) (F C)) => cat k k': ktree E _ _.

    (** Identity morphism *)
    Global Instance Id_sktree : Id_ sktree :=

      fun A => id_ (F A). 

    (** *** Symmetric monoidal category *)

    (** Initial object, monoidal unit *)

    Global Instance Initial_iI_sktree : Initial sktree iI :=
      fun A => iI_voidl >>> empty.

    (** The tensor product is given by the coproduct *)
    Global Instance Case_sktree : @CoprodCase i sktree isum :=
      fun (a b c: i) (ska: ktree _ _ _) skb => isum_suml >>> case_ ska skb.

    Global Instance Inl_sktree : CoprodInl sktree isum :=
      fun _ _ => inl_ >>> sum_isuml.

    Global Instance Inr_sktree : CoprodInr sktree isum :=
      fun _ _ => inr_ >>> sum_isuml.

    (** Traced monoidal category *)
    Definition sloop {A B C : i}
               (body : sktree (isum C A) (isum C B)) :
      sktree A B :=
      loop (sum_isuml >>> body >>> isum_suml). 

  End Operations.

End SubK.