From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     CategoryOps
     CategoryTheory
     CategoryFunctor
     CategoryMonad
     CategoryNaturalTransformation
.

Import CatNotations.
Local Open Scope cat_scope.

Section MonadTransformer.

  Context {obj: Type}
          {C: obj-> obj-> Type}
          `{Category_C: Category obj C}
          {M : obj -> obj} {N : obj -> obj}
  .

  (** *Monad Transformer Definition *)
  (* A monad transformer is a natural transformation on two monads. *)
  Context {M_Monad : Monad C M} {N_Monad : Monad C N}
          {M_ML : MonadLaws M_Monad} {N_ML : MonadLaws N_Monad}.

  Definition m_fmap := fun (a b : obj) X => bind (a := a) (b := b) (M := M) (X >>> ret (M := M)).
  Definition n_fmap := fun (a b : obj) X => bind (a := a) (b := b) (M := N) (X >>> ret (M := N)).

  (* "lift" should be equivalent to the [eta] in a natural transformation. *)
  Context {lift : forall a, C (M a) (N a)}.
  Context {MonadTransformer: NaturalTransformation C C _ _ M N lift m_fmap n_fmap}.

  Context `{forall (a b : obj), PER (@eq2 obj C _ a b)}.

  (** *Monad Transformer Laws
   * Assuming that a monad transformer is a natural transformation, prove the monad transformer laws
   * (i.e. the lift_ret and lift_bind laws, as annotated on the respective theorems.) *)

  Ltac cat_reflexivity :=
    rewrite <- cat_id_l at 1; apply cat_id_l.

  (* lift . return = lift *)
  Theorem lift_ret_law :
    forall A, ret (M := M) >>> lift A ⩯ ret (M := N).
  Proof.
    intros A.

    (* ====== Assertions about naturality squares. ====== *)

    (* Return is a natural transformation from the Identity functor in a category
     * to the functor specified by the monad. *)
    assert (ret_naturality_m :
              forall (a b : obj) (f : C a b), ret >>> m_fmap a b f ⩯ f >>> ret). {
      intros. unfold m_fmap. rewrite bind_ret_l. cat_reflexivity.
    }
    assert (ret_naturality_n :
              forall (a b : obj) (f : C a b), ret >>> n_fmap a b f ⩯ f >>> ret). {
      intros. unfold n_fmap. rewrite bind_ret_l. cat_reflexivity.
    }

    (* A monad transformer is a natural transformation over two monads. *)
    pose proof naturality as transformer_naturality.

    unfold n_fmap, m_fmap in *. specialize (ret_naturality_n (M A) (N A) (lift A)).

    (* IY: This assertion should hold for the naturality diagrams, but I'm not
     * sure how to prove it in Coq. *)
    assert (H_diag : forall (a b : obj) (f : C a b), ret >>> n_fmap a b f ⩯ ret >>> lift a >>> n_fmap a b f). {
      intros.
    }
    admit.

    (* Using the above assertion, we can prove the rest of this theorem. *)
    specialize (H_diag A A (id_ A)).
    specialize (ret_naturality_n A A (id_ A)). rewrite ret_naturality_n in H_diag.
    rewrite cat_id_l in H_diag. symmetry. rewrite H_diag.
    rewrite category_cat_assoc.  apply category_proper_cat. cat_reflexivity.
    unfold n_fmap.
    2 : apply Category_C.
    epose proof cat_id_r.

    (* Here, we can't use [rewrite <- cat_id_r] immediately. *)
    assert (lift A >>> bind (id_ A >>> ret) ⩯ lift A >>> id_ (N A)). {
      apply category_proper_cat. cat_reflexivity. rewrite cat_id_l. rewrite bind_ret_r. cat_reflexivity.
    }
    rewrite cat_id_r in H1. apply H1.
  Admitted.

  Class MonadTransformerLaws : Prop :=
    {
      (* lift . return = lift *)
      lift_ret A : ret (M := M) >>> lift A ⩯ ret (M := N);

      (* (* lift (m `bind` k) = (lift m) `bind` (lift n) *) *)
      (* lift_bind {A} : bind >>> lift ⩯ lift *)
    }.

  Instance MonadTransformerLaw_Instance : MonadTransformerLaws.
  Proof.
    constructor.
    (* lift_ret law. *)
    - intros A. destruct MT.
      destruct NTL.
      epose proof (Monad_FunctorLaws _ _ M_ML) as M_Functor.
      epose proof (Monad_FunctorLaws _ _ N_ML) as N_Functor.
      specialize (naturality A A (id_ A)).
      destruct M_Functor. specialize (fmap_id A).
      Set Printing Implicit. 
      apply setoid_rewrite fmap_id in naturality.
      rewrite fmap_id in naturality. 
      unfold fmap, Monad_Functor in *.
      
      unfold lift.
      (* Can't change naturality.. *)
      Fail specialize (naturality A A (id_ A)).

      edestruct F_FUN, G_FUN.
   Admitted.

  (* TODO Give StateT Instance of MonadTransformer. *)
End MonadTransformer.
