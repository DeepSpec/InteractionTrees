From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.DelaySpecMonad
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac clear_ret_eutt_spin :=
  match goal with | H : ret ?a ≈ spin  |- _ => simpl in H; exfalso; eapply not_ret_eutt_spin; eauto
             | H : Ret ?a ≈ spin  |- _ => exfalso; eapply not_ret_eutt_spin; eauto
             | H : spin ≈ ret ?a  |- _ => exfalso; symmetry in H; eapply not_ret_eutt_spin; eauto
             | H : divergence (ret _ ) |- _ => pinversion H
  end.
  
Ltac invert_evidence :=
  intros; repeat match goal with 
                 | H : _ /\ _ |- _ => destruct H
                 | H : _ \/ _ |- _ => destruct H 
                 | H : exists a : ?A, _ |- _ => destruct H as [?a ?H]
                 | x : ?A + ?B |- _ => destruct x as [?a | ?b]
                 | H : upaco1 _ _ _ |- _ => pclearbot
                 end.

Ltac invert_ret := simpl in *; match goal with | H : Ret ?a ≈ Ret ?b |- _ => 
                                                 apply inv_ret in H; try discriminate; try (injection H as H);
                                                 subst end.


Ltac basic_solve := invert_evidence; try clear_ret_eutt_spin; try invert_ret.

Ltac dest_dep f a := destruct (f a) as [?fa ?Hfa] eqn : ?Heq; simpl in *.


Notation "a ∈ b" := (proj1_sig b a) (at level 70). 

Notation "a ∋ b" := (proj1_sig a b) (at level 70).

Section StateSpecT.
  Context (S : Type).
  Context (W : Type -> Type).
  Context {MonadW : Monad W}.
  Context {OrderW : OrderM W}.
  Context {OrderedMonadW : OrderedMonad W}.

  Definition StateSpecT (A : Type) := stateT S W A.
  
  Global Instance StateSpecTOrder : OrderM StateSpecT := 
    fun A (w1 w2 : stateT S W A) => forall (s : S), w1 s <≈ w2 s.

  Global Instance StateSpecTOrderedLaws : OrderedMonad StateSpecT.
  Proof.
    intros A B w1 w2 f1 f2 Hlw Hlf. unfold StateSpecT in *.
    red in OrderedMonadW. rename OrderedMonadW into HW. repeat red.
    intros. apply HW; auto. intros. destruct a as [s' a]. simpl.
    repeat red in Hlf. apply Hlf.
  Qed.
  
  (*Can I encode a pre post thing, state spec enriches the precondition and 
     specializes post condition*)

  (*maybe I need a computational monad M with a monad iter structure,
    I think the taus only showed up because I was using hte monad iter structure
    of strong bisimulation not weak,
    also note that this loop invar stuff, while relevant to D monads, is not
    itself of D monads 
   *)

End StateSpecT.

Section LoopInvarSpecific.
  Context (S : Type).

  Definition StateSpec (A : Type) := StateSpecT S DelaySpec A.

  Definition State (A : Type) := stateT S Delay A.

  Instance StateIter : MonadIter State := MonadIter_stateT0.
  
  Definition reassoc {A B : Type} (t : Delay (S * (A + B) ) ) : Delay ((S * A) + (S * B)  ) :=
    t >>= (fun '(s,ab) => 
             match ab with
             | inl a => ret (inl (s , a))
             | inr b => ret (inr (s , b))
             end
).

  Definition iso_arrow {A B : Type} (f : A -> State B) (g : (S * A) -> Delay (S * B) ) :=
    forall (a : A) (s : S), f a s ≈ g (s,a).

  Definition decurry_flip {A B C : Type} (f : A -> B -> C) : B * A -> C :=
    fun '(b,a) => f a b.

  (*this is just decurry*)
  Definition iso_destatify_arrow {A B : Type} (f : A -> State (A + B) ) : (S * A) -> Delay ((S * A) + (S * B)) :=
    fun '(s,a) => reassoc (f a s).


  
  (*should be able to use original*)
  Lemma loop_invar_state: forall (A B : Type) (g : A -> State (A + B)) (a : A) (s : S)
               (p : Delay ( S * B) -> Prop) (q : Delay ((S * A) + (S *B))  -> Prop  ) 
               (Hp : resp_eutt _ _ p) (Hq : resp_eutt _ _ q) ,
        (q (reassoc (g a s) )) -> 
        (q -+> p) -> (forall t, q t -> q (t >>= (iter_lift ( iso_destatify_arrow g)  ))) -> 
         (p \1/ divergence) (iter g a s) .
  Proof.
    intros. specialize (loop_invar (S * A) (S * B) ) as Hloop.
    set (iso_destatify_arrow g) as g'.
    enough ((p \1/ divergence) (KTree.iter g' (s,a) )).
    - assert (KTree.iter g' (s,a) ≅ iter g a s).
      + unfold g', iso_destatify_arrow.
        unfold iter, Iter_Kleisli, Basics.iter, MonadIterDelay, StateIter,
        MonadIter_stateT0, reassoc.
        admit. (*obviously the same but something annoying going on*)
      + assert (Hpdiv : resp_eutt _ _ (p \1/ divergence)).
        { intros t1 t2 Heutt. split; intros; basic_solve.
          - left. eapply Hp; eauto. symmetry. auto.
          - right. rewrite <- Heutt. auto.
          - left. eapply Hp; eauto.
          - right. rewrite Heutt. auto.
         }
        eapply Hpdiv; try apply H2. rewrite H3. reflexivity.
     - eapply Hloop; eauto.
  Admitted.

End LoopInvarSpecific.

Section LoopInvarGeneral.
  Context (S : Type).
  Context (M : Type -> Type).
  Context {MonadM : Monad M}.
  Context {EqMM : EqM M}.
  Context {MonadLawsM : MonadLaws M}.
  Context {IterM : MonadIter M}.

  Context (divergence : forall {A : Type}, M A -> Prop).

  Definition loop_invar_imp {A B : Type} (q : M (A + B) -> Prop ) (p : M B -> Prop) :Prop :=
    forall m, q (m >>= fun b => ret (inr b) ) -> p m. 

  Definition iter_lift {A B : Type} (g : A -> M (A + B)) : (A + B) -> M (A + B) :=
    fun x => match x with 
             | inl a => g a
             | inr b => ret (inr b) end.

  Notation "q -+> p" := (loop_invar_imp q p) (at level 80).

  Definition resp_eq {A : Type} (p : M A -> Prop) : Prop :=
    forall m1 m2, m1 ≈ m2 -> (p m1) <-> (p m2).
(*
  Definition loop_invar_prop : Prop :=   forall (A B : Type) (g : A -> M (A + B) ) (a : A) 
                          (p : M B -> Prop) (Hp : resp_eq p)
                          (q : M (A + B) -> Prop ) (Hq : resp_eq q ),
    (q -+> p) -> (q (g a)) -> 
    (forall t, q t ->  q (bind t (iter_lift g))) ->
    p \1/ divergence) (iter g a).

  Context (divergence : forall (A : Type), M A -> Prop ).
  (* Context (under_loop_invar : forall (A B : Type) (g : A -> M (A + B) ) (a : A), ) *)
  (*might need a proof that if that whole inl wf thing happens then it 
    is some infinite element, or have some kind of underlying loop invariant principle*)
  (*divergent elements follow two laws bind spin f eq spin, 
    if
   *)
  (*complication, delay monad is simple in some sense, every element is either spin,
    or it is ret some value*)
  (*notions of divergence always makes sense in the base monad*)


  *)

  

End LoopInvarGeneral.

