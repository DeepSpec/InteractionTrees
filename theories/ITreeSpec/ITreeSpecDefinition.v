From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
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
     Dijkstra.ITrace
     Dijkstra.ITraceBind
     Dijkstra.EuttEv
     Dijkstra.EuttDiv
     Dijkstra.ITracePreds
     Dijkstra.ITraceBindTrigger
     Dijkstra.TracesIT
     Dijkstra.StateSpecT
     Dijkstra.StateIOTrace
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant SpecEv (E : Type -> Type) : Type -> Type :=
  | Spec_Vis {A : Type} (e : EvAns E A) : SpecEv E A
  | Spec_forall { A : Type} : SpecEv E A
  | Spec_exists {A : Type} : SpecEv E A
.
Arguments Spec_forall {E} {A}.
Arguments Spec_exists {E} {A}.
Arguments Spec_Vis {E} {A}.


Definition itree_spec E R := itree (SpecEv E) R.
Definition itree_spec' E R := itree' (SpecEv E ) R.

Global Instance itree_spec_monad {E} : Monad (itree_spec E) := Monad_itree.
(* move this to main itrace definitions *)
Global Instance itrace_monad {E} : Monad (itrace E) := Monad_itree.


Inductive satisfiesF {E R} (F : itree_spec E R -> itrace E R -> Prop) : 
  itree_spec' E R -> itrace' E R -> Prop :=
  | satisfies_Ret (r : R) : satisfiesF F (RetF r) (RetF r)
  | satisfies_TauLR (phi : itree_spec E R) (tr : itrace E R) :
      F phi tr -> satisfiesF F (TauF phi) (TauF tr)
  | satisfies_TauL phi otr :
      satisfiesF F (observe phi) otr -> satisfiesF F (TauF phi) otr
  | satisfies_TauR ophi tr :
      satisfiesF F ophi (observe tr) -> satisfiesF F ophi (TauF tr)
  | satisfies_Spec_Vis A (e : EvAns E A) kphi ktr :
      (forall a : A, F (kphi a) (ktr a) ) -> satisfiesF F (VisF (Spec_Vis e ) kphi) (VisF e ktr)
  | satisfies_forall A kphi tr :
      (forall a : A, F (kphi a) tr) -> satisfiesF F (VisF Spec_forall kphi) (observe tr)
  | satisfies_exists A kphi tr :
      (exists a : A, F (kphi a) tr) -> satisfiesF  F (VisF Spec_exists kphi) (observe tr)
.

Hint Constructors satisfiesF.
Definition satisfies_ {E R} (F : itree_spec E R -> itrace E R -> Prop) (phi : itree_spec E R) (tr : itrace E R) := 
  satisfiesF F (observe phi) (observe tr).
Hint Unfold satisfies_.

Lemma monot_satisfies {E R} : monotone2 (@satisfies_ E R).
Proof.
  red. intros. red. red in IN. induction IN; eauto.
  destruct H as [a Ha]. eauto.
Qed.
Hint Resolve monot_satisfies : paco.

Definition satisfies {E R} (phi : itree_spec E R) (tr : itrace E R): Prop :=
  paco2 satisfies_ bot2 phi tr.

Lemma eqitC_euttEv_wcompat_satisfies {E R} (b1 b2 : bool) :
  wcompatible2 (@satisfies_ E R) (eqitC_euttEv eq b1 b2).
Proof.
  constructor.
  { red. intros. eapply eqitC_euttEv_mon; eauto. }
  intros.
  dependent destruction PR. punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r0) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto; (try constructor; eauto).
    remember (RetF r0) as x. hinduction EQVr before r; intros; subst; try inv Heqx; eauto.
    eapply LERR1 in REL0; eauto. eapply LERR2 in REL; eauto. subst. constructor.
  - red. remember (TauF phi) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ( try (constructor; eauto; fail )).
    remember (TauF tr) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - remember (TauF phi) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (TauF tr) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (VisF (Spec_Vis e) kphi ) as x. red.
    hinduction EQVl before r; intros; subst; try dependent destruction Heqx; try inv CHECK; try (constructor; eauto; fail).
    remember (VisF e0 ktr) as y. 

    hinduction EQVr before r; intros; subst; try dependent destruction Heqy; try inv CHECK; eauto.
    constructor. intros. pclearbot. gclo. econstructor; eauto.
    gfinal. eauto.
  - remember (VisF Spec_forall kphi) as x. red.
    hinduction EQVl before r; intros; subst; try dependent destruction Heqx; eauto.
    constructor. intros. pclearbot. specialize (REL a). gclo.
    econstructor; eauto. gfinal. eauto.
  - remember (VisF Spec_exists kphi) as x. red. destruct H as [a CIH].
    hinduction EQVl before r; intros; subst; try dependent destruction Heqx; eauto.
    constructor. exists a. gclo. specialize (REL a). pclearbot. econstructor; eauto.
    gfinal. eauto.
Qed.

Hint Resolve (eqitC_euttEv_wcompat_satisfies true true) : paco.

Global Instance gsatisfies_cong_eqit {E R r rg} :
  Proper (@eq_itree (SpecEv E) R R eq ==> eq_itree eq ==> flip impl)
         (gpaco2 satisfies_ (eqitC_euttEv eq true true) r rg  ).
Proof.
  repeat intro. gclo. econstructor; eauto. 
  - eapply eqit_mon; try eapply H; eauto.
  - eapply eqit_mon; try eapply H0; eauto.
  - intros; subst; auto.
  - intros; subst; auto.
Qed.

Global Instance gsatisfies_cong_euttge {E R r rg} :
  Proper (@euttge (SpecEv E) R R eq ==> euttge eq ==> flip impl)
         (gpaco2 satisfies_ (eqitC_euttEv eq true true) r rg  ).
Proof.
  repeat intro. gclo. econstructor; eauto; intros; subst; auto.
Qed.

(* Print wcompatible2 *)
(* May have something to do with that closure thing *)
(* It is in the itrees library, *)

Notation "tr ⊧ phi" := (satisfies phi tr ) (at level 5).

Definition refines {E R} (phi psi : itree_spec E R) : Prop :=
  forall tr, tr ⊧ phi -> tr ⊧ psi.


Definition and_spec {E R} (phi psi : itree_spec E R) :=
  Vis Spec_forall (fun b : bool => if b then phi else psi).

Definition or_spec {E R} (phi psi : itree_spec E R) :=
  Vis Spec_exists (fun b : bool => if b then phi else psi).

Definition empty_cont {A : Type} (v : void) : A :=
  match v with end.

Definition top {E R} : itree_spec E R :=
  Vis Spec_forall empty_cont.

Definition bot E R : itree_spec E R :=
  Vis Spec_exists empty_cont.

Definition forall_non_empty A {E R} (kphi : A -> itree_spec E R) : itree_spec E R :=
  and_spec (Vis Spec_forall kphi) (Vis Spec_exists (fun _ : A => top) ).

Definition show_empty {E} (A : Type) : itree_spec E (A -> void) :=
  Vis Spec_exists (fun H => Ret H).
