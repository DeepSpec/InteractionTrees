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
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
     Dijkstra.IBranch
     Dijkstra.IBranchBind
     Dijkstra.EuttDiv
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant branch_forallF {E : Type -> Type} {R : Type} (F : ibranch E R -> Prop) 
        (PE : forall A, EvAns E A -> Prop) (PR : R -> Prop) : ibranch' E R -> Prop :=
| branch_forall_ret (r : R) : PR r -> branch_forallF F PE PR (RetF r)
| branch_forall_tau (b : ibranch E R) : F b -> branch_forallF F PE PR (TauF b)
| branch_forall_vis {A : Type} (e : EvAns E A) (k : A -> ibranch E R) :
    PE A e -> (forall (a :A), F (k a) ) -> branch_forallF F PE PR (VisF e k)
.

Hint Constructors branch_forallF.

Definition branch_forall_ {E R} PE PR F (b : ibranch E R) :=
  branch_forallF F PE PR (observe b).

Lemma branch_forall_monot {E R} PE PR : monotone1 (@branch_forall_ E R PE PR).
Proof.
  repeat intro. red in IN. red. induction IN; auto.
Qed.

Hint Resolve branch_forall_monot : paco.

Definition branch_forall {E R} PE PR := paco1 (@branch_forall_ E R PE PR) bot1.

Lemma branch_forall_proper_aux: forall (E : Type -> Type) (R : Type) (PE : forall A : Type, EvAns E A -> Prop)
                                  (PR : R -> Prop) (b1 b2 : itree (EvAns E) R),
    (b1 ≈ b2)%itree -> branch_forall PE PR b1 -> branch_forall PE PR b2.
Proof.
  intros E R PE PR. pcofix CIH. intros b1 b2 Heutt Hforall.
  pfold. red. punfold Hforall. red in Hforall.
  punfold Heutt. red in Heutt. induction Heutt; subst; auto.
  - inv Hforall. auto.
  - inv Hforall. pclearbot. constructor. right. eapply CIH; eauto.
  - inv Hforall. inj_existT. subst. pclearbot.
    constructor; auto. intros. right. eapply CIH; eauto. apply H3.
  - apply IHHeutt. inv Hforall. pclearbot. punfold H0.
  - constructor. left. pfold. red. apply IHHeutt. auto.
Qed.

Global Instance branch_forall_proper_eutt {E R PE PR} : Proper (eutt eq ==> iff) (@branch_forall E R PE PR).
Proof.
  intros b1 b2 Heutt. split; intros.
  - eapply branch_forall_proper_aux; eauto.
  - symmetry in Heutt. eapply branch_forall_proper_aux; eauto.
Qed.
    
      

Lemma forall_spin : forall E R PE PR, branch_forall PE PR (@ITree.spin (EvAns E) R).
Proof.
  intros. pcofix CIH. pfold. red. cbn. constructor.
  right. auto.
Qed.

Inductive branch_inf_oftenF {E : Type -> Type} {R : Type} (PE : forall A, EvAns E A -> Prop)
        (F : ibranch E R -> Prop) : ibranch' E R -> Prop :=
| branch_inf_often_tau (b : ibranch E R) : branch_inf_oftenF PE F (observe b) -> 
                                             branch_inf_oftenF PE F (TauF b)
| branch_inf_often_vis_neg (e : EvAns E unit) (k : unit -> ibranch E R) : 
    branch_inf_oftenF PE F (observe (k tt)) -> branch_inf_oftenF PE F (VisF e k)
| branch_inf_often_vis_pos (e : EvAns E unit) (k : unit -> ibranch E R) : 
    F (k tt) -> PE unit e -> branch_inf_oftenF PE F (VisF e k)
.

Hint Constructors branch_inf_oftenF.

Definition branch_inf_often_ {E R} PE F (b : ibranch E R) :=
  branch_inf_oftenF PE F (observe b).

Lemma branch_inf_often_monot {E R} PE : monotone1 (@branch_inf_often_ E R PE).
Proof.
  repeat intro. red in IN. red. induction IN; auto.
Qed.

Hint Resolve branch_inf_often_monot : paco.

Definition branch_inf_often {E R} PE := paco1 (@branch_inf_often_ E R PE) bot1.

Inductive front_and_last {E : Type -> Type} {R : Type} (PEF : forall A, EvAns E A -> Prop)
          (PEL : forall A, EvAns E A -> Prop) (PR : R -> Prop) : ibranch E R -> Prop :=
| front_and_last_base (e : EvAns E unit) (r : R) (b : itree (EvAns E) R) :
    b ≈ Vis e (fun u => Ret r) -> PEL unit e -> PR r -> front_and_last PEF PEL PR b
  | front_and_last_cons (e : EvAns E unit) (k : unit -> ibranch E R) (b : itree (EvAns E) R ) :
      b ≈ Vis e k -> PEF unit e -> front_and_last PEF PEL PR (k tt) -> front_and_last PEF PEL PR b
      
.

Lemma fal_proper_aux: forall (E : Type -> Type) (R : Type) (PEF PEL : forall A : Type, EvAns E A -> Prop)
                        (PR : R -> Prop) (b1 b2 : itree (EvAns E) R),
    (b1 ≈ b2)%itree -> front_and_last PEF PEL PR b1 -> front_and_last PEF PEL PR b2.
Proof.
  intros E R PEF PEL PR b1 b2 Heutt Hfal.
  generalize dependent b2. induction Hfal; intros.
  - eapply front_and_last_base; eauto.
    rewrite <- Heutt. auto.
  - eapply front_and_last_cons; eauto. rewrite <- Heutt. auto.
Qed.

Global Instance front_and_last_proper_eutt {E R PEF PEL PR} : Proper (eutt eq ==> iff) (@front_and_last E R PEF PEL PR).
Proof.
  intros b1 b2 Heutt. split; intros.
  - eapply fal_proper_aux; eauto.
  - symmetry in Heutt. eapply fal_proper_aux; eauto.
Qed.
     
