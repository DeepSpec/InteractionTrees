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
     Events.Exception
     Events.ExceptionFacts
     Core.Divergence
     Dijkstra.TracesIT
     Dijkstra.ITrace
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.StrongBisimProper
     Secure.SecurityImpExc.SecurityImpHandler (* for use_simpobs*)
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.

Lemma secure_eqit_try_catch : forall Err E R1 R2 (RR : R1 -> R2 -> Prop)
                           b1 b2 Label priv l
    (t1 : itree (exceptE Err +' E)  R1) (t2 : itree (exceptE Err +' E) R2) kcatch1 kcatch2,
    eqit_secure Label priv RR b1 b2 l t1 t2 ->
    (forall e : Err, eqit_secure Label priv RR b1 b2 l (kcatch1 e) (kcatch2 e) ) ->
    eqit_secure Label priv RR b1 b2 l (try_catch t1 kcatch1) (try_catch t2 kcatch2).
Proof. 
  intros Err E R1 R2 RR b1 b2 Label priv l.
  pcofix CIH. intros t1 t2 kcatch1 kcatch2 Ht12 Hkcatch12.
  punfold Ht12. red in Ht12. genobs t1 ot1. genobs t2 ot2. 
  hinduction Ht12 before r; intros; use_simpobs.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite try_catch_ret.
    pfold. constructor; auto.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite try_catch_tau.
    pfold. constructor. right. eapply CIH; eauto.
  - rewrite Heqot1. rewrite try_catch_tau. pfold. constructor; auto.
    pstep_reverse.
  - rewrite Heqot2. rewrite try_catch_tau. pfold. constructor; auto.
    pstep_reverse.
  - pclearbot. destruct e.
    + rewrite Heqot1. rewrite Heqot2. destruct e. repeat rewrite try_catch_exc.
      eapply paco2_mon; try apply Hkcatch12. intros; contradiction.
    + rewrite Heqot1. rewrite Heqot2. repeat rewrite try_catch_ev. pfold.
      constructor; auto. left. pfold. constructor. right.
      eapply CIH; eauto. apply H.
  - (* so this lemma is not actually true because  private halts are 
       indistinguishable from spin but try catch will act differently on them
     *)
