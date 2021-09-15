From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

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
     Secure.SecureEqHalt
     Secure.SecurityImpExc.SecurityImp
     Secure.SecurityImpExc.SecurityImpHandlerExcState
     Secure.SecureEqProgInsensEv
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.


Lemma interp_imp_try_catch R (ttry : itree _ R) kcatch σ:
  interp_imp (try_catch ttry kcatch) σ ≈ 
             try_catch (interp_imp ttry σ) (fun '(l, σ') => interp_imp (kcatch l) σ' ).
Proof.
  generalize dependent ttry. generalize dependent σ.
  ginit. gcofix CIH. intros. 
  destruct (observe ttry) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - setoid_rewrite Heq. setoid_rewrite try_catch_ret.
    setoid_rewrite interp_state_ret. rewrite try_catch_ret.
    gstep. constructor. auto.
  - setoid_rewrite Heq.
    rewrite try_catch_tau. setoid_rewrite interp_state_tau. rewrite try_catch_tau.
    gstep. constructor. gfinal. left. eapply CIH.
  - destruct e as [ ?  | [? | ? ] ].
    + rewrite Heq. destruct e. rewrite try_catch_exc.
      setoid_rewrite interp_state_vis. cbn.
      repeat rewrite bind_trigger. rewrite bind_vis.
      rewrite try_catch_exc. gfinal. right.
      eapply paco2_mon with (r := bot2); intros; try contradiction.
      enough (interp_imp (kcatch s) σ ≈ interp_imp (kcatch s) σ); auto.
      reflexivity.
    + rewrite Heq. destruct s.
      * setoid_rewrite try_catch_ev. setoid_rewrite interp_state_vis.
        cbn. setoid_rewrite bind_ret_l. rewrite try_catch_tau.
        setoid_rewrite interp_state_tau. rewrite tau_euttge.
        gstep. constructor. gfinal. left. eapply CIH.
      * setoid_rewrite try_catch_ev. setoid_rewrite interp_state_vis.
        cbn. setoid_rewrite bind_ret_l. rewrite try_catch_tau.
        setoid_rewrite interp_state_tau. rewrite tau_euttge.
        gstep. constructor. gfinal. left. eapply CIH.
   + rewrite Heq. setoid_rewrite try_catch_ev. setoid_rewrite interp_state_vis.
     cbn. repeat rewrite bind_trigger. repeat rewrite bind_vis. 
     setoid_rewrite try_catch_ev. gstep. constructor.
     intros. red. setoid_rewrite bind_ret_l. rewrite interp_state_tau.
     rewrite try_catch_tau. gstep. constructor. gstep. constructor.
     gfinal. left. eauto.
Qed.


(* what is the precise compositional condition 
   maybe if I pick RE carefully there will be a clear compositional thing

*)
(* 
Lemma interp_imp_try_catch_comp Label RE R RR ttry1 ttry2 kcatch1 kcatch2 :
  (forall l1 l2 σ1 σ2, RE ... -> pi_eqit_secure Label  kcatch1 (l1, σ1) )
*)

(* this needs to take in two events can do tomorrow morning *)
Variant Rexc (P : sensitivity -> map -> Prop) : forall A, (exceptE (sensitivity * map) +' IOE) A -> Prop :=
  | rexcio A (io : IOE A) : Rexc P A (inr1 io) 
  | rexc l σ : P l σ -> Rexc P void (inl1 (Throw _ (l, σ) ) )
.

(* Need something like the bind rule but for try_catch with the new pi_eqit_secure definition 
   This is another trade off,
   I am a bit worried about having space to talk about all of the differences and why we have
   them, but that is what the meeting tomorrow is about 

 *)

(* Now I am concerned that my proposed new pi_eqit_secure is insufficient 
   it constrains final states only in the case where both exceptions are public
   I think I just need to talk with the rest of the team, figure out what to do

   The key problem seems with the original proof lies with programs like this

   while pub_x <> 0 do
     x := x - 1;
     if priv_y = 0 
     then raise private 
     else skip
     print public pub_x
   end

   depending on initial value of priv_y it is either a sequence of prints to the
   public stream or a single exception 

   In the standard semantics this is fine
   but when we interpret away exceptions,
   this would enforce that a ret would be equiv to a print 


   My original pi_eqit_secure definition still enables an improvement on the type system,
   by relating spin to Ret, we can get a permissive while rule, even if we would still
   need to be restrictive on the exceptions,
   what I would need to do is change the Rsense relation, removing the mixed
   cases and adding the restriction to public exceptions in the exception case 
   the nice part is that this would only make the proofs easier

   private exceptions are hard :`(
 *)
