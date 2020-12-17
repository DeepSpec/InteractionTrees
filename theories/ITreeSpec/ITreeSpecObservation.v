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
     Dijkstra.EuttDiv
     Dijkstra.ITracePreds
     Dijkstra.ITraceBindTrigger
     Dijkstra.TracesIT
     Dijkstra.StateSpecT
     Dijkstra.StateIOTrace
     ITreeSpec.ITreeSpecDefinition
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


CoFixpoint obs_trace_ {E R} (otr : itrace' E R) : itree_spec E R :=
  match otr with
  | RetF r => Ret r
  | TauF t => Tau (obs_trace_ (observe t))
  | VisF (evans _ e a) k => 
    Vis (Spec_Vis (evans _ e a)) (fun _ => obs_trace_ (observe (k tt) ) ) 
  | VisF (evempty _ H e) k => 
    Vis (Spec_Vis (evempty _ H e) ) (empty_cont)
  end.

Definition obs_trace {E R} (tr : itrace E R) :=
  obs_trace_ (observe tr).



CoFixpoint obs_ {E R} (ot : itree' E R) : itree_spec E R :=
  match ot with 
  | RetF r => Ret r
  | TauF t => Tau ( obs_ (observe t) )
  | @VisF _ _ _ A e k => 
    (* Note that which branch you will need to take is not computable
       but the information is contained *)
    or_spec
      (Vis Spec_exists (fun a => Vis (Spec_Vis (evans _ e a)) (fun _ => (obs_ (observe (k a))  ) ) ) )
      (show_empty A >>= ( fun H => Vis (Spec_Vis (evempty _ H e) ) empty_cont))
      (* (Vis Spec_empty (fun H => Vis (Spec_Vis (evempty _ H e) ) empty_cont) ) *)


  end.

Definition obs {E R} (t : itree E R) :=
  obs_ (observe t).

Global Instance proper_obs {E R}: Proper (@eq_itree E R R eq ==> eq_itree eq) obs.
Proof.
  red. red. pcofix CIH. intros t1 t2 Heutt. pfold. red. cbn.
  punfold Heutt. red in Heutt. unfold observe. cbn. inversion Heutt; subst; cbn; auto; pclearbot;
  try (inversion CHECK).
  - constructor. right. eapply CIH; eauto.
  - constructor. intros [ | ].
    + left. pfold. red. cbn. constructor. intros. left. pfold.
      constructor. intros. right.
      eapply CIH; eauto.
    + left. pfold. red. cbn. constructor. intros. left.
      pfold. red. cbn. constructor. intros; contradiction.
Qed.


Lemma obs_ret : forall E R (r : R), @obs E R (Ret r) ≅ Ret r.
Proof.
  intros. pfold. red. cbn. auto.
Qed.

Lemma obs_vis : forall E R A (e : E A) (k : A -> itree E R),
    obs (Vis e k) ≅ 
        or_spec (Vis Spec_exists (fun a : A => Vis (Spec_Vis (evans _ e a) ) (fun _ => obs (k a) ) ))
                (show_empty A >>= (fun H => Vis (Spec_Vis (evempty _ H e) ) empty_cont ) ).
Proof.
  intros. pfold. red. cbn. constructor. intros [ | ].
  - left. pfold. red. cbn. constructor. left. pfold. constructor.
    intros; left. enough (obs (k v) ≅ obs (k v) ); auto. reflexivity.
  - left. pfold. red. cbn. constructor. intros H. left. pfold.
    red. cbn. constructor. intros [].
Qed.

Lemma obs_tau : forall E R (t : itree E R), obs (Tau t) ≅ Tau (obs t).
Proof.
  intros. pfold. red. cbn. constructor. left.
  enough (obs t ≅ obs t); auto. reflexivity.
Qed.
