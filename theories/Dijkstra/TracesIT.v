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
     Dijkstra.EuttDiv
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section TraceSpec.
  Context (E : Type -> Type).
  Arguments resp_eutt {E} {A}.

  Definition TraceSpecInput (A : Type) := {p : ibranch E A -> Prop | resp_eutt p}.

  Instance proper_eutt_spec_in {A} {p : TraceSpecInput A} : Proper (@eutt _ A A eq ==> iff) (proj1_sig p). 
  Proof.
    intros b1 b2 Heutt. destruct p as [p Hp]. simpl. split; intros;
    eapply Hp; try apply H; auto. symmetry. auto.
  Qed.

  Definition TraceSpec (A : Type) := ev_list E -> {w : TraceSpecInput A -> Prop | 
                                      forall (p p' : TraceSpecInput A), (forall b, b ∈ p -> b ∈ p') -> w p -> w p'  }.

  Instance EqM_TraceSpec : EqM TraceSpec := fun _ w1 w2 => forall log p, w1 log ∋ p <-> w2 log ∋ p. 
  (* look over this code *)
  (* https://github.com/FStarLang/FStar/blob/dm4all/examples/dm4all/IORWLocal.fst *)

  Notation "↑ log" := (ev_list_to_stream log) (at level 30).

  Program Definition ret_ts1 {A : Type} (a : A) : TraceSpec A := fun log p => p ( Ret a).

  Program Definition ret_ts2 {A : Type} (a : A) : TraceSpec A := fun log p => p (↑log ++ Ret a).


  (* RE : forall A B, E1 A -> A -> E2 B -> B -> Prop  
     (forall a1 a2, RE e1 a1 e2 a2 -> corec (k1 a1) (k2 a2)) -> eutt VisF e1 k1 VisF e2 k2

*)
  
  Program Definition bind_ts1_all {A B : Type} (w : TraceSpec A) (g : A -> TraceSpec B) :=
    fun log p => w log (fun b : itree (EvAns E) A  => (forall a log', b ≈ (↑log' ++ Ret a) -> g a log' p ) /\ (must_diverge b -> p (div_cast b) )  ).
  Next Obligation.
    intros b1 b2 Heutt. split; intros; split; basic_solve.
    - apply H. rewrite Heutt. auto.
    - rewrite <- Heutt. apply H1. rewrite Heutt. auto.
    - apply H. rewrite <- Heutt. auto.
    - rewrite Heutt. apply H1. rewrite <- Heutt. auto.
  Qed.


  Program Definition bind_ts1 {A B : Type} (w : TraceSpec A) (g : A -> TraceSpec B) : TraceSpec B :=
    fun log p => w log (fun b : itree (EvAns E) A => (exists a, exists log', b ≈ (↑log' ++ Ret a)  /\ g a log' p) \/ 
                                 (must_diverge b /\ p (div_cast b )) ).
  Next Obligation.
    intros b1 b2 Heutt. split; intros; basic_solve.
    - left. exists a. exists log'.
      rewrite <- Heutt. auto.
    - right. rewrite <- Heutt. auto.
    - left. exists a. exists log'. rewrite Heutt.
      auto.
    - right. rewrite Heutt. auto.
  Qed.
  Next Obligation.
    destruct (w log) as [wl Hwl]. simpl in *. 
    eapply Hwl; try apply H0. simpl. clear H0. intros.
    basic_solve.
    - left. exists a. exists log'. split; auto.
      destruct (g a log') as [gal Hgal]. simpl in *.
      eapply Hgal; try apply H1. auto.
    - right. auto.
 Qed.
    

  Instance TraceSpecMonad : Monad TraceSpec :=
    {
      ret := @ret_ts2;
      bind := @bind_ts1;
    }.

  (*If initial logs are allow to be inf, and b in inf then for any a there is some log, 
    b = log ++ ret a, even if b never actually returns it, this is problematic, so I will
    restrict it, I think this restriction is justifiable*)

  Lemma apply_monot : forall (A : Type) (w : TraceSpec A) (log : ev_list E) (p p' : TraceSpecInput A),
      (forall b, p ∋ b -> p' ∋ b) -> w log ∋ p -> w log ∋ p'.
  Proof.
    intros. destruct (w log) as [w' Hw'].
    simpl in *. eauto.
  Qed.



  Program Instance TraceSpecMonadLaws : MonadLaws TraceSpec.
  Next Obligation.
    rename a into A. rename b into B. rename x into a.
    red. red. cbn. split; intros; basic_solve.
    - apply inv_append_eutt in H. destruct H. subst. auto. 
    - exfalso. assert (can_converge a (↑ log ++ Ret a) ).
      { apply can_converge_append. apply can_converge_list_to_stream. }
      eapply must_diverge_not_converge; eauto.
    - left. exists a. exists log. split; auto. reflexivity.
  Qed.
  Next Obligation.
    rename a into A. rename x into w. red. red. cbn. split; intros; basic_solve.
    - eapply apply_monot; try apply H. clear H.
      simpl. intros. basic_solve.
      + rewrite H. auto.
      + apply div_cast_nop in H.
        rewrite H. auto.
    - eapply apply_monot; try apply H. clear H.
      intros. simpl. destruct (classic_converge_ibranch b).
      + basic_solve. left. exists r. exists log0. split.
        * symmetry. auto.
        * rewrite H0. auto.
      + right. split; auto. rewrite div_cast_nop in H; auto. 
  Qed.
  Next Obligation.
    rename a into A. rename b into B. rename c into C. rename x into w.
    red. red. cbn. split; intros; basic_solve.
    - eapply apply_monot; try apply H. clear H. simpl. intros.
      basic_solve.
      + left. exists a. exists log'. auto.
      + exfalso. 
        assert (can_converge a (↑log' ++ Ret a) ).
        { apply can_converge_append. apply can_converge_list_to_stream. }
        assert (must_diverge (@div_cast (EvAns E) A A b) ).
        { apply must_diverge_bind. auto. }
        rewrite <- H0 in H2. unfold div_cast in H3. cbn in H3.
        eapply must_diverge_not_converge with (r := a) ; eauto.
        apply must_diverge_bind. auto.
      + right. split; auto.
        destruct p as [p Hp]. simpl in *. eapply Hp; try apply H1.
        eapply eutt_clo_bind with (UU := fun a b => False); intuition.
        apply div_bind_nop. auto.
    - eapply apply_monot; try apply H. clear H. simpl. intros.
      basic_solve.
      + left. exists a. exists log'. auto.
      + right. split; auto. right. split.
        * apply must_diverge_bind. auto.
        * destruct p as [p Hp]. simpl in *. eapply Hp; try apply H0.
          eapply eutt_clo_bind with (UU := fun a b => False); intuition.
          apply eutt_div_sym. apply div_bind_nop. auto.
   Qed.

(*  
  x := Read;
  while x
        Write;
        x := Read

  do b := Decide () while b 
        b := Decide()

  iter (fun _ => b <- trigger Decide;; if b then ret inl tt else ret inr tt) tt
*)


End TraceSpec.

Section TraceSpec2.

  Context (E : Type -> Type).
  Arguments resp_eutt {E} {A}.

  Definition TraceSpecIn (A : Type) := {p : ibranch E A -> Prop | resp_eutt p}.

  Definition TraceSpec2 (A : Type) := {w : TraceSpecIn A -> Prop |  forall (p p' : TraceSpecIn A), (forall b, b ∈ p -> b ∈ p') -> w p -> w p'}.

  Program Definition ret_ts (A : Type) (a : A) : TraceSpec2 A := fun p => p (Ret a).

  Program Definition bind_ts (A B : Type) (w : TraceSpec2 A) (g : A -> TraceSpec2 B) : TraceSpec2 B := 
    fun p => w (fun b : itree (EvAns E) A => 
                  (exists a, can_converge a b /\ g a p) \/ (must_diverge b /\ p (div_cast b) ) ).
  Next Obligation.
    intros b1 b2 Heutt. split; intros; basic_solve.
    - left. exists a. split; auto. rewrite <- Heutt. auto.
    - right. rewrite <- Heutt at 1. split; auto. destruct p as [p Hp]. simpl in *.
      eapply Hp; eauto. rewrite Heutt. reflexivity.
    - left. exists a. rewrite Heutt. auto.
    - right. rewrite Heutt at 1. split; auto. destruct p as [p Hp]. simpl in *.
      eapply Hp; eauto. rewrite Heutt. reflexivity.
  Qed.
  Next Obligation.
    destruct w as [w Hw]. simpl in *. eapply Hw; try apply H0.
    clear H0. simpl. intros. basic_solve.
    - left. exists a. split; auto. destruct (g a) as [ga Hga]. simpl in *.
      eauto.
    - right. split; auto.
  Qed.

  Instance EqM_TraceSpec2 : EqM TraceSpec2 := fun _ w1 w2 => forall p, w1 ∋ p <-> w2 ∋ p. 

  Instance MonadTraceSpec2 : Monad TraceSpec2 :=
    {
      ret := ret_ts;
      bind := bind_ts
    }.

  Lemma apply_monot' : forall (A : Type) (w : TraceSpec2 A) (p p' : TraceSpecIn A),
      (forall b, p ∋ b -> p' ∋ b) -> w ∋ p -> w ∋ p'.
  Proof.
    intros. destruct w as [w' Hw'].
    simpl in *. eauto.
  Qed.


  Program Instance MonadLawsTraceSpec2 : MonadLaws TraceSpec2.
  Next Obligation.
    rename a into A. rename b into B. rename x into a. red. red. cbn.
    split; intros; basic_solve.
    - admit. (*basic can_converge lemma*)
    - pinversion H.
    - left. exists a. split; auto. apply conv_ret. reflexivity.
  Admitted.
  Next Obligation.
    rename a into A. rename x into w. red. red. cbn. 
    split; intros.
    - eapply apply_monot'; try apply H. simpl. intros.
      basic_solve.
      + (*significant problem*)
  Admitted.
  Next Obligation.
    Admitted.

End TraceSpec2.
