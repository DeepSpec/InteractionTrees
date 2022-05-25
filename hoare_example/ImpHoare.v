From Coq Require Import
     Arith Lia (* nia *)
     Morphisms
.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Props.Divergence.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
     Dijkstra.StateSpecT
     Dijkstra.StateDelaySpec
.

From Paco Require Import paco.

From hoare Require Import Imp.

Import Monads.
Import MonadNotation.
Import ImpNotations.
#[local] Open Scope monad_scope.
#[local] Open Scope itree_scope.
#[local] Open Scope imp_scope.

Definition denote_imp (c : com) : stateT env Delay unit :=
  interp_imp (denote_com c).

Definition hoare_triple (P Q : env -> Prop) (c : com) : Prop :=
  forall (s s' :env), P s -> (denote_imp c s ≈ ret (s',tt)) -> Q s'.

Definition lift_imp_post (P : env -> Prop) : Delay (env * unit) -> Prop :=
  fun (t : Delay (env * unit) ) => (exists (s : env), ret (s, tt) ≈ t /\ P s).

Notation "{{ P }} c {{ Q }}" := (hoare_triple P Q c) (at level 70).

Definition is_bool (E : Type -> Type) (bc : bool) (be : bexp) (s : env) : Prop :=
   @interp_imp E bool (denote_bexp be) s ≈ ret (s, bc).

Definition is_true (b : bexp) (s : env) : Prop :=
  is_bool void1 true b s.

Definition is_false  (b : bexp) (s : env) : Prop :=
  is_bool void1 false b s.

(*
Ltac unf_intep := unfold interp_imp, interp_map, interp_state, interp, Basics.iter, MonadIter_stateT0, interp, Basics.iter, MonadIter_stateT0.
*)

Lemma aexp_term : forall (E : Type -> Type) (ae : aexp) (s : env),
    exists (n : nat), @interp_imp void1 _ (denote_aexp ae) s ≈ Ret (s,n).
Proof.
  intros. induction ae.
  - exists n. cbn. tau_steps. reflexivity.
    (*getvar case, extract to a lemma*)
  - cbn. exists (lookup_default x 0 s).
    tau_steps. reflexivity.
  - basic_solve. exists (n0 + n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
  - basic_solve. exists (n0 - n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
  - basic_solve. exists (n0 * n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
Qed.

Lemma bools_term : forall (be : bexp) (s : env),
    exists (bc : bool), @interp_imp void1 _ (denote_bexp be) s ≈ Ret (s,bc).
Proof.
  intros. induction be.
  - exists true. cbn. unfold interp_imp, interp_map, interp_state. repeat rewrite interp_ret.
    tau_steps. reflexivity.
  - exists false. tau_steps. reflexivity.
  - specialize (aexp_term void1 a1 s) as Ha1. specialize (aexp_term void1 a2 s) as Ha2.
    basic_solve. exists (n0 =? n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite Ha1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_imp_bind.
    rewrite Ha2. tau_steps. reflexivity.
  - specialize (aexp_term void1 a1 s) as Ha1. specialize (aexp_term void1 a2 s) as Ha2.
    basic_solve. exists (n0 <=? n).
    cbn. setoid_rewrite interp_imp_bind. rewrite Ha1.
    setoid_rewrite bind_ret_l. setoid_rewrite interp_imp_bind.
    rewrite Ha2. tau_steps. reflexivity.
  - basic_solve. exists (negb bc). cbn.
    setoid_rewrite interp_imp_bind. rewrite IHbe. tau_steps.
    reflexivity.
  - basic_solve. exists (bc0 && bc)%bool.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHbe1. setoid_rewrite bind_ret_l.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHbe2. tau_steps.
    reflexivity.
Qed.

Lemma classic_bool : forall (b : bexp) (s : env), is_true b s \/ is_false b s.
Proof.
  intros. specialize (bools_term b s) as Hbs.
  basic_solve. destruct bc; auto.
Qed.

(*   *)

Lemma hoare_seq : forall (c1 c2 : com) (P Q R : env -> Prop), {{P}} c1 {{Q}} -> {{Q}} c2 {{R}}  ->
                                                               {{P}} c1 ;;; c2 {{R}}.
Proof.
  unfold hoare_triple. intros c1 c2 P Q R Hc1 Hc2 s s' Hs Hs'.
  unfold denote_imp in Hs'. cbn in Hs'. rewrite interp_imp_bind in Hs'.
  fold (denote_imp c1) in Hs'. fold (denote_imp c2) in Hs'.
  destruct (eutt_reta_or_div (denote_imp c1 s) ); basic_solve.
  - destruct a as [s'' [] ]. rewrite <- H in Hs'. setoid_rewrite bind_ret_l in Hs'. symmetry in H.
    eapply Hc2; eauto.
  - apply div_spin_eutt in H. rewrite H in Hs'. rewrite <- spin_bind in Hs'.
    symmetry in Hs'. exfalso. eapply not_ret_eutt_spin. eauto.
Qed.

Lemma hoare_if : forall (c1 c2 : com) (b : bexp) (P Q : env -> Prop),
    {{fun s => is_true b s /\ P s}} c1 {{Q}} ->
    {{fun s => is_false b s /\ P s}} c2 {{Q}} ->
    {{ P }} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  unfold hoare_triple. intros c1 c2 b P Q Hc1 Hc2 s s' Hs.
  unfold denote_imp. cbn.
  destruct (classic_bool b s).
  - unfold is_true, is_bool in H. rewrite interp_imp_bind.
    rewrite H. setoid_rewrite bind_ret_l. apply Hc1. auto.
  - unfold is_false, is_bool in H. rewrite interp_imp_bind.
    rewrite H. setoid_rewrite bind_ret_l. apply Hc2. auto.
Qed.

Definition app {A B : Type} (f : A -> B) (a : A) := f a.

Definition run_state_itree {A S : Type} {E : Type -> Type} (s : S) (m : stateT S (itree E) A )  : itree E (S * A) :=
  m s.

Global Instance EqStateEq {S R: Type} {E : Type -> Type} : Equivalence (@state_eq E R S).
Proof.
  constructor; repeat intro.
  - reflexivity.
  -  unfold state_eq in H. symmetry. auto.
  - unfold state_eq in *. rewrite H. auto.
Qed.

Global Instance run_state_proper_eq_itree {E : Type -> Type} {S R : Type} {s : S} :
  Proper (@state_eq E S R ==> eq_itree eq) (@run_state_itree R S E s).
Proof.
  repeat intro. unfold run_state_itree. unfold state_eq in H. rewrite H. reflexivity.
Qed.

Global Instance run_state_proper_eutt {E : Type -> Type} {S R : Type} {s : S} :
  Proper (@state_eq E S R ==> eutt eq) (@run_state_itree R S E s).
Proof.
  repeat intro. unfold run_state_itree. unfold state_eq in H. rewrite H. reflexivity.
Qed.

Global Instance eutt_proper_under_interp_state
       {E F: Type -> Type} {S R : Type} {h : E ~> stateT S (itree F) } :
  Proper (eq_itree eq ==> @state_eq F S R) (fun (t : itree E R) =>  interp_state h t).
Proof.
  repeat intro. unfold interp_state. rewrite H. reflexivity.
Qed.

(*
Check (case_ (handle_map (V := value) pure_state ) ).

Timeout 5 Definition run_state_map {value A : Type} (t : itree (mapE var 0 +' void1)  A) s  : itree void1 ( env * A):=
  interp_state (case_ (handle_map (V := value) ) pure_state) t s.
*)

Section interp_state_eq_iter.
  Context {E F: Type -> Type}.
  Context (S : Type).
  Context (f : E ~> stateT S (itree F) ).
  Context (A B : Type).
  Context (g : A ->itree E (A + B) ).
  Context (a : A).


  Lemma interp_state_eq_iter : state_eq (interp_state f (ITree.iter g a) )
                              (MonadIter_stateT0 _ _ (fun a0 => interp_state f (g a0)) a).
  Proof.
    unfold ITree.iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
    eapply interp_state_iter; reflexivity.
  Qed.

End interp_state_eq_iter.
Set Default Timeout 15.

Global Instance proper_state_eq_iter {S: Type} :
  Proper (@state_eq void1 S (unit + unit) ==> @state_eq void1 S (unit) ) (fun body => @MonadIter_stateT0 Delay S _ _ unit unit (fun _ : unit => body) tt ).
Proof.
  repeat intro.
  unfold MonadIter_stateT0, Basics.iter, MonadIterDelay. eapply eq_itree_iter.
  repeat intro. subst. destruct y0 as [s' [] ].
  simpl. specialize (H s'). rewrite H. reflexivity.
Qed.

Lemma interp_state_bind_state : forall (E F : Type -> Type) (A B S : Type)
                   (h : forall T : Type, E T -> S -> itree F (S * T) ) (t : itree E A)
                   (k : A -> itree E B),
    state_eq (interp_state h (ITree.bind t k))
             (bind (interp_state h t) (fun a => interp_state h (k a) ) ).

Proof.
  unfold state_eq. intros. eapply interp_state_bind.
Qed.

Definition state_eq2 {E : Type -> Type} {A B S : Type} (k1 k2 : A -> stateT S (itree E) B ) : Prop :=
  forall a, state_eq (k1 a)  (k2 a).

Lemma eq_itree_clo_bind {E : Type -> Type} {R1 R2 : Type} :
  forall (RR : R1 -> R2 -> Prop) (U1 U2 : Type) (UU : U1 -> U2 -> Prop)
         (t1 : itree E U1) (t2 : itree E U2)
         (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2),
    eq_itree UU t1 t2 ->
    (forall (u1 : U1) (u2 : U2), UU u1 u2 -> eq_itree RR (k1 u1) (k2 u2)  ) ->
    eq_itree RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. unfold eq_itree in *. eapply eqit_bind'; eauto.
Qed.


Global Instance bind_state_eq2 {E : Type -> Type} {A B S : Type} {m : stateT S (itree E) A} :
  Proper (@state_eq2 E A B S ==> @state_eq E S B) (bind m).
Proof.
  repeat intro. unfold state_eq2, state_eq in H. cbn.
  eapply eq_itree_clo_bind; try reflexivity. intros. subst.
  destruct u2 as [s' a]. simpl. rewrite H. reflexivity.
Qed.

(*can actually make this nicer*)
Lemma compile_while : forall (b : bexp) (c : com),
                             ((denote_imp ( WHILE b DO c END )) ≈ MonadIter_stateT0 unit unit
                                         (fun _ : unit => bind (interp_imp (denote_bexp b))
                                                               (fun b : bool => if b
                                                                         then bind (denote_imp c) (fun _ : unit => interp_imp (Ret (inl tt)) )
                                                                         else interp_imp (Ret (inr tt))) ) tt)%monad.
Proof.
  intros. simpl. unfold denote_imp. simpl. unfold while. unfold interp_imp at 1, interp_map at 1.
  cbn. red. red. intros. symmetry.
  rewrite interp_iter. do 3 red.
  match goal with | |- _ ≈ ?m _ => set m as while_denote; fold while_denote end.
  assert (Hwhile_rewrite : state_eq while_denote while_denote); try reflexivity.
  unfold while_denote in Hwhile_rewrite at 2.
  setoid_rewrite interp_state_eq_iter in Hwhile_rewrite.
  fold (run_state_itree s while_denote). rewrite Hwhile_rewrite.
  clear Hwhile_rewrite. unfold run_state_itree.
  match goal with |- MonadIter_stateT0 _ _ (fun _ :unit => ?m1) _ _ ≈ MonadIter_stateT0 _ _ (fun _ : unit => ?m2) _ _ =>
                  enough (state_eq m1 m2) end.
  - eapply proper_state_eq_iter in H.
    match goal with |- ?m1 s ≈ ?m2 s => set m1 as while_denote1; fold while_denote1;
                                        set m2 as while_denote2; fold while_denote2 end.
    fold (run_state_itree s while_denote1). fold (run_state_itree s while_denote2).
    unfold while_denote1. unfold while_denote2. rewrite H. reflexivity.
 - rewrite interp_bind. rewrite interp_state_bind_state.
   clear s. intro s. eapply eq_itree_clo_bind; try reflexivity.
   intros. subst. destruct u2 as [s' b0 ]. simpl. destruct b0.
   + rewrite interp_bind. rewrite interp_state_bind.
     unfold interp_imp, interp_map. reflexivity.
   + unfold interp_imp, interp_map. reflexivity.
Qed.




Lemma hoare_while : forall (c : com) (b : bexp) (P : env -> Prop),
    {{fun s => is_true b s /\ P s}} c {{ P  }} ->
    {{ P }} WHILE b DO c END {{ fun s => is_false b s /\ P s}}.
Proof.
  unfold hoare_triple. intros.
  specialize (compile_while b c) as Hbc. red in Hbc. red in Hbc.
  rewrite Hbc in H1. clear Hbc.
  specialize (loop_invar_state env unit unit) as Hloop. unfold State in Hloop.
  rename H1 into Heutt. rename H0 into Hs.
  set ((fun _ : unit =>
             b <-
             interp_imp
               (denote_bexp b);;
             (if b
              then
               _ <- denote_imp c;;
               interp_imp
                 (Ret (inl tt))
              else
               interp_imp
                 (Ret (inr tt))))) as body.
  split.
  - set (fun (t : Delay (env * unit) ) =>
           (exists s, t ≈ ret (s,tt) /\ is_false b s) \/ may_diverge t
        ) as p.
    set (fun (t : Delay (env * unit + env * unit)) =>
           (exists s, (t ≈ ret (inl (s,tt)) ) \/ ((t ≈ ret (inr (s,tt)) /\ is_false b s)) )  \/ may_diverge t
        ) as q.
    assert (resp_eutt p) as Hp.
    {
      unfold p. unfold is_false, is_bool.
      intros t1 t2 He. split; intro; basic_solve.
      - left. exists s0.  split; auto. rewrite <- He. auto.
      - rewrite He in H0. auto.
      - left. exists s0. split; auto. rewrite He. auto.
      - rewrite <- He in H0. auto.
    }
    assert (resp_eutt q) as Hq.
    {
      unfold q. unfold is_true, is_false, is_bool.
      intros t1 t2 He. split; intros; basic_solve.
      - left. exists s0. rewrite He in H0. auto.
      - left. exists s0. rewrite He in H0. auto.
      - rewrite He in H0. auto.
      - left. exists s0. rewrite He. auto.
      - left. exists s0. rewrite He. auto.
      - rewrite <- He in H0. auto.
    }
   enough (p (Ret (s',tt) ) ).
    {
      unfold p in H0. basic_solve; auto. pinversion H0.
    }
    enough (p (CategoryOps.iter body tt s) ).
    {
      eapply Hp; try apply H0. unfold CategoryOps.iter, Iter_Kleisli, Basics.iter.
      unfold body. symmetry. auto.
    }
    enough ((p \1/ may_diverge) (CategoryOps.iter body tt s) ).
    {
      destruct H0; auto. unfold p. auto.
    }
    specialize Hloop with (s := s) (p := p) (q := q).
    eapply Hloop; eauto.
    + unfold reassoc. unfold body.
      destruct (eutt_reta_or_div (interp_imp (denote_com c) s ) );
      destruct (classic_bool b s); basic_solve.
      * do 2 red in H1. unfold interp_imp, interp_map in H1.
        destruct a as [s'' [] ].
        eapply Hq.
        -- cbn. setoid_rewrite bind_bind.
           rewrite H1.
           setoid_rewrite bind_ret_l. simpl.
           setoid_rewrite bind_bind. rewrite <- H0.
           tau_steps. reflexivity.
        -- unfold q. left. exists s''. left. reflexivity.
      * do 2 red in H1. unfold interp_imp, interp_map in H1.
        destruct a as [s'' [] ].
        eapply Hq.
        -- cbn. rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
           simpl. tau_steps. reflexivity.
        -- unfold q. left. exists s. right. split; auto. reflexivity.
      * do 2 red in H1. unfold interp_imp, interp_map in H1.
        eapply Hq.
        -- cbn. rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
           simpl. apply div_spin_eutt in H0. rewrite H0. setoid_rewrite bind_bind.
           rewrite <- spin_bind. reflexivity.
        -- red. right. apply spin_diverge.
      * do 2 red in H1. unfold interp_imp, interp_map in H1.
        eapply Hq.
        -- cbn. rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
           simpl. apply div_spin_eutt in H0.
           tau_steps. reflexivity.
        -- red. left. exists s. right. split; auto; reflexivity.
   + unfold q,p. unfold DelaySpecMonad.loop_invar_imp. intros.
     basic_solve.
     * cbn in H0. exfalso. destruct (eutt_reta_or_div t); basic_solve.
       -- rewrite <- H1 in H0. setoid_rewrite bind_ret_l in H0. basic_solve.
       -- apply div_spin_eutt in H1. rewrite H1 in H0. rewrite <- spin_bind in H0.
          symmetry in H0. eapply not_ret_eutt_spin; eauto.
     * cbn in H0. destruct (eutt_reta_or_div t); basic_solve; auto.
       rewrite <- H2 in H0. setoid_rewrite bind_ret_l in H0. basic_solve. left.
       exists s0. split; auto. symmetry. auto.
     * right. destruct (eutt_reta_or_div t); basic_solve; auto.
       cbn in H0. rewrite <- H1 in H0. setoid_rewrite bind_ret_l in H0.
       pinversion H0.
  + unfold q.
    unfold DelaySpecMonad.iter_lift, iso_destatify_arrow, reassoc.
    basic_solve; try (destruct (classic_bool b s0) );
      try (destruct (eutt_reta_or_div (interp_imp (denote_com c) s0 ) )); basic_solve.
    * eapply Hq.
      -- cbn. rewrite H0. setoid_rewrite bind_ret_l.
         setoid_rewrite bind_bind. do 2 red in H1. unfold interp_imp, interp_map in H1.
         rewrite H1. setoid_rewrite bind_ret_l. simpl.
         destruct a as [s1 [] ]. rewrite <- H2. setoid_rewrite bind_bind.
         setoid_rewrite bind_ret_l. simpl. tau_steps. reflexivity.
      -- red. left. destruct a as [s'' [] ]. exists s''. left. reflexivity.
    * eapply Hq.
      -- cbn. rewrite H0. setoid_rewrite bind_ret_l. setoid_rewrite bind_bind.
         do 2 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
         setoid_rewrite bind_ret_l. simpl. apply div_spin_eutt in H2. rewrite H2.
         setoid_rewrite bind_bind. rewrite <- spin_bind. reflexivity.
      -- right. apply spin_diverge.
    * destruct a as [s'' [] ]. eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret_l.
         do 2 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
         setoid_rewrite bind_bind. setoid_rewrite bind_ret_l. simpl. tau_steps. reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret_l.
         do 2 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
         setoid_rewrite bind_bind. setoid_rewrite bind_ret_l. simpl. tau_steps. reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * do 2 red in H1. do 2 red in H2. rewrite H1 in H2.
      apply eutt_inv_Ret in H2. injection H2. discriminate.
    * do 2 red in H1. do 2 red in H2. rewrite H1 in H2.
      apply eutt_inv_Ret in H2. injection H2. discriminate.
    * eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret_l.  reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret_l.  reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * right. cbn. apply div_spin_eutt in H0. rewrite H0. rewrite <- spin_bind.
      apply spin_diverge.
   - set (fun (t : Delay (env * unit)) =>
           (exists s, t ≈ ret (s,tt) /\ P s ) \/ may_diverge t
        ) as p.
    set (fun (t : Delay (env * unit + env * unit)) =>
           (exists s, (t ≈ ret (inl (s,tt) ) \/ t ≈ ret (inr (s,tt) ) ) /\ P s )\/ may_diverge t )  as q.
    assert (resp_eutt p) as Hp.
    {
      unfold p. intros t1 t2 He. split; intros; basic_solve.
      - left. exists s0. rewrite He in H0. auto.
      - right. rewrite He in H0. auto.
      - left.  exists s0. rewrite <- He in H0. split; auto.
      - right. rewrite He. auto.
    }
      assert (resp_eutt q) as Hq.
      {
        unfold q. intros t1 t2 He. split; intros; basic_solve.
        - left. exists s0. rewrite He in H0. auto.
        - left. exists s0. rewrite He in H0. auto.
        - right. rewrite He in H0. auto.
        - left. rewrite <- He in H0. exists s0. auto.
        - left. rewrite <- He in H0. exists s0. auto.
        - right. rewrite He. auto.
      }
      specialize Hloop with (s := s) (p := p) (q := q).

      enough (p (Ret (s',tt))).
      {
        unfold p in H0. basic_solve; auto. pinversion H0.
      }
      enough ((p \1/ may_diverge) (CategoryOps.iter body tt s ) ).
      {
        destruct H0.
        - eapply Hp; try apply H0. rewrite <- Heutt. reflexivity.
        - unfold CategoryOps.iter, Iter_Kleisli, Basics.iter in H0.
          unfold body in H0. rewrite Heutt in H0. pinversion H0.
      }
      eapply Hloop; eauto.
      + unfold reassoc. unfold body. destruct (classic_bool b s).
        * assert (is_true b s /\ P s); auto.
          destruct (eutt_reta_or_div (interp_imp (denote_com c) s) ); basic_solve.
          -- destruct a as [s'' [] ].
             unfold is_true, is_bool in H0.
             unfold interp_imp, interp_map in H0.
             eapply Hq.
             ++ cbn. setoid_rewrite bind_bind. rewrite H0.
                setoid_rewrite bind_ret_l. simpl. setoid_rewrite bind_bind.
                rewrite <- H2. tau_steps.
                reflexivity.
             ++ specialize (H s s''). unfold q. left. exists s''. split; try (left; reflexivity).
                eapply H; eauto. symmetry. auto.
          -- apply div_spin_eutt in H2.
             cbn. rewrite bind_bind.
             unfold is_true, is_bool in H0.
             unfold interp_imp, interp_map in H0. rewrite H0.
             setoid_rewrite bind_ret_l. simpl. rewrite H2.
             setoid_rewrite bind_bind. rewrite <- spin_bind.
             right. apply spin_diverge.
        * unfold is_false, is_bool, interp_imp, interp_map in H0. cbn.
          eapply Hq.
          -- setoid_rewrite bind_bind. rewrite H0. setoid_rewrite bind_ret_l.
             simpl. cbn. tau_steps. reflexivity.
          -- unfold q. left. exists s. split; auto. right. reflexivity.
      + red. intros. unfold p. unfold q in H0. basic_solve.
        * cbn in H0.
          destruct (eutt_reta_or_div t); basic_solve.
          -- destruct a as [s'' [] ]. rewrite <- H2 in H0.
             setoid_rewrite bind_ret_l in H0. basic_solve.
          -- exfalso. apply div_spin_eutt in H2. rewrite H2 in H0. rewrite <- spin_bind in H0.
             symmetry in H0. apply not_ret_eutt_spin in H0. auto.
        * cbn in H0.
        destruct (eutt_reta_or_div t); basic_solve.
        -- destruct a as [s'' [] ]. rewrite <- H2 in H0.
           setoid_rewrite bind_ret_l in H0. basic_solve. left. exists s0.
           symmetry in H2. auto.
        -- exfalso. apply div_spin_eutt in H2. rewrite H2 in H0.
           rewrite <- spin_bind in H0. symmetry in H0. apply not_ret_eutt_spin in H0. auto.
      * cbn in H0. right. destruct (eutt_reta_or_div t); auto.
        basic_solve. rewrite <- H1 in H0. setoid_rewrite bind_ret_l in H0.
        pinversion H0.
    + unfold DelaySpecMonad.iter_lift, iso_destatify_arrow, reassoc.
      intros t Ht. cbn.
      destruct (eutt_reta_or_div t);
         basic_solve.
      * destruct a as [s'' [] ].
        destruct (classic_bool b s'');
          destruct (eutt_reta_or_div (interp_imp (denote_com c) s'' )); basic_solve;
        eapply Hq.
        -- rewrite <- H0. setoid_rewrite bind_ret_l.
           setoid_rewrite bind_bind. do 2 red in H1.
           unfold interp_imp, interp_map in H1. rewrite H1. setoid_rewrite bind_ret_l.
           simpl. setoid_rewrite bind_bind.
           rewrite <- H2. setoid_rewrite bind_ret_l. destruct a as [s3 [] ].
           simpl. tau_steps. reflexivity.
        -- destruct a as [s3 [] ]. unfold q in Ht. basic_solve.
           ++ rewrite  H3 in H0. basic_solve.
              unfold q. left. exists s3. split; try (left; reflexivity). symmetry in H2.
              cbn in H0. pinversion H0. subst. injection REL; intros; subst.
              eapply H; eauto.
           ++ rewrite H3 in H0. cbn in *; basic_solve; pinversion H0; try discriminate; basic_solve.
           ++ rewrite <- H0 in H3. pinversion H3.
        -- rewrite <- H0. setoid_rewrite bind_ret_l. setoid_rewrite bind_bind.
           do 2 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
           setoid_rewrite bind_ret_l. simpl. apply div_spin_eutt in H2.
           setoid_rewrite bind_bind. rewrite H2.
           rewrite <- spin_bind. reflexivity.
        -- unfold q. right. apply spin_diverge.
        -- rewrite <- H0. setoid_rewrite bind_ret_l.
           unfold is_false, is_bool in H1. unfold interp_imp, interp_map in H1.
           rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret_l. simpl.
           tau_steps. reflexivity.
        -- unfold q. left. exists s''. split; try (right; reflexivity). unfold q in Ht.
           basic_solve.
           ++ rewrite H3 in H0. basic_solve. auto. pinversion H0. injection REL; intros; subst; auto.
           ++ rewrite H3 in H0. basic_solve. pinversion H0. discriminate.
           ++ rewrite <- H0 in H3. pinversion H3.
        -- rewrite <- H0. setoid_rewrite bind_ret_l.
           setoid_rewrite bind_bind.
           do 2 red in H1. unfold interp_imp, interp_map in H1.
           rewrite H1. setoid_rewrite bind_ret_l. simpl. tau_steps.
           reflexivity.
        -- unfold q. left. exists s''.
           split; try (right; reflexivity). unfold q in Ht.
           basic_solve.
           ++ rewrite H3 in H0. basic_solve. pinversion H0; injection REL; intros; subst; auto.
           ++ rewrite H3 in H0. basic_solve. pinversion H0; discriminate.
           ++ rewrite <- H0 in H3. pinversion H3.
     * destruct b0 as [s'' [] ]. eapply Hq.
       -- rewrite <- H0. setoid_rewrite bind_ret_l.
          reflexivity.
       -- unfold q. left. exists s''. split; try (right; reflexivity).
          unfold q in Ht. basic_solve.
          ++ rewrite H1 in H0. basic_solve. pinversion H0. discriminate.
          ++ rewrite H1 in H0. basic_solve. pinversion H0; injection REL; intros; subst; auto.
          ++ rewrite <- H0 in H1. pinversion H1.
     * clear Ht. unfold q. right. apply div_spin_eutt in H0.
       rewrite H0. rewrite <- spin_bind. apply spin_diverge.

Qed.

Lemma denote_imp_bind : forall (c1 c2 : com), state_eq (denote_imp (c1 ;;; c2)) (denote_imp c1 ;; denote_imp c2).
Proof.
  intros. intro. cbn. unfold denote_imp. simpl. setoid_rewrite interp_imp_bind.
  eapply eq_itree_clo_bind; try reflexivity. intros. subst. destruct u2. reflexivity.
Qed.

Definition state_eq_eutt {R S : Type} {E : Type -> Type} (m0 m1 : stateT S (itree E) R) :Prop :=
  forall s, m0 s ≈ m1 s.

Global Instance equiv_state_eq_eutt {R S} {E} : Equivalence (@state_eq_eutt R S E).
Proof.
  constructor; red; red; intros.
  - reflexivity.
  - red in H. rewrite H. reflexivity.
  - red in H. red in H0.  rewrite H. rewrite H0. reflexivity.
Qed.

Lemma state_eq_sub_state_eutt : forall (E : Type -> Type) (R S: Type) ,
    subrelation (@state_eq E S R) state_eq_eutt.
Proof.
  red. intros E R S m0 m1 Heq.
  red. red in Heq. intros. rewrite Heq. reflexivity.
Qed.

Global Instance state_eq_prop_state_eutt {R S} {E} : Proper (@state_eq E S R ==> state_eq ==> impl) state_eq_eutt.
Proof.
  red. red. intros m0 m1 Heq0. red. intros m2 m3. intros Heq2.
  red. intros. red. red in H. red in Heq2. red in Heq0. intros.
  rewrite <- Heq2. rewrite <- H. rewrite Heq0. reflexivity.
Qed.

Lemma set_var_val_interp : forall x n E, @state_eq_eutt _ _ E (interp_imp (trigger (SetVar x n))) (fun s => Ret (Maps.add x n s,tt)).
Proof.
  intros. intro. tau_steps. reflexivity.
Qed.

Fixpoint compute_aexp (a : aexp) (s : env) : value :=
  match a with
  | ANum n => n
  | AId x => lookup_default x 0 s
  | APlus a1 a2 => (compute_aexp a1 s) + (compute_aexp a2 s)
  | AMinus a1 a2 => (compute_aexp a1 s) - (compute_aexp a2 s)
  | AMult a1 a2 => (compute_aexp a1 s) * (compute_aexp a2 s)
  end.


Fixpoint compute_bexp (b : bexp) (s : env)  : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (compute_aexp a1 s) =? (compute_aexp a2 s)
  | BLe a1 a2 => (compute_aexp a1 s) <=? (compute_aexp a2 s)
  | BNot b0 => negb (compute_bexp b0 s)
  | BAnd b1 b2 => (compute_bexp b1 s) && (compute_bexp b2 s)
  end.

Lemma compute_aexp_sc : forall (a : aexp),
    @state_eq_eutt value env void1 (interp_imp (denote_aexp a)) (fun s => Ret (s, compute_aexp a s)).
Proof.
  intros. red. intros. induction a; simpl;
  try (tau_steps; reflexivity);
  try (rewrite interp_imp_bind; rewrite IHa1; rewrite bind_ret_l;
    rewrite interp_imp_bind; rewrite IHa2; rewrite bind_ret_l; tau_steps; reflexivity).
Qed.

Lemma compute_aexp_sc_tree : forall (a : aexp) (s : env),
    (@interp_imp void1 value (denote_aexp a) s) ≈ (Ret (s, compute_aexp a s) ).
Proof.
  intros. apply compute_aexp_sc.
Qed.


Lemma compute_bexp_sc : forall (b : bexp),
    @state_eq_eutt bool env void1 (interp_imp (denote_bexp b) ) (fun s => Ret (s, compute_bexp b s)).
Proof.
  intros. red. intros. induction b; simpl;
  try (tau_steps; reflexivity).
  - rewrite interp_imp_bind. rewrite compute_aexp_sc_tree.
    rewrite bind_ret_l. rewrite interp_imp_bind. rewrite compute_aexp_sc_tree.
    rewrite bind_ret_l. tau_steps. reflexivity.
  - rewrite interp_imp_bind. rewrite compute_aexp_sc_tree.
    rewrite bind_ret_l. rewrite interp_imp_bind. rewrite compute_aexp_sc_tree.
    rewrite bind_ret_l. tau_steps. reflexivity.
  - rewrite interp_imp_bind. rewrite IHb. rewrite bind_ret_l.
    tau_steps. reflexivity.
  - rewrite interp_imp_bind. rewrite IHb1. rewrite bind_ret_l.
    rewrite interp_imp_bind. rewrite IHb2. rewrite bind_ret_l.
    tau_steps. reflexivity.
Qed.

Lemma compute_bexp_sc_tree : forall (b : bexp) (s : env),
    (@interp_imp void1 bool (denote_bexp b) s ) ≈ (Ret (s, compute_bexp b s) ).
Proof.
  intros. apply compute_bexp_sc.
Qed.

Definition inc_var (x : var) (s : env) : env:=
  Maps.add x (1 + lookup_default x 0 s)%nat  s.

Lemma compute_assign_sc : forall (x : var) (a : aexp),
    state_eq_eutt (@interp_imp void1 unit (denote_com (x ::= a) ) )
                  (fun s => Ret (Maps.add x (compute_aexp a s) s, tt) ).
Proof.
  intros. simpl. intro. rewrite interp_imp_bind.
  rewrite compute_aexp_sc_tree. rewrite bind_ret_l. tau_steps. reflexivity.
Qed.

Lemma compute_assign_sc_tree : forall (x : var) (a : aexp) (s : env),
    (@interp_imp void1 unit (denote_com (x ::= a)) s ) ≈ Ret (Maps.add x (compute_aexp a s) s, tt ).
Proof.
  intros. apply compute_assign_sc.
Qed.
(*state_eq_eutt is proper wrt to verify_cond*)

Global Instance proper_verify_cond {S A : Type} {w : StateDelaySpec S A} :
  Proper (state_eq_eutt ==> iff) (verify_cond S w).
Proof.
  repeat intro. unfold verify_cond, DijkstraProp. split; intros.
  - repeat red in H0. repeat red. intros. specialize (H0 s p). destruct p as [p Hp].
    simpl in *.
    eapply Hp; [symmetry; apply H | eauto].
  - repeat red in H0. repeat red. intros. specialize (H0 s p). destruct p as [p Hp].
    simpl in *.
    eapply Hp; auto.
Qed.

Global Instance proper_verify_cond_strong {S A : Type} {w : StateDelaySpec S A} :
  Proper (state_eq ==> iff) (verify_cond S w).
Proof.
  repeat intro. unfold verify_cond, DijkstraProp. split; intros.
  - repeat red in H0. repeat red. intros. specialize (H0 s p). destruct p as [p Hp].
    simpl in *. apply state_eq_sub_state_eutt in H.
    eapply Hp; [symmetry|]; auto.
  - repeat red in H0. repeat red. intros. specialize (H0 s p). destruct p as [p Hp].
    simpl in *. apply state_eq_sub_state_eutt in H. eapply Hp; eauto.
Qed.

Global Instance state_eutt_iter {A B S: Type} {E : Type -> Type} :
  Proper (pointwise_relation A (@state_eq_eutt (A + B) S E ) ==>
                             pointwise_relation A (@state_eq_eutt B S E) ) (MonadIter_stateT0 B A).
Proof.
  repeat intro. red in H. red. red. unfold MonadIter_stateT0.
  apply eutt_iter. red. intros. destruct a0 as [s' a']. simpl. red in H.
  rewrite H. reflexivity.
Qed.

Global Instance state_eutt_bind_l {A B S : Type} {E : Type -> Type} :
  Proper ((@state_eq_eutt A S E) ==> pointwise_relation _ (@state_eq_eutt B S E)  ) bind.
Proof.
  unfold Proper, respectful, pointwise_relation. intros m0 m1 Heutt k.
  intro. cbn. red in Heutt. rewrite Heutt. reflexivity.
Qed.
(*we need a way to generate properness goals, this is fucking ridiculous*)
Global Instance state_eutt_bind_r {A B S : Type} {E : Type -> Type}
       {m : stateT S (itree E) A } :
  Proper ((pointwise_relation _ state_eq_eutt) ==>  (@state_eq_eutt B S E )  ) (bind m).
Proof.
  repeat intro. rename x into k0. rename y into k1. rename H into Heutt.
  red. red. red in Heutt. red in Heutt. cbn.
  eapply eutt_clo_bind; try reflexivity. intros. subst. destruct u2 as [s' a]. simpl.
  rewrite Heutt. reflexivity.
Qed.

Global Instance state_eutt_bind_l' {A B S : Type} {E : Type -> Type} :
  Proper ((@state_eq_eutt A S E) ==> pointwise_relation _ (@state_eq_eutt B S E) ==> state_eq_eutt  ) bind.
Proof.
  unfold Proper, respectful, pointwise_relation. intros m0 m1 Hmeutt k0 k1 Hkeutt.
  intro. cbn. red in Hmeutt. rewrite Hmeutt.
  eapply eutt_clo_bind; try reflexivity. intros. subst. destruct u2 as [s' a].
  simpl. red in Hkeutt. rewrite Hkeutt. reflexivity.
Qed.

Global Instance run_state_eutt_proper_eutt : forall (E : Type -> Type) (S R : Type) (s : S),
          Proper (@state_eq_eutt R S E  ==> eutt eq) (run_state_itree s).
Proof.
  repeat intro. red in H. unfold run_state_itree. rewrite H. reflexivity.
Qed.

Lemma lookup_nin : forall (x : var) (s : env), (forall v : value, ~ Maps.mapsto x v s) -> Maps.lookup x s = None.
Proof.
  intros. red in s. red in s. generalize dependent x. induction s; intros; auto.
  - cbn. destruct a as [y v]. destruct (Strings.String.string_dec x y).
    + subst. exfalso. apply (H v). red. cbn. red. cbn.
      rewrite RelDec.rel_dec_eq_true; auto. apply RelDec_string_Correct.
    + rewrite RelDec.rel_dec_neq_false; auto; try apply RelDec_string_Correct.
      unfold Maps.lookup in IHs. cbn in *. apply IHs; auto. intros.
      intro Hcontra. apply (H v0). red. cbn.
      rewrite RelDec.rel_dec_neq_false; auto; try apply RelDec_string_Correct.
Qed.


Lemma lookup_neq : forall (s : env) (x y: var) (v d: value), x <> y ->
                lookup_default x d (Maps.add y v s)  = lookup_default x d s.
Proof.

  intros.
  destruct (classic (exists v', Maps.mapsto x v' s)).
  - destruct H0 as [v' Hv'].
    assert (Maps.mapsto x v' (Maps.add y v s)).
    {
      eapply Maps.mapsto_add_neq in Hv'; eauto.
    }
    apply Maps.mapsto_lookup in H0. apply Maps.mapsto_lookup in Hv'. unfold lookup_default.
    rewrite Hv'. rewrite H0. auto.
  - assert (forall v',~ Maps.mapsto x v' s).
    { intros v' Hc. apply H0. exists v'. auto. }
    clear H0. apply lookup_nin in H1 as Hs. unfold lookup_default.
    rewrite Hs.
    assert (forall v', ~Maps.mapsto x v' (Maps.add y v s)).
    {
      intros v' Hcontra. apply Maps.mapsto_add_neq in Hcontra; auto.
      eapply H1; eauto.
    }
    apply lookup_nin in H0 as Hs'. rewrite Hs'. auto.
Qed.


Lemma lookup_eq : forall (s : env) (x : var) (v d : value),
    lookup_default x d (Maps.add x v s) = v.
Proof.
  intros. assert (Maps.mapsto x v (Maps.add x v s) ).
  { apply Maps.mapsto_add_eq; try reflexivity. }
  eapply Maps.mapsto_lookup in H. unfold lookup_default. rewrite H. auto.
Qed.

Definition assign_aexp (P : env -> Prop) (x : var) (a : aexp) : env -> Prop :=
  fun s => P (Maps.add x (compute_aexp a s) s).

Lemma hoare_assign : forall (P : env -> Prop) (x : var) (a : aexp),
    {{assign_aexp P x a}} x ::= a {{P}}.
Proof.
  intros. red. intros s s' Hassign Hret. unfold denote_imp in Hret.
  rewrite compute_assign_sc_tree in Hret. basic_solve. auto.
Qed.

Lemma hoare_consequence : forall (P0 P1 Q0 Q1: env -> Prop) (c : com),
    (forall s, P0 s -> P1 s) -> (forall s, Q0 s -> Q1 s) ->
    {{P1}} c {{Q0}} -> {{P0}} c {{Q1}}.
Proof.
  unfold hoare_triple. intros P0 P1 Q0 Q1 c HP HQ Hc s s' Hs Hcomp.
  apply HQ. eapply Hc; eauto.
Qed.

Section SQRTEx.

  Context (i n : var).
  Context ( Hneq : i <> n).

  Definition nat_sqrt : com :=
    i ::= 0;;;
    WHILE (~ (i * i = n) ) DO
       i ::= i + 1
    END.

  Local Open Scope nat_scope.
  Local Close Scope imp_scope.


  Definition is_square : nat -> Prop := fun (n : nat) => exists (m : nat), (m * m = n).

  Definition pre1 : env -> Prop := fun s => is_square (lookup_default n 0 s).
  Definition pre2 : env -> Prop := fun s => ~ is_square (lookup_default n 0 s).

  Definition post1 (s0 : env) (t : Delay (env * unit) ) : Prop :=
    exists s, t ≈ ret (s,tt) /\ (lookup_default i 0 s * lookup_default i 0 s) = lookup_default n 0 s0.

  Definition post2 : env -> Delay (env * unit) -> Prop := fun _ t => may_diverge t.

  Lemma burn_tree : forall (E : Type -> Type) (R : Type) (n : nat) (t : itree E R),
      t ≈ burn n t.
  Proof.
    intros. symmetry. generalize dependent t. induction n0; intros; try reflexivity.
    simpl. destruct (observe t) eqn : Heq.
    - specialize (itree_eta t) as Ht. rewrite Heq in Ht. rewrite Ht. reflexivity.
    - specialize (itree_eta t) as Ht. rewrite Heq in Ht. rewrite Ht.
      rewrite tau_eutt. auto.
    - specialize (itree_eta t) as Ht. rewrite Heq in Ht. rewrite Ht. reflexivity.
  Qed.
(*
  Global Instance proper_state_eq_eutt_iter {S Type: } :
    Proper (state_eq_eutt ==> pointwise_relation _ (state_eq_eutt) )
           (fun body)
*)


  Lemma compile_nat_sqrt_body :
    state_eq_eutt (denote_imp (WHILE (~ i * i  = n) DO i ::= i + 1 END)%imp)
                              (MonadIter_stateT0 _ _  (fun (_ :unit) (s : env) =>
                                                         if (compute_bexp (~ i * i = n) s)
                                                         then Ret (inc_var i s, inl tt)
                                                         else Ret (s, inr tt) ) tt ) .
  Proof.
    rewrite compile_while. apply state_eutt_iter. intro.
    rewrite compute_bexp_sc. intro. simpl. rewrite bind_ret_l. simpl.
    destruct (lookup_default i 0 s * lookup_default i 0 s =? lookup_default n 0 s); simpl.
    - tau_steps. reflexivity.
    - unfold denote_imp. rewrite compute_assign_sc_tree. rewrite bind_ret_l.
      cbn. tau_steps. rewrite Nat.add_comm. reflexivity.
  Qed.

  Let body_arrow (s : env) : Delay (env * (unit + unit) ) :=
    if (compute_bexp (~ i * i = n) s )
    then Ret (inc_var i s, inl tt)
    else Ret (s, inr tt).

  (*this may force me to come up with good wf_from conditions*)

  Ltac eqbdestruct a b := destruct (a =? b) eqn :?Heq;
                          match type of Heq with
                            | _ = true => apply Nat.eqb_eq in Heq
                            | _ = false => apply Nat.eqb_neq in Heq end.


  Lemma diverge_if_not_square_nat_sqrt_aux : forall (s : env),
      ~ is_square (lookup_default n 0 s) ->
      not_wf_from (fun s0 s1 => Ret (s1, inl tt) ≈ body_arrow s0 ) s.
  Proof.
    intros s Hn.
    set (lookup_default n 0 s) as n0.
    assert (forall m, m * m <> n0 ).
    {
      intros m Hcontra. unfold n0 in Hcontra. apply Hn. exists m. auto.
    }
    eapply intro_not_wf with (P := fun s => lookup_default n 0 s = n0) (f := fun s => inc_var i s); auto.
    - intros s0 s1 Hinv Heval. unfold body_arrow in Heval. simpl in Heval.
      rewrite Hinv in Heval. eqbdestruct (lookup_default i 0 s0 * lookup_default i 0 s0) n0.
      + simpl in *. basic_solve. pinversion Heval; discriminate.
      + simpl in Heval. basic_solve. pinversion Heval. injection REL; intros; subst. unfold inc_var. rewrite lookup_neq; auto.
    - intros s' Hinv. unfold body_arrow. simpl. rewrite Hinv.
      eqbdestruct (lookup_default i 0 s' * lookup_default i 0 s') n0; simpl.
      + exfalso. eapply H; apply Heq.
      + reflexivity.
  Qed.

  Lemma converge_if_square_nat_sqrt_aux : forall (s : env),
      lookup_default i 0 s = 0 ->
      is_square (lookup_default n 0 s) ->
      wf_from (fun s0 s1 => Ret (s1, inl tt) ≈ body_arrow s0 ) s.
  Proof.
    intros s Hi H. intros. unfold is_square in H. destruct H as [sqrt Hsqrt].
    set (fun s' : env => lookup_default i 0 s' <= sqrt /\
                         lookup_default n 0 s = lookup_default n 0 s') as inv.
    set (fun s : env => sqrt - lookup_default i 0 s)  as f.
    apply wf_intro_gt with (f := f) (P := inv); unfold inv; unfold f.
    - intros s1 s2 Hs1 Heutt.
      unfold body_arrow in Heutt. simpl in Heutt.
      destruct Hs1 as [Hsqrt1 Hconst].
      eqbdestruct (lookup_default i 0 s1 * lookup_default i 0 s1) (lookup_default n 0 s1);
        simpl in *; basic_solve; pinversion Heutt; try discriminate; injection REL; intros; subst.
      split.
      + unfold inc_var. rewrite lookup_eq.
        nia.
      + unfold inc_var. rewrite lookup_neq; auto.
    - intros s1 s2 Hs1 Heutt. unfold body_arrow in Heutt. simpl in *.
      eqbdestruct (lookup_default i 0 s1 * lookup_default i 0 s1) (lookup_default n 0 s1); simpl in *;
        pinversion Heutt; try discriminate; injection REL; intros; subst.
        unfold inc_var. rewrite lookup_eq. nia.
    - split; nia.
 Qed.

      (*Global Instance state_eq_eutt_eutt : Proper (state_eq_eutt ==> (pointwise_relation _ (eutt eq) ) ) (pointwise_relation _ (eutt eq) ). *)


  Lemma diverge_if_not_square_nat_sqrt : forall (s : env),
      ~ is_square (lookup_default n 0 s) ->
      may_diverge ( (denote_imp (WHILE (~ i * i  = n) DO i ::= i + 1 END)%imp) s).
    Proof.
      intros.
      enough (denote_imp (WHILE ~ i * i = n DO i ::= i + 1 END)%imp s ≈ ITree.spin).
      {
         rewrite H0. apply spin_diverge.
      }
      match goal with |- ?m s ≈ ITree.spin => fold (run_state_itree s m) end.
      rewrite compile_nat_sqrt_body. unfold run_state_itree.
      apply iter_inl_spin_state.
      apply ( diverge_if_not_square_nat_sqrt_aux) in H. unfold state_iter_arrow_rel.
      simpl. unfold body_arrow in H. simpl in *. generalize dependent s. pcofix CIH. intros.
      pinversion H0; try apply not_wf_F_mono'.
      pfold. eapply not_wf with (a' := (a',tt)).
      - symmetry. auto.
      - right. auto.
    Qed.

    (*maybe there is a better way to do it, prove that if the body can't prove a a spin,
      and it is wf then
      start working on that
     *)

  Lemma converge_if_square_nat_sqrt : forall (s : env),
        lookup_default i 0 s = 0 ->
        is_square (lookup_default n 0 s) ->
        exists s', (denote_imp (WHILE ~ i * i = n DO i ::= i + 1 END)%imp s ≈ Ret (s',tt) ).
  Proof.
    intros s Hi0 Hn. specialize (converge_if_square_nat_sqrt_aux s Hi0 Hn) as Hwf.
    eenough (exists s', _ ≈ Ret (s',tt) ).
    {
      destruct H as [s' H] . exists s'.
      match goal with |- (?m s ≈ _)%monad => fold (run_state_itree s m) end.
      rewrite compile_nat_sqrt_body. unfold run_state_itree. apply H.
    }
    specialize (iter_wf_converge_state unit unit env (fun _ : unit => body_arrow) ) as Hconv.
    specialize (Hconv tt s).
    enough ( exists p : env * unit,
            MonadIter_stateT0 unit unit (fun _ : unit => body_arrow) tt s
            ≈ Ret p).
    { destruct H as [ [s' [] ] H ]. eauto. }
    apply Hconv.
    - intros. unfold body_arrow. simpl.
      eqbdestruct (lookup_default i 0 s0 * lookup_default i 0 s0) (lookup_default n 0 s0); simpl.
      + exists (s0, inr tt). reflexivity.
      + exists (inc_var i s0, inl tt). reflexivity.
    - clear Hconv. clear Hi0. clear Hn. induction Hwf.
      + apply base. intros [s' [] ] ? . apply (H s').
        unfold state_iter_arrow_rel in H0. symmetry. auto.
      + apply step. intros [ s' [] ] ?. eapply H0. unfold state_iter_arrow_rel in H1. symmetry. auto.
  Qed.


  Lemma prepost1_holds_nat_sqrt_loop :
    verify_cond env (encode_dyn env ((pre1 /1\ fun s => lookup_default i 0 s = 0), post1) )
                (denote_imp (WHILE (~ i * i  = n) DO i ::= i + 1 END)%imp ).
  Proof.
    rewrite compile_nat_sqrt_body.
    repeat red. simpl. intros. destruct H. apply H0. clear H0. destruct H as [Hpre Hi0].
    assert (Hpost1 : forall s, resp_eutt (post1 s)).
    {
      unfold post1. repeat intro. split; basic_solve.
      - exists s1. split; auto. rewrite <- H. auto.
      - exists s1. rewrite H. split; auto.
    }
    unfold pre1 in Hpre.

    clear p.
    set (lookup_default n 0 s) as n0.
    set (fun x s => lookup_default x 0 s)  as get.
    set (fun (t : Delay ((env * unit) + (env * unit)) ) => exists s0,
    ((t ≈ ret (inl (s0,tt)) /\ get i s0 * get i s0 <= n0  ) \/ (t ≈ ret (inr (s0,tt)) /\ get i s0 * get i s0 = n0)) /\ get n s0 = n0 ) as q .
    set (fun (t : Delay (env * unit)) => exists s0, t ≈ ret (s0,tt) /\ get i s0 * get i s0 = n0 ) as p.
    match goal with |- post1 s ?t => enough (p t); auto end.
    assert (Hq : resp_eutt q).
    {
      + unfold q. repeat intro. split; intros; basic_solve; auto.
        * exists s0. split; auto. left. rewrite <- H. auto.
        * exists s0. split; auto. right. rewrite <- H. auto.
        * exists s0. split; auto. left. rewrite H. auto.
        * exists s0. split; auto. right. rewrite H. auto.
    }
    match goal with |- p ?t => enough ((p \1/ may_diverge) t)  end.
    - destruct H; auto. exfalso.
      specialize (converge_if_square_nat_sqrt s Hi0 Hpre) as Hconv.
      basic_solve.
      match type of Hconv with ?m s ≈ _ => fold (run_state_itree s m) in Hconv end.
      rewrite compile_nat_sqrt_body in Hconv. unfold run_state_itree in Hconv. rewrite Hconv in H.
      pinversion H.
    - eapply loop_invar_state with (q := q); eauto.
      (*Establishment*)
      + unfold reassoc. simpl. rewrite Hi0. simpl.
        destruct (lookup_default n 0 s) eqn : Heq; simpl.
        * eapply Hq.
          -- rewrite bind_ret_l. reflexivity.
          -- red. exists s. split; auto. right. unfold get. split; try reflexivity. unfold n0.
             (*wierd, so it seems to have something to do with different type aliasing for env*)
             unfold env in Hi0. rewrite Hi0. auto.
        * eapply Hq.
          -- rewrite bind_ret_l. reflexivity.
          -- red. exists (inc_var i s). split; auto.
             ++ left. split; try reflexivity. unfold get, inc_var.
                rewrite lookup_eq. unfold is_square in Hpre. basic_solve. nia.
             ++ unfold get, inc_var. rewrite lookup_neq; auto.
      (*Post Condition*)
      + red. cbn. intros. red. red in H. basic_solve.
        * exists s0. destruct (eutt_reta_or_div t); basic_solve.
          -- destruct a as [ s' [] ]. rewrite <- H2 in H. simpl in *. rewrite bind_ret_l in H.
             basic_solve.
          -- apply div_spin_eutt in H2. rewrite H2 in H.
             rewrite <- spin_bind in H. exfalso. symmetry in H. eapply not_ret_eutt_spin; try apply H.
        * exists s0. destruct (eutt_reta_or_div t); basic_solve.
          -- destruct a as [ s' []  ]. symmetry in H2. rewrite H2 in H.
             simpl in *. rewrite H1. rewrite bind_ret_l in H. basic_solve. auto.
          -- apply div_spin_eutt in H2. rewrite H2 in H. rewrite <- spin_bind in H.
             exfalso. symmetry in H. eapply not_ret_eutt_spin; try apply H.
       (*Preservation*)
      + intros. simpl. red in H. basic_solve.
        * eapply Hq.
          -- rewrite H. simpl. rewrite bind_ret_l. unfold DelaySpecMonad.iter_lift, iso_destatify_arrow, reassoc.
             simpl. reflexivity.
          -- eqbdestruct (lookup_default i 0 s0 * lookup_default i 0 s0) (lookup_default n 0 s0).
             ++ simpl. red. exists s0. setoid_rewrite Heq.
                rewrite Nat.eqb_refl.
                cbn. rewrite bind_ret_l. split; auto. right. unfold get, n0.
                split; try reflexivity.
                unfold env in Heq.  rewrite Heq. auto.
             ++ simpl. red. exists (inc_var i s0).  apply Nat.eqb_neq in Heq as Heq'. setoid_rewrite Heq'. simpl. rewrite bind_ret_l. split; auto.
                ** left. split; try reflexivity. unfold get, inc_var. rewrite lookup_eq.
                   unfold get in H1. red in Hpre. basic_solve. unfold get in H0. unfold n0 in *.
                   rewrite <- Hpre. rewrite <- H0 in H1. rewrite <- Hpre in H0. unfold env in *.  rewrite H0 in Heq.
                   assert (lookup_default i 0 s0 < m); nia.
                ** unfold get, inc_var. rewrite lookup_neq; auto.
         * eapply Hq.
           -- rewrite H. simpl. rewrite bind_ret_l. cbn. reflexivity.
           -- red. exists s0. split; auto. right. split; auto. reflexivity.
  Qed.


  Lemma prepost1_holds_nat_sqrt : verify_cond env (encode_dyn env (pre1,post1) ) (denote_imp nat_sqrt).
  Proof.
    unfold nat_sqrt.  rewrite denote_imp_bind.
    setoid_rewrite compile_nat_sqrt_body.
    setoid_rewrite compute_assign_sc. repeat red. intros s [p Hp]. intros. simpl in H.
    destruct H as [Hpre H]. apply H. clear H.
    assert (Hpost: forall s, resp_eutt (post1 s)).
    {
      repeat intro. unfold post1. split; intros; basic_solve.
      - exists s1. split; auto. rewrite <- H. auto.
      - exists s1. rewrite H. split; auto.
    }
    eapply Hpost.
    - Opaque Maps.add. simpl. rewrite bind_ret_l. simpl. reflexivity.
    - match goal with |- post1 s ?m => enough (post1 (Maps.add i 0 s) m) end.
      { unfold post1. unfold post1 in H. rewrite lookup_neq in H; auto. }
      specialize prepost1_holds_nat_sqrt_loop as Hloop.
      rewrite compile_nat_sqrt_body in Hloop. repeat red in Hloop.
      match goal with |- post1 ?s _ => set s as s1 end.
      simpl in Hloop. specialize (Hloop s1 (exist _ (post1 s1) (Hpost s1)) ).
      simpl in *. eapply Hloop. split; try split; intros.
      + unfold pre1, s1. rewrite lookup_neq; auto.
      + unfold s1. rewrite lookup_eq. auto.
      + red. red in H. basic_solve. unfold s1 in H0. exists s0. split; auto.
   Qed.

  Lemma prepost2_holds_nat_sqrt : verify_cond env (encode_dyn env (pre2,post2) ) (denote_imp nat_sqrt).
  Proof.
    unfold nat_sqrt. rewrite denote_imp_bind.
    setoid_rewrite compile_nat_sqrt_body.
    setoid_rewrite compute_assign_sc. repeat red. intros s [p Hp]. intros. simpl in H.
    destruct H as [Hpre H]. apply H. clear H. red in Hpre.
    simpl. red. rewrite bind_ret_l. simpl.
    assert (Hs' : ~ is_square (lookup_default n 0 (Maps.add i 0 s)) ).
    { rewrite lookup_neq; auto. } clear Hpre.
    apply diverge_if_not_square_nat_sqrt in Hs' as Hdivs.
    specialize compile_nat_sqrt_body as Hcomp. red in Hcomp. rewrite <- Hcomp.
    auto.
  Qed.

  Lemma both_hold_nat_sqrt : verify_cond env
                      (encode_list_dyn env (  (pre1, post1) :: (pre2,post2) :: nil ) ) (denote_imp nat_sqrt).
  Proof.
     repeat red. cbn. intros. inversion H; subst.
     - apply prepost1_holds_nat_sqrt. auto.
     - inversion H1; subst; try inversion H2.
       apply prepost2_holds_nat_sqrt. auto.
  Qed.

End SQRTEx.
