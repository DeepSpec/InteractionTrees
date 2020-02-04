From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.FunctionalExtensionality
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
     Dijkstra.StateSpecT
   (*  Simple *)
.

Require Import Omega.
Require Import NArith.
Require Import Imp.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Import ImpNotations.
Local Open Scope imp_scope.
From Paco Require Import paco.


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
  is_bool Void true b s.

Definition is_false  (b : bexp) (s : env) : Prop :=
  is_bool Void false b s.

(*
Ltac unf_intep := unfold interp_imp, interp_map, interp_state, interp, Basics.iter, MonadIter_stateT0, interp, Basics.iter, MonadIter_stateT0.
*)

Lemma aexp_term : forall (E : Type -> Type) (ae : aexp) (s : env),
    exists (n : nat), @interp_imp Void _ (denote_aexp ae) s ≈ Ret (s,n).
Proof.
  intros. induction ae.
  - exists n. cbn. tau_steps. reflexivity.
    (*getvar case, extract to a lemma*)
  - cbn. exists (lookup_default x 0 s). 
    tau_steps. reflexivity.
  - basic_solve. exists (n0 + n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
  - basic_solve. exists (n0 - n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
  - basic_solve. exists (n0 * n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
Qed.
     
    
Lemma bools_term : forall (be : bexp) (s : env),
    exists (bc : bool), @interp_imp Void _ (denote_bexp be) s ≈ Ret (s,bc).
Proof.
  intros. induction be.
  - exists true. cbn. unfold interp_imp, interp_map, interp_state. repeat rewrite interp_ret. 
    tau_steps. reflexivity.
  - exists false. tau_steps. reflexivity.
  - specialize (aexp_term Void a1 s) as Ha1. specialize (aexp_term Void a2 s) as Ha2.
    basic_solve. exists (n0 =? n).
    cbn. setoid_rewrite interp_imp_bind. rewrite Ha1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind.
    rewrite Ha2. tau_steps. reflexivity.
  - specialize (aexp_term Void a1 s) as Ha1. specialize (aexp_term Void a2 s) as Ha2.
    basic_solve. exists (n0 <=? n).
    cbn. setoid_rewrite interp_imp_bind. rewrite Ha1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind.
    rewrite Ha2. tau_steps. reflexivity.
  - basic_solve. exists (negb bc). cbn.
    setoid_rewrite interp_imp_bind. rewrite IHbe. tau_steps.
    reflexivity.
  - basic_solve. exists (bc0 && bc)%bool.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHbe1. setoid_rewrite bind_ret.
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
  destruct (eutt_reta_or_div _ (denote_imp c1 s) ); basic_solve.
  - destruct a as [s'' [] ]. rewrite <- H in Hs'. setoid_rewrite bind_ret in Hs'. symmetry in H.
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
    rewrite H. setoid_rewrite bind_ret. apply Hc1. auto.
  - unfold is_false, is_bool in H. rewrite interp_imp_bind.
    rewrite H. setoid_rewrite bind_ret. apply Hc2. auto.
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
  repeat intro. 
Admitted.

(*
Check (case_ (handle_map (V := value) pure_state ) ).

Timeout 5 Definition run_state_map {value A : Type} (t : itree (mapE var 0 +' Void)  A) s  : itree Void ( env * A):= 
  interp_state (case_ (handle_map (V := value) ) pure_state) t s.
*)

Section interp_state_eq_iter.
  Context {E F: Type -> Type}.
  Context (S : Type).
  Context (f : E ~> stateT S (itree F) ).
  Context (A B : Type).
  Context (g : A ->itree E (A + B) ).
  Context (a : A).
  

  Lemma interp_state_eq_iter : state_eq (interp_state f (KTree.iter g a) )
                              (MonadIter_stateT0 _ _ (fun a0 => interp_state f (g a0)) a).
  Proof.
    specialize @interp_state_iter with (E := E) as Hisi. unfold Basics.iter in Hisi.
    unfold KTree.iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
    eapply Hisi. reflexivity.
  Qed.

End interp_state_eq_iter.
Set Default Timeout 15.

Global Instance proper_state_eq_iter {S: Type} : 
  Proper (@state_eq Void S (unit + unit) ==> @state_eq Void S (unit) ) (fun body => @MonadIter_stateT0 Delay S _ _ unit unit (fun _ : unit => body) tt ). 
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
  intros. generalize dependent t2. generalize dependent t1.
  pcofix CIH. 
  intros. pinversion H1; eauto.
  - specialize (@itree_eta E U1 t1 ) as Hr1.
    rewrite <- H2 in Hr1.
    specialize (@itree_eta E U2 t2) as Hr2.
    rewrite <- H in Hr2.  pfold. red. Admitted.



Global Instance bind_state_eq2 {E : Type -> Type} {A B S : Type} {m : stateT S (itree E) A} : 
  Proper (@state_eq2 E A B S ==> @state_eq E S B) (bind m).
Proof.
  repeat intro. unfold state_eq2, state_eq in H. cbn.
  eapply eq_itree_clo_bind; try reflexivity. intros. subst.
  destruct u2 as [s' a]. simpl. rewrite H. reflexivity.
Qed.


Lemma compile_while : forall (b : bexp) (c : com), 
                             (denote_imp ( WHILE b DO c END )) ≈ MonadIter_stateT0 unit unit 
                                         (fun _ : unit => bind (interp_imp (denote_bexp b)) 
                                                               (fun b : bool => if b 
                                                                         then bind (denote_imp c) (fun _ : unit => interp_imp (Ret (inl tt)) )  
                                                                         else interp_imp (Ret (inr tt))) ) tt.
Proof.
  intros. simpl. unfold denote_imp. simpl. unfold while. unfold interp_imp at 1, interp_map at 1.
  cbn. red. red. intros. symmetry.
Abort.
Lemma hoare_while : forall (c : com) (b : bexp) (P : env -> Prop),
    {{fun s => is_true b s /\ P s}} c {{ P  }} ->
    {{ P }} WHILE b DO c END {{ fun s => is_false b s /\ P s}}.
Proof.
  unfold hoare_triple. intros. unfold denote_imp in H1. cbn in H1.
  unfold while in H1. unfold interp_imp, interp_map in H1.
  (*this moves interp inside the iter*)

  (* setoid_rewrite eutt_interp_state_iter in H1. *)
  rewrite interp_iter in H1.
  match goal with | H : ?m0 s ≈ _ |- _ => set m0 as m end.
  fold m in H1.
  assert (state_eq m m); try reflexivity.
  unfold m at 1 in H2.  rewrite interp_state_eq_iter in H2.
  fold (run_state_itree s m) in H1. symmetry in H2. 
  
  setoid_rewrite H2 in H1.
  
  match goal with | H : run_state_itree s (_ _ _ (fun _ => ?e) tt) ≈ _  |- _ => set e as body end.
  assert (state_eq body body); try reflexivity.
  
  unfold body in H3 at 2.
  setoid_rewrite interp_bind in H3.
  fold body in H1. setoid_rewrite interp_state_bind_state in H3.
  

  match type of H3 with state_eq _ (bind (?h0 (?h1 ?bexp) ) 
                                         (fun be => ?h2 (?h3 (
                                   if _ 
                                   then ?l else ?r) ))) => set h0 as hsb; set h1 as hib; fold hsb in H3; fold hib in H3; 
                                                             set h2 as hsu; set h3 as hiu; fold hsu in H3; fold hiu in H3  end.
  assert (Hse : state_eq2 
                  (fun b: bool => hsu (hiu (if b 
                                            then ITree.bind (denote_com c) (fun _ : unit => Ret (inl tt)) 
                                            else Ret (inr tt))))
                  (fun b : bool => if b 
                                   then bind (interp_imp (denote_com c) )  (fun _ : unit => interp_imp (Ret (inl tt)) ) 
                                   else interp_imp (Ret (inr tt) ) ) 
 ).
  {
    intro b0. destruct b0; try reflexivity. unfold hsu, hiu. setoid_rewrite interp_bind. unfold interp_imp, interp_map. intro.
    setoid_rewrite interp_state_bind. unfold bind. simpl. reflexivity.
  }
  rewrite Hse in H3. clear Hse.

  (*once I fully push down interps in body I can rewrite in H1*)
  eapply proper_state_eq_iter in H3; eauto. rewrite H3 in H1. clear H3. 
  unfold run_state_itree in H1. unfold hsb, hib, hsu, hiu in H1.
  clear hsb hib hsu hiu. clear H2 body m. rename H1 into Heutt.
  rename H0 into Hres.
  specialize (loop_invar_state env unit unit) as Hloop. unfold State in Hloop.

  match type of Heutt with MonadIter_stateT0 unit unit ?g tt _ ≈ _ => set g as body end.

  split.
  - set (fun (t : Delay (env * unit) ) => 
           (exists s, t ≈ ret (s,tt) /\ is_false b s) \/ divergence t
        ) as p.
    set (fun (t : Delay (env * unit + env * unit)) =>
           (exists s, (t ≈ ret (inl (s,tt)) ) \/ ((t ≈ ret (inr (s,tt)) /\ is_false b s)) )  \/ divergence t
        ) as q.
    assert (resp_eutt _ _ p) as Hp.
    {
      unfold p. unfold is_false, is_bool.
      intros t1 t2 He. split; intro; basic_solve.
      - left. exists s0.  split; auto. rewrite <- He. auto.
      - rewrite He in H0. auto.
      - left. exists s0. split; auto. rewrite He. auto.
      - rewrite <- He in H0. auto.
    }
    assert (resp_eutt _ _ q) as Hq.
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
    enough ((p \1/ divergence) (CategoryOps.iter body tt s) ).
    {
      destruct H0; auto. unfold p. auto.
    }
    specialize Hloop with (s := s) (p := p) (q := q).
    eapply Hloop; eauto.
    + unfold reassoc. unfold body. 
      destruct (eutt_reta_or_div _ (interp_imp (denote_com c) s ) );
      destruct (classic_bool b s); basic_solve.
      *  do 4 red in H1. unfold interp_imp, interp_map in H1.
         destruct a as [s'' [] ]. 
         eapply Hq.
         -- cbn. setoid_rewrite bind_bind. rewrite H1.
            setoid_rewrite bind_ret. simpl.
            setoid_rewrite bind_bind. rewrite <- H0.
            tau_steps. reflexivity.
         -- unfold q. left. exists s''. left. reflexivity.
      * do 4 red in H1. unfold interp_imp, interp_map in H1.
        destruct a as [s'' [] ].
        eapply Hq.
        -- cbn. rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret.
           simpl. tau_steps. reflexivity.
        -- unfold q. left. exists s. right. split; auto. reflexivity.
      * do 4 red in H1. unfold interp_imp, interp_map in H1.
        eapply Hq.
        -- cbn. rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret.
           simpl. apply div_spin_eutt in H0. rewrite H0. setoid_rewrite bind_bind.
           rewrite <- spin_bind. reflexivity.
        -- red. right. apply spin_div.
      * do 4 red in H1. unfold interp_imp, interp_map in H1.
        eapply Hq.
        -- cbn. rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret.
           simpl. apply div_spin_eutt in H0. 
           tau_steps. reflexivity.
        -- red. left. exists s. right. split; auto; reflexivity.
   + unfold q,p. unfold DelaySpecMonad.loop_invar_imp. intros.
     basic_solve.
     * cbn in H0. exfalso. destruct (eutt_reta_or_div _ t); basic_solve.
       -- rewrite <- H1 in H0. setoid_rewrite bind_ret in H0. basic_solve.
       -- apply div_spin_eutt in H1. rewrite H1 in H0. rewrite <- spin_bind in H0.
          symmetry in H0. eapply not_ret_eutt_spin; eauto.
     * cbn in H0. destruct (eutt_reta_or_div _ t); basic_solve; auto.
       rewrite <- H2 in H0. setoid_rewrite bind_ret in H0. basic_solve. left.
       exists s0. split; auto. symmetry. auto.
     * right. destruct (eutt_reta_or_div _ t); basic_solve; auto.
       cbn in H0. rewrite <- H1 in H0. setoid_rewrite bind_ret in H0.
       pinversion H0.
  + unfold q. 
    (*I chose the wrong q*)

    unfold DelaySpecMonad.iter_lift, iso_destatify_arrow, reassoc. 
    basic_solve; try (destruct (classic_bool b s0) ); 
      try (destruct (eutt_reta_or_div _ (interp_imp (denote_com c) s0 ) )); basic_solve.
    * eapply Hq.
      -- cbn. rewrite H0. setoid_rewrite bind_ret.
         setoid_rewrite bind_bind. do 4 red in H1. unfold interp_imp, interp_map in H1.
         rewrite H1. setoid_rewrite bind_ret. simpl.
         destruct a as [s1 [] ]. rewrite <- H2. setoid_rewrite bind_bind.
         setoid_rewrite bind_ret. simpl. tau_steps. reflexivity.
      -- red. left. destruct a as [s'' [] ]. exists s''. left. reflexivity.
    * eapply Hq.
      -- cbn. rewrite H0. setoid_rewrite bind_ret. setoid_rewrite bind_bind.
         do 4 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
         setoid_rewrite bind_ret. simpl. apply div_spin_eutt in H2. rewrite H2.
         setoid_rewrite bind_bind. rewrite <- spin_bind. reflexivity.
      -- right. apply spin_div.
    * destruct a as [s'' [] ]. eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret.
         do 4 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
         setoid_rewrite bind_bind. setoid_rewrite bind_ret. simpl. tau_steps. reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret.
         do 4 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
         setoid_rewrite bind_bind. setoid_rewrite bind_ret. simpl. tau_steps. reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * do 4 red in H1. do 4 red in H2. rewrite H1 in H2.
      apply inv_ret in H2. injection H2. discriminate.
    * do 4 red in H1. do 4 red in H2. rewrite H1 in H2.
      apply inv_ret in H2. injection H2. discriminate.
    * eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret.  reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * eapply Hq.
      -- cbn.  rewrite H0. setoid_rewrite bind_ret.  reflexivity.
      -- left. exists s0. right. split; auto. reflexivity.
    * right. cbn. apply div_spin_eutt in H0. rewrite H0. rewrite <- spin_bind.
      apply spin_div.
   - set (fun (t : Delay (env * unit)) => 
           (exists s, t ≈ ret (s,tt) /\ P s ) \/ divergence t
        ) as p.
    set (fun (t : Delay (env * unit + env * unit)) => 
           (exists s, (t ≈ ret (inl (s,tt) ) \/ t ≈ ret (inr (s,tt) ) ) /\ P s )\/ divergence t )  as q.
    assert (resp_eutt _ _ p) as Hp.
    {
      unfold p. intros t1 t2 He. split; intros; basic_solve.
      - left. exists s0. rewrite He in H0. auto.
      - right. rewrite He in H0. auto.
      - left.  exists s0. rewrite <- He in H0. split; auto.
      - right. rewrite He. auto.
    }
      assert (resp_eutt _ _ q) as Hq.
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
      enough ((p \1/ divergence) (CategoryOps.iter body tt s ) ).
      { 
        destruct H0.
        - eapply Hp; try apply H0. rewrite <- Heutt. reflexivity.
        - unfold CategoryOps.iter, Iter_Kleisli, Basics.iter in H0.
          unfold body in H0. rewrite Heutt in H0. pinversion H0.
      }
      eapply Hloop; eauto.
      + unfold reassoc. unfold body. destruct (classic_bool b s).
        * assert (is_true b s /\ P s); auto. 
          destruct (eutt_reta_or_div _ (interp_imp (denote_com c) s) ); basic_solve.
          -- destruct a as [s'' [] ].
             unfold is_true, is_bool in H0. 
             unfold interp_imp, interp_map in H0.
             eapply Hq.
             ++ cbn. setoid_rewrite bind_bind. rewrite H0.
                setoid_rewrite bind_ret. simpl. setoid_rewrite bind_bind.
                rewrite <- H2. tau_steps.
                reflexivity.
             ++ specialize (H s s''). unfold q. left. exists s''. split; try (left; reflexivity).
                eapply H; eauto. symmetry. auto.
          -- apply div_spin_eutt in H2. eapply Hq with (t1 := spin).
             ++ cbn. unfold is_true, is_bool in H0. setoid_rewrite bind_bind.
                unfold interp_imp, interp_map in H0.  rewrite H0.
                setoid_rewrite bind_ret. simpl. rewrite H2.
                setoid_rewrite bind_bind. apply spin_bind.
             ++ unfold q. right. apply spin_div.
        * unfold is_false, is_bool, interp_imp, interp_map in H0. cbn.
          eapply Hq.
          -- setoid_rewrite bind_bind. rewrite H0. setoid_rewrite bind_ret.
             simpl. cbn. tau_steps. reflexivity.
          -- unfold q. left. exists s. split; auto. right. reflexivity.
      + red. intros. unfold p. unfold q in H0. basic_solve.
        * cbn in H0. 
          destruct (eutt_reta_or_div _ t); basic_solve.
          -- destruct a as [s'' [] ]. rewrite <- H2 in H0.
             setoid_rewrite bind_ret in H0. basic_solve.
          -- exfalso. apply div_spin_eutt in H2. rewrite H2 in H0. rewrite <- spin_bind in H0.
             symmetry in H0. apply not_ret_eutt_spin in H0. auto.
        * cbn in H0.
        destruct (eutt_reta_or_div _ t); basic_solve.
        -- destruct a as [s'' [] ]. rewrite <- H2 in H0.
           setoid_rewrite bind_ret in H0. basic_solve. left. exists s0. 
           symmetry in H2. auto.
        -- exfalso. apply div_spin_eutt in H2. rewrite H2 in H0.
           rewrite <- spin_bind in H0. symmetry in H0. apply not_ret_eutt_spin in H0. auto.
      * cbn in H0. right. destruct (eutt_reta_or_div _ t); auto.
        basic_solve. rewrite <- H1 in H0. setoid_rewrite bind_ret in H0.
        pinversion H0.
    + unfold DelaySpecMonad.iter_lift, iso_destatify_arrow, reassoc.
      intros t Ht. cbn.
      destruct (eutt_reta_or_div _ t); 
         basic_solve.
      * destruct a as [s'' [] ].
        destruct (classic_bool b s''); 
          destruct (eutt_reta_or_div _ (interp_imp (denote_com c) s'' )); basic_solve;
        eapply Hq.
        -- rewrite <- H0. setoid_rewrite bind_ret.
           setoid_rewrite bind_bind. do 4 red in H1. 
           unfold interp_imp, interp_map in H1. rewrite H1. setoid_rewrite bind_ret.
           simpl. setoid_rewrite bind_bind.
           rewrite <- H2. setoid_rewrite bind_ret. destruct a as [s3 [] ].
           simpl. tau_steps. reflexivity.
        -- destruct a as [s3 [] ]. unfold q in Ht. basic_solve.
           ++ rewrite  H3 in H0. basic_solve.
              unfold q. left. exists s3. split; try (left; reflexivity). symmetry in H2.
              eapply H; eauto.
           ++ rewrite H3 in H0. basic_solve.
           ++ rewrite <- H0 in H3. pinversion H3.
        -- rewrite <- H0. setoid_rewrite bind_ret. setoid_rewrite bind_bind.
           do 4 red in H1. unfold interp_imp, interp_map in H1. rewrite H1.
           setoid_rewrite bind_ret. simpl. apply div_spin_eutt in H2.
           setoid_rewrite bind_bind. rewrite H2.
           rewrite <- spin_bind. reflexivity.
        -- unfold q. right. apply spin_div.
        -- rewrite <- H0. setoid_rewrite bind_ret. 
           unfold is_false, is_bool in H1. unfold interp_imp, interp_map in H1.
           rewrite H1. setoid_rewrite bind_bind. setoid_rewrite bind_ret. simpl.
           tau_steps. reflexivity.
        -- unfold q. left. exists s''. split; try (right; reflexivity). unfold q in Ht.
           basic_solve.
           ++ rewrite H3 in H0. basic_solve. auto.
           ++ rewrite H3 in H0. basic_solve.
           ++ rewrite <- H0 in H3. pinversion H3.
        -- rewrite <- H0. setoid_rewrite bind_ret. 
           setoid_rewrite bind_bind.
           do 4 red in H1. unfold interp_imp, interp_map in H1.
           rewrite H1. setoid_rewrite bind_ret. simpl. tau_steps.
           reflexivity.
        -- unfold q. left. exists s''.
           split; try (right; reflexivity). unfold q in Ht.
           basic_solve.
           ++ rewrite H3 in H0. basic_solve. auto.
           ++ rewrite H3 in H0. basic_solve.
           ++ rewrite <- H0 in H3. pinversion H3.
     * destruct b0 as [s'' [] ]. eapply Hq.
       -- rewrite <- H0. setoid_rewrite bind_ret.
          reflexivity.
       -- unfold q. left. exists s''. split; try (right; reflexivity).
          unfold q in Ht. basic_solve.
          ++ rewrite H1 in H0. basic_solve.
          ++ rewrite H1 in H0. basic_solve. auto.
          ++ rewrite <- H0 in H1. pinversion H1.
     * clear Ht. unfold q. right. apply div_spin_eutt in H0.
       rewrite H0. rewrite <- spin_bind. apply spin_div.

Qed.       
