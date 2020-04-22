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
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(*need to add taus and eutt to streams*)
(*or maybe paly around with steve's encoding this with itrees idea*)
(*make a dummy version for the paper*)
Variant streamF {A : Type} {F : Type} : Type :=
  | NilF 
  | ConsF (h : A) (t : F).

CoInductive stream (A : Type) : Type := go {_observe : @streamF A (stream A) } .

Notation stream' A := (@streamF A (stream A)).

Definition Nil {A} : stream A:=
  {| _observe := NilF |}.

Definition Cons {A} (h : A) (t : stream A) := {| _observe := ConsF h t |}.

Definition observe_stream {A} : stream A -> stream' A := @_observe A.

Variant is_infF {A : Type}  (F : stream A -> Prop) : stream' A -> Prop :=
  is_inf_cons (h : A) (t : stream A) : F t -> is_infF F (ConsF h t).

Hint Constructors is_infF.

Definition is_inf_ {A : Type} (F : stream A -> Prop) : stream A -> Prop :=
  fun s => is_infF F (observe_stream s).

Definition is_inf {A : Type} := paco1 (@is_inf_ A) bot1.

Lemma is_inf_monot {A} : monotone1 (@is_inf_ A).
Proof.
  red. intros. red in IN. red. induction IN; auto.
Qed.
  
Hint Resolve is_inf_monot : paco.


CoFixpoint app' {A : Type} (osl: stream' A) (sr : stream A) : stream A :=
  match osl with
  | NilF => sr
  | ConsF h t => Cons h (app' (observe_stream t) sr) 
  end.

Definition app {A : Type} (sl : stream A) : stream A -> stream A :=
  app' (observe_stream sl).

Variant bisimF {A : Type} (F : stream A -> stream A -> Prop) : stream' A -> stream' A -> Prop :=
  | bisimNil : bisimF F NilF NilF
  | bisimConsF (h : A) (s1 s2 : stream A) : F s1 s2 -> bisimF F (ConsF h s1) (ConsF h s2).

Hint Constructors bisimF.

Definition bisim_ {A : Type} (F : stream A -> stream A -> Prop) : stream A -> stream A -> Prop :=
  fun s1 s2 => bisimF F (observe_stream s1) (observe_stream s2).

Definition bisim {A : Type} := paco2 (@bisim_ A) bot2.

Lemma bisim_monot {A} : monotone2 (@bisim_ A).
Proof.
  red. intros. red in IN. red. induction IN; auto.
Qed.

Hint Resolve bisim_monot : paco.

Instance bisim_equiv {A} : Equivalence (@bisim A).
Proof.
  constructor; red.
  - pcofix CIH. intros. pfold. red. destruct (observe_stream x); auto.
  - pcofix CIH. intros.
    pfold. red.
    pinversion H0; subst; auto.
  - pcofix CIH. intros. pfold. red.
    pinversion H0; pinversion H1; auto.
    + rewrite <- H in H3. discriminate.
    + rewrite <- H2 in H5. discriminate.
    + rewrite <- H2 in H4. injection H4; intros; subst.
      constructor. right. eauto.
Qed.

Instance proper_bisim_app {A} : Proper (@bisim A ==> bisim ==> bisim) app.
Proof.
  repeat red. pcofix CIH.  intros s1 s2 H12 s3 s4 H34.
  pfold. red. unfold app. pinversion H12.
  - simpl. destruct s3. destruct s4. pinversion H34; simpl in *; subst; auto.
    constructor. left. eapply paco2_mon; eauto. intuition.
  - cbn. constructor. right. apply CIH; auto.
Qed.

Instance proper_bisim_inf_imp {A} : Proper (@bisim A ==> impl) is_inf.
Proof.
  repeat red. pcofix CIH.
  intros s1 s2 H12 H. pfold. red. punfold H. red in H.
  punfold H12. red in H12. inversion H12; subst; auto.
  - rewrite <- H1 in H. inversion H.
  - inversion H. subst. pclearbot. destruct H2; intuition. constructor. right. eapply CIH; eauto.
    rewrite <- H3 in H0. injection H0 as H0 . subst. auto.
Qed.

Instance proper_bisim_inf {A} : Proper (@bisim A ==> iff) (is_inf).
Proof.
  split; try apply proper_bisim_inf_imp; auto.
  apply bisim_equiv. auto.
Qed.

Lemma app_inf : forall (A : Type) (s1 s2 : stream A), is_inf s1 -> bisim (app s1 s2) s1.
Proof.
  intros A. pcofix CIH. intros s1 s2 Hinf. pfold. unfold app.
  pinversion Hinf.
  red. cbn. rewrite <- H. constructor. right. apply CIH; auto.
Qed. 

Variant forall_streamF {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream' A -> Prop :=
  | forall_nil : forall_streamF P F NilF
  | forall_cons (h : A) (t : stream A) : P h -> F t -> forall_streamF P F (ConsF h t).

Hint Constructors forall_streamF.

Definition forall_stream_ {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream A -> Prop :=
  fun s => forall_streamF P F (observe_stream s).

Lemma forall_stream_monot (A : Type) (P : A -> Prop) : monotone1 (forall_stream_ P).
Proof.
  red. intros. red. red in IN. destruct IN; auto.
Qed.

Hint Resolve forall_stream_monot : paco.

Definition forall_stream {A : Type} (P : A -> Prop) := paco1 (forall_stream_ P) bot1.
  
Inductive inf_manyF {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream' A -> Prop :=
| cons_search (h : A) (t : stream A) : inf_manyF P F (observe_stream t) -> inf_manyF P F (ConsF h t)
| cons_found (h : A) (t : stream A) : P h -> F t -> inf_manyF P F (ConsF h t)
.

Hint Constructors inf_manyF.

Definition inf_many_ {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream A -> Prop :=
  fun s => inf_manyF P F (observe_stream s).

Lemma inf_many_monot (A : Type) (P : A -> Prop) : monotone1 (inf_many_ P).
Proof.
  red. intros. red in IN. red. induction IN; auto.
Qed.

Hint Resolve inf_many_monot : paco.

Definition inf_many {A : Type} (P : A -> Prop) := paco1 (inf_many_ P) bot1.

Lemma inf_many_inf : forall (A : Type) (P : A -> Prop) (s : stream A),
    inf_many P s -> is_inf s.
Proof.
  intros A P. pcofix CIH. intros s Him.
  punfold Him. red in Him. pfold. red.
  induction Him; auto. pclearbot.
  auto.
Qed.

Lemma inf_and_forall : forall (A : Type) (P : A -> Prop) (s : stream A),
    is_inf s -> forall_stream P s -> inf_many P s.
Proof.
  intros A P. pcofix CIH. intros s Hinf Hforall.
  pfold. red. punfold Hinf. red in Hinf. punfold Hforall.
  red in Hforall. inversion Hinf.
  inversion Hforall.
  - rewrite <- H in H2. discriminate.
  - pclearbot. rewrite <- H in H1. injection H1 as H1. subst.
    apply cons_found; auto.
Qed.

Lemma bisim_nil : forall (A : Type) (s : stream A),
    observe_stream s = NilF -> bisim s Nil.
Proof.
  intros. pfold. red. rewrite H. cbn. auto.
Qed.

Lemma app_nil : forall (A : Type) (s : stream A),
    bisim (app Nil s) s.
Proof.
  intros A. pcofix CIH. intros. pfold. red. unfold app. cbn.
  simpl. destruct s. simpl. destruct _observe0; auto.
  constructor. left. apply paco2_mon with (r := bot2); intuition.
  fold (@bisim A). apply bisim_equiv.
Qed.

Lemma app_assoc : forall (A : Type) (s1 s2 s3 : stream A),
    bisim (app s1 (app s2 s3)) (app (app s1 s2) s3). 
Proof.
  intros A. pcofix CIH. intros.
  destruct (observe_stream s1) eqn : Heq.
  - eapply paco2_mon with (r := bot2); intuition.
    fold (@bisim A).
    apply bisim_nil in Heq. rewrite Heq.
    rewrite app_nil. rewrite app_nil.
    apply bisim_equiv.
  - pfold. unfold app. red. rewrite Heq. 
    cbn. constructor. right. apply CIH.
Qed.

(*(ibranch E A -> Prop) -> stream Ev -> Prop    *)

(*ibranch E A () *)
Variant ibranchF {E : Type -> Type} {R : Type} {F : Type} : Type :=
  | RetBF (r : R) : ibranchF
  | TauBF (b : F) : ibranchF
  | VisBF {A : Type} (ev : E A) (ans : A) (b : F) : ibranchF
.

CoInductive ibranch (E : Type -> Type) (R : Type) :=
  gob {_observeb : @ibranchF E R (ibranch E R) }.

Notation ibranch' E R := (@ibranchF E R (ibranch E R) ).

Definition observe_branch {E R} (b : ibranch E R) : ibranch' E R :=
  _observeb E R b.

Definition RetB {E R} (r : R) : ibranch E R := {| _observeb := RetBF r |}.

Definition TauB {E R} (b : ibranch E R) : ibranch E R := {| _observeb := TauBF b |}.

Definition VisB {E R A} (ev : E A) (ans : A) (b : ibranch E R) := 
  {| _observeb := VisBF ev ans b|}.

CoFixpoint bind_branch' {E R U} (ob : ibranch' E R) (k : R -> ibranch E U) : ibranch E U :=
  match ob with
  | RetBF r => k r
  | TauBF b => TauB (bind_branch' (observe_branch b) k)
  | VisBF ev ans b => VisB ev ans (bind_branch' (observe_branch b) k) 
  end.  

Definition bind_branch {E R U} (b : ibranch E R) (k : R -> ibranch E U) :=
  bind_branch' (observe_branch b) k.


Instance MonadIbranch {E} : Monad (ibranch E) :=
  {
    ret A := @RetB E A;
    bind A B := @bind_branch E A B
  }.

Definition promote_event (E : Type -> Type) : Type -> Type :=
  fun A => ((E A) * A)%type.

CoFixpoint promote_branch' {E R} (ob : ibranch' E R) : itree (promote_event E) R :=
  match ob with
  | RetBF r => Ret r
  | TauBF b => Tau (promote_branch' (observe_branch b))
  | VisBF ev ans b => Vis (ev,ans) (fun a => promote_branch' (observe_branch b) ) 
  end. 

Definition promote_branch {E R} (b : ibranch E R) :=
 promote_branch' (observe_branch b).

Inductive ibranch_euttF (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop) 
          (sim : ibranch E R1 -> ibranch E R2 -> Prop) : 
  ibranch' E R1 -> ibranch' E R2 -> Prop
          
  :=
  | EqBRet (r1 : R1) (r2 : R2) : RR r1 r2 -> ibranch_euttF E R1 R2 RR 
                                                           sim (RetBF r1) (RetBF r2)
  | EqVisBF (A : Type) (ev : E A) (ans : A) (b1 : ibranch E R1) (b2 : ibranch E R2) : 
      sim b1 b2 -> ibranch_euttF E R1 R2 RR sim (VisBF ev ans b1) (VisBF ev ans b2)
  | EqTauBF (b1 : ibranch E R1) (b2 : ibranch E R2) :
      sim b1 b2 -> ibranch_euttF E R1 R2 RR sim (TauBF b1) (TauBF b2)
  | EqTauBFL (b1 : ibranch E R1) (ob2 : ibranch' E R2) : 
      ibranch_euttF E R1 R2 RR sim (observe_branch b1) ob2 ->
      ibranch_euttF E R1 R2 RR sim (TauBF b1) ob2
  | EqTauBFR (ob1 : ibranch' E R1) (b2 : ibranch E R2) : 
      ibranch_euttF E R1 R2 RR sim ob1 (observe_branch b2) ->
      ibranch_euttF E R1 R2 RR sim ob1 (TauBF b2)
.

Hint Constructors ibranch_euttF.

Definition ibranch_eutt_ (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
           (sim : ibranch E R1 -> ibranch E R2 -> Prop) : 
  ibranch E R1 -> ibranch E R2 -> Prop :=
  fun b1 b2 => ibranch_euttF E R1 R2 RR sim (observe_branch b1) (observe_branch b2).

Hint Unfold ibranch_eutt_.

Lemma ibranch_eutt_monot {E R1 R2 RR} : monotone2 (ibranch_eutt_ E R1 R2 RR).
Proof.
  red. intros. red in IN. red. induction IN; eauto.
Qed.

Hint Resolve ibranch_eutt_monot : paco.

Definition ibranch_eutt {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
           : ibranch E R1 -> ibranch E R2 -> Prop :=
  paco2 (ibranch_eutt_ E R1 R2 RR) bot2.

Lemma eutt_promotel : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
  (b1 : ibranch E R1) (b2 : ibranch E R2),
    eutt RR (promote_branch b1) (promote_branch b2) -> ibranch_eutt RR b1 b2.
Proof.
  intros E R1 R2 RR. pcofix CIH. intros.
  punfold H0. pfold. unfold_eqit. unfold promote_branch in H0. red. 
  dependent induction H0; subst.
  - destruct (observe_branch b1); destruct (observe_branch b2); try discriminate.
    cbn in *. injection x0 as x0. injection x as x. subst. auto.
  - destruct (observe_branch b1); destruct (observe_branch b2); try discriminate.
    cbn in *. injection x0 as x0. injection x as x. subst. 
    apply EqTauBF. right. pclearbot. auto.
  - destruct (observe_branch b1); destruct (observe_branch b2); try discriminate.
    cbn in *. injection x0 as x0. injection x as x. subst.
    apply inj_pair2 in H. apply inj_pair2 in H0.
    apply inj_pair2 in H1. apply inj_pair2 in H2. subst. injection H1; intros; subst.
    constructor. right. apply CIH; auto. apply REL in ans0 as HREL'. 
    pclearbot. auto.
  - destruct (observe_branch b1); try discriminate. cbn in x.
    injection x as x. constructor. eapply IHeqitF; eauto. subst. auto.
  - destruct (observe_branch b2); try discriminate. cbn in x.
    injection x as x. constructor. eapply IHeqitF; eauto. subst. auto.
Qed.

Lemma eutt_promoter : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
  (b1 : ibranch E R1) (b2 : ibranch E R2),
    ibranch_eutt RR b1 b2 -> eutt RR (promote_branch b1) (promote_branch b2).
Proof.
  intros E R1 R2 RR. pcofix CIH. intros.
  punfold H0. red in H0. pfold. red. unfold promote_branch.
  induction H0; cbn; eauto.
  - constructor. intros. red. pclearbot. right. apply CIH; auto.
  - constructor. right. pclearbot. apply CIH; auto.
Qed.

Lemma eutt_promote : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
  (b1 : ibranch E R1) (b2 : ibranch E R2),
    eutt RR (promote_branch b1) (promote_branch b2) <-> ibranch_eutt RR b1 b2.
Proof.
  split; try apply eutt_promotel; try apply eutt_promoter.
Qed.
  
Instance ibranch_eutt_equiv {E R} : Equivalence (@ibranch_eutt E R R eq).
Proof.
  constructor; red.
  - intros. apply eutt_promote. reflexivity.
  - intros. apply eutt_promote. apply eutt_promote in H. symmetry.
    auto.
  - intros. apply eutt_promote. apply eutt_promote in H. apply eutt_promote in H0.
    rewrite H. auto.
Qed.

Instance ibranch_eutt_eqm {E} : EqM (ibranch E) := fun R => @ibranch_eutt E _ _ eq.

Lemma tau_eutt_ib : forall (E : Type -> Type) (R : Type) (b : ibranch E R),
    TauB b ≈ b.
Proof.
  intros E R b. pfold. constructor.
  destruct (observe_branch b); auto;
  constructor; left; apply ibranch_eutt_equiv.
Qed.

Instance ibranch_monad_laws {E} : MonadLaws (ibranch E).
Proof.
  constructor.
  - intros A B f a. pfold. red. cbn. unfold bind_branch. cbn.
    simpl. destruct (f a). cbn.
    destruct _observeb0; auto; constructor; left; apply ibranch_eutt_equiv.
  - intros A. pcofix CIH. intros b. pfold. red. cbn. unfold bind_branch.
    simpl. destruct (observe_branch b); cbn; auto.
    + constructor. right. apply CIH.
    + constructor. right. apply CIH.
  - intros A B C. intros b f g. generalize dependent b.
    pcofix CIH. intros. pfold. red. cbn. unfold bind_branch.
    destruct (observe_branch b); cbn; auto.
    + simpl. destruct (f r0). destruct _observeb0; simpl.
      * destruct (g r1). destruct _observeb0; auto; constructor;
                           left; eapply paco2_mon; try apply ibranch_eutt_equiv; intuition.
      * constructor. left. eapply paco2_mon; try apply ibranch_eutt_equiv; intuition.
      * constructor. left. eapply paco2_mon; try apply ibranch_eutt_equiv; intuition.
    + constructor. right. apply CIH.
    + constructor. right. apply CIH.
Qed.

Variant Ev (E : Type -> Type) : Type := 
  ev (A : Type ) (e : E A) (a : A).
  

CoFixpoint app_branch' {E R} (os : stream' (Ev E)) (b : ibranch E R) : ibranch E R:=
  match os with
  | NilF => b
  | ConsF (ev _ _ e a) t => 
    VisB e a (app_branch' (observe_stream t) b)
  end.

Definition app_branch {E R} (s : stream (Ev E)) (b : ibranch E R) := 
  app_branch' (observe_stream s) b.



Instance app_branch_eutt {E R} : Proper (@bisim (Ev E) ==> 
                                 @ibranch_eutt E R R eq ==> ibranch_eutt eq) app_branch.
Proof.
  repeat red. 
  pcofix CIH.
  intros s1 s2 Hs b1 b2 Hb.
  pfold. red. unfold app_branch. punfold Hs. red in Hs.
  destruct Hs.
  - simpl. punfold Hb. red in Hb.
    destruct b1; destruct b2; auto. cbn in Hb.
    induction Hb; eauto.
    + constructor. left. pclearbot. eapply paco2_mon; try apply H. intuition.
    + constructor. left. pclearbot. eapply paco2_mon; try apply H. intuition.
  - simpl. destruct h. cbn. constructor. right.
    pclearbot. eapply CIH; eauto.
Qed.

Lemma app_branch_nil : forall (E : Type -> Type) (R : Type) (b : ibranch E R),
    app_branch Nil b ≈ b.
Proof.
  intros. unfold app_branch. simpl. pfold.
  red. simpl. destruct b. destruct _observeb0; simpl in *; eauto.
  + constructor. left. apply paco2_mon with (r := bot2); try intuition.
    apply ibranch_eutt_equiv.
  + constructor. left. apply paco2_mon with (r := bot2); try intuition.
    apply ibranch_eutt_equiv.
Qed.

Lemma stream_nil_or_cons : forall (A : Type) (s : stream A),
    bisim s Nil \/ exists s', exists h, bisim s (Cons h s').
Proof.
  intros. destruct (observe_stream s) eqn : Heq.
  - left. pfold. red. rewrite Heq. constructor.
  - right. exists t. exists h. pfold. red. rewrite Heq. cbn. constructor.
    left. apply bisim_equiv.
Qed.



Lemma app_branch_assoc : forall (E : Type -> Type) (R : Type)
               (s1 s2 : stream (Ev E)) (b : ibranch E R),
    app_branch s1 (app_branch s2 b) ≈ app_branch (app s1 s2) b.
Proof.
  intros E R. pcofix CIH. intros.
  destruct (stream_nil_or_cons _ s1).
  - apply paco2_mon with (r := bot2); intuition. rewrite H.
    rewrite app_nil. rewrite app_branch_nil. apply ibranch_eutt_equiv.
  - destruct H as [s' [h Hcon ] ].
    pfold. red. unfold app_branch, app. pinversion Hcon. subst. 
    cbn. simpl. destruct h. simpl. constructor. right. apply CIH.
Qed.

Notation "s ++ b" := (app_branch s b).

(*  (ibranch E A -> Prop) -> stream Ev -> Prop *)

Variant divergesF {E R} (F : stream (Ev E) -> ibranch E R -> Prop) : stream' (Ev E) -> ibranch' E R -> Prop:=
   | divergesFTau (log : stream (Ev E)) (b : ibranch E R) : F log b -> divergesF F (observe_stream log) (TauBF b)
   | divergesFVis {A : Type} (log : stream (Ev E)) (b : ibranch E R) (e : E A) (ans : A) : F log b -> 
                                                    divergesF F (ConsF (ev E A e ans) log) (VisBF e ans b)
.
(*nvm I need to add taus to my stream, current tau law lets us relate spin to any event stream when you want it to be nil or spin*)
Hint Constructors divergesF.

Definition diverges_ {E R} (F : stream (Ev E) -> ibranch E R -> Prop) : stream (Ev E) -> ibranch E R -> Prop :=
  fun log b => divergesF F (observe_stream log) (observe_branch b).

Lemma diverges_monot {E R} : monotone2 (@diverges_ E R).
Proof.
  repeat red. intros. induction IN; eauto.
Qed.

Hint Resolve diverges_monot : paco.

Definition diverges {E R} : stream (Ev E) -> ibranch E R -> Prop :=
  paco2 (@diverges_ E R) bot2.

CoFixpoint spinb {E R} : ibranch E R := TauB spinb.

Inductive converge_ {E R} : R -> list (Ev E) ->  ibranch' E R -> Prop :=
  | convergeRet (r : R) : converge_ r [] (RetBF r)
  | convergeTau (b : ibranch E R) (r : R) (log : list (Ev E) ) : converge_ r (observe_branch b) -> converge_ r (TauBF b)
  | convergeVis {A : Type} (b : ibranch E R) (ev : E A) (ans : A) (r : R) : 
      converge_ r (observe_branch b) -> converge_ r (VisBF ev ans b)
.
Hint Constructors converge_.

Definition converge {E R} (r : R) (b : ibranch E R) := converge_ r (observe_branch b).

Lemma not_converge_imp_div : forall (E : Type -> Type) (R : Type) (b : ibranch E R),
    ~ (exists r, converge r b) -> diverges b.
Proof.
  intros E R. pcofix CIH. intros.
  pfold. red. unfold converge in H0. destruct (observe_branch b).
  - exfalso. apply H0. exists r0. auto.
  - constructor. right. apply CIH. intro Hcontra. apply H0. basic_solve.
    exists r0. auto.
  - constructor. right. apply CIH. intro Hcontra. apply H0. basic_solve.
    exists r0. auto.
Qed.

Lemma classic_ibranch : forall (E : Type -> Type) (R : Type) (b : ibranch E R),
    (exists r, converge r b) \/ diverges b.
Proof.
  intros. destruct (classic (exists r, converge r b) ); auto.
  right. apply not_converge_imp_div. auto.
Qed.

Lemma converge_uniq : forall (E : Type -> Type) (R : Type) (b : ibranch E R) (r1 r2 : R),
    converge r1 b -> converge r2 b -> r1 = r2.
Proof.
  intros. unfold converge in *. induction H; inversion H0; auto.
Qed.

(*need to extend converge to *)



Definition stream_to_branch {E R} (s : stream (Ev E) ) : ibranch E R :=
  app

(*need to be able to separate a branch into its return *)
Definition resp_euttb {E R} (p : ibranch E R -> Prop) : Prop :=
  forall b1 b2, b1 ≈ b2 -> p b1 -> p b2.

Notation "a ∈ b" := (proj1_sig b a) (at level 70). 

Notation "a ∋ b" := (proj1_sig a b) (at level 70).

Section TraceSpec.
  Context (E : Type -> Type).

  Definition TraceSpecInput (A : Type) := {p : ibranch E A -> Prop | resp_euttb p}.

  Definition TraceSpec (A : Type) := stream (Ev E) -> {w : TraceSpecInput A -> Prop | 
                                      forall (p p' : TraceSpecInput A), (forall b, b ∈ p -> b ∈ p') -> w p -> w p'  }.

  (*ignore history by default*)
  Program Definition ret_ts1 {A : Type} (a : A) : TraceSpec A := fun log p => p (RetB a).

  Program Definition bind_ts1 {A B : Type} (w : TraceSpec A) (g : A -> TraceSpec B) :=
    fun log p => w log (fun b => (exists a, exists log', converge a log' b /\ g a log' p) \/ (diverge b /\ p b) )(*need to convert p*)

  (*care about history by default*)
  Program Definition ret_ts2 {A : Type} (a : A) : TraceSpec A := fun s p => p (app_branch s (RetB a) ). 

  Definition TraceSpec' (A : Type) := (ibranch E A -> Prop) 
