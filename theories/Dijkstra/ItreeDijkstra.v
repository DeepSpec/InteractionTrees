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
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(** The itree Tau (Tau (Tau ...))*)
CoFixpoint spin {E: Type -> Type} {A : Type}  : itree E A := Tau spin.

Lemma spin_div : forall E A, @divergence E A spin.
Proof.
  intros. pcofix CIH. pfold. unfold divergence_. 
  cbn. constructor. right. auto.
Qed.

(*this implies that if a spec w accepts spin, then bind w f should too?   *)
Lemma spin_bind : forall (E : Type -> Type) (A B : Type) (f : A -> itree E B), spin ≈ bind spin f.
Proof.
  intros. pcofix CIH. pfold. unfold bind. simpl. red.
  cbn. constructor. right. auto.
Qed.

Inductive Void : Type -> Type := .

(*Depreacated predicate on itree predicates. Intended to denote that a predicate is invariant wrt adding
  or subtracting a finite number of Tau's. Replaced with resp_eutt*)
Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).

(*Characterizes predicates that respect the eutt relation on itrees. Captures the notion that a predicate
  is invariant wrt adding or subtracting a finite number of Tau's*)
Definition resp_eutt (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
  forall (t1 t2 : itree E A), t1 ≈ t2 -> (P t1 <-> P t2).

Lemma tau_invar_resp_eutt1: forall (E : Type -> Type) (A : Type) (P : itree E A -> Prop),
                                 (forall t1 t2, t1 ≈ t2 ->(P t1 <-> P t2)) -> tau_invar E A P.
  Proof.
    intros. unfold tau_invar. split; intros;
    eapply H; try eassumption; rewrite tau_eutt; reflexivity.
  Qed.

(*Derives contradiction from evidence that a return tree is divergent*)
Ltac inv_div_ret := match goal with [ H : divergenceF _ (RetF _) |- _  ] => inversion H end.

(*Divergent trees never return a value*)
Lemma div_ret_eutt : forall (E : Type -> Type) (A : Type) (t: itree E A) (a : A),
      divergence t -> ~(t ≈ ret a).
  Proof.
    intros. intros HContra. rewrite HContra in H. pinversion H.
  Qed.  

(*Trees that return a value do not diverge*)
Lemma ret_eutt_div : forall (E : Type -> Type) (A : Type) (t : itree E A) (a : A),
      t ≈ ret a -> ~ (divergence t).
  Proof.
    intros. intros HContra. rewrite H in HContra. pinversion HContra.
  Qed.

(*spin is the only divergent itree with the Void event type,*)
Lemma div_spin_eutt : forall (A : Type) (t : itree Void A), divergence t -> t ≈ spin.
Proof.
  intros A. pcofix CIH. intros. pfold. red. cbn.
  destruct (observe t) eqn : Heqt.
  - specialize (itree_eta t) as H. rewrite Heqt in H. rewrite H in H0. pinversion H0.
  - constructor. right. apply CIH. specialize (itree_eta t) as H. rewrite Heqt in H.
    assert (t ≈ Tau t0).
    + rewrite H. reflexivity.
    + rewrite <- tau_eutt. rewrite <- H1. auto.
  - destruct e.
Qed.

(*Formalized notion of specification monads and effect observations for pure, possibly divergent, computations *)
Section PureITree.
  
  Definition PureITree A := itree Void A.

  (*Morally, this is the type of pure itree specifcations. A sigma of this with a monotonicity requiremnet is used
    in order to proved the ordered monad law*)
  Definition _PureITreeSpec A := forall (p : itree Void A -> Prop), (resp_eutt Void A p) -> Prop.



  (*Monotonicity condition for specs on pure itrees*)
  Definition monotonici A (w : _PureITreeSpec A) :=
    forall (p p' : itree Void A -> Prop) (Hp : resp_eutt Void A p) (Hp' : resp_eutt Void A p'),
                                          (forall i', p i' -> p' i') -> w p Hp -> w p' Hp'. 

  (*Sigm*)
  Definition PureITreeSpec A := {w : _PureITreeSpec A | monotonici A w}.

  (*The set of predicates that accept divergent trees*)
  Definition _div_spec A : _PureITreeSpec A := fun p _ => p spin.

  Lemma div_spec_monot : forall A, monotonici A (_div_spec A).
    Proof.
      unfold monotonici, _div_spec. auto.
    Qed.

  Definition div_spec A := exist _ (_div_spec A) (div_spec_monot A).

  (*Assortment of definitions and lemmas defining an inductive definition of the return value of a tree and relating
    it to tau_invar and divergence. I believe none of this code is particularly useful anymore*)
  Section IsVal.
  Inductive is_val A (a : A) : itree Void A -> Prop :=
    | base :  is_val A a (ITreeDefinition.Ret a)
    | tau (t : itree Void A): is_val A a t -> is_val A a (Tau t) .

  Lemma is_val_to_eutt : forall A (a : A) (t : itree Void A),
      is_val A a t -> ret a ≈ t.
  Proof.
    intros. induction H.
    - reflexivity.
    - rewrite tau_eutt. auto.
  Qed.

  Definition is_val_eutt A (a : A) (t : itree Void A) := t ≈ ret a.

  Lemma is_val_resp_eutt : forall A a, resp_eutt Void A (is_val_eutt A a).
    Proof.
      intros. intros t1 t2. unfold is_val_eutt. split; intros.
      - rewrite H in H0. auto.
      - rewrite H. auto.
    Qed.

  Lemma is_val_tau_invar : forall A (a : A), tau_invar Void A (is_val A a).
  Proof.
    intros. unfold tau_invar. split; intros.
    - constructor. auto.
    - inversion H. auto.
  Qed.

  Lemma eutt_reta_or_spin_aux : forall A (t : itree Void A), (forall a, ~(t≈ ret a)) -> divergence t.
    Proof.
      intros A. pcofix CIH. intros. pfold. unfold divergence_.
      destruct (observe t) eqn:Heqt.
      - specialize (itree_eta t) as H. rewrite Heqt in H.
        specialize (H0 r0). rewrite H in H0. exfalso. apply H0.
        reflexivity.
      - specialize (itree_eta t) as H. rewrite Heqt in H. constructor. right. eapply CIH; eauto.
        intros. rewrite <- tau_eutt. rewrite <- H. auto.
      - destruct e.
    Qed.

  Lemma tau_invar_prop_subst_aux : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), tau_invar Void A p ->
                               is_val A a t /\ is_val A a t' -> (p t -> p t').
  Proof.
    intros. destruct H0 as [Ht Ht'].
    induction  Ht'; induction Ht; auto.
    - apply H in H1. auto.
    - apply H in IHHt'. auto.
    - apply IHHt. apply H. auto.
  Qed.

  Lemma tau_invar_prop_subst_aux_eutt : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), resp_eutt Void A p ->
                                     is_val_eutt A a t /\ is_val_eutt A a t' -> (p t -> p t').
    Proof.
      intros. destruct H0 as [Ht Ht'].
      unfold is_val_eutt in *. rewrite <- Ht in Ht'. eapply H; try eassumption.
    Qed.
  Lemma tau_invar_prop_subst : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), tau_invar Void A p ->
                               is_val A a t /\ is_val A a t' -> (p t <-> p t').
    Proof.
      split; intros; eapply tau_invar_prop_subst_aux; eauto.
      destruct H0. split; eauto.
    Qed.

  Lemma tau_invar_prop_subst_eutt : forall A (a : A) (p : itree Void A -> Prop) (t t' : itree Void A), resp_eutt Void A p ->
                                     is_val_eutt A a t /\ is_val_eutt A a t' -> (p t <-> p t').
    Proof.
      split; intros; eapply tau_invar_prop_subst_aux_eutt; eauto. split; destruct H0; eauto.
    Qed.


  Lemma divergence_tau_invar : forall A, tau_invar Void A divergence.
  Proof.
    intros. split; intros.
    - pfold. left. constructor. auto.
    - pinversion H. subst. auto.
  Qed.

  Ltac dest_void := match goal with [ E : Void ?A  |- _ ]=> destruct E end.  

  Lemma divergence_resp_eutt' : forall A, resp_eutt Void A divergence.
    Proof.
      intro A. intro. intro.  intro. split.
      - generalize dependent t2. generalize dependent t1. pcofix CIH.
        intros. assert (Ht1 : divergence t1). auto. pfold. punfold H1. unfold divergence_ in *.
        destruct (observe t1) eqn : Heqt1; destruct (observe t2) eqn : Heqt2; try dest_void; try inv_div_ret.
        + specialize (itree_eta t2) as H. rewrite Heqt2 in H.
          rewrite H in H0. rewrite H0 in Ht1. pinversion Ht1.
        + constructor. inversion H1; subst. right. eapply CIH with (t1 := t1); eauto.
          clear H2 H1. rewrite H0. clear Heqt1.  specialize (itree_eta t2) as H. rewrite Heqt2 in H.
          rewrite <- (tau_eutt t0). rewrite H. reflexivity.
      - generalize dependent t2. generalize dependent t1. pcofix CIH.
        intros. assert (Ht2: divergence t2). auto. pfold. punfold H1. unfold divergence_ in *.
        destruct (observe t1) eqn : Heqt1; destruct (observe t2) eqn : Heqt2; try dest_void; try inv_div_ret.
        + specialize (itree_eta t1) as H. rewrite Heqt1 in H. rewrite H in H0.
          rewrite <- H0 in Ht2. pinversion Ht2.
        + constructor. inversion H1; subst. right. eapply CIH with (t2 := t2); eauto.
          rewrite <- H0. clear H1 H2 Heqt2. specialize (itree_eta t1 ) as H. rewrite Heqt1 in H.
          rewrite <- (tau_eutt t). rewrite H. reflexivity.
  Qed.

  Lemma divergence_resp_eutt : forall A, resp_eutt Void A divergence.
  Proof.
    intros. unfold resp_eutt. intros. rewrite H. tauto.
  Qed.

  Lemma no_val_div : forall A , tau_invar Void A (fun t => ~exists a, is_val A a t).
    Proof.
      intros. split; intros; intro Hcontra.
      - apply H. destruct Hcontra as [a Ha]. exists a. inv Ha. auto.
      - apply H. destruct Hcontra as [a Ha]. exists a. constructor. auto.
    Qed.
  End IsVal.
  (*End of deprecated section*)

  (*Morally, this is the return function. This is paired with a proof that all such specs are monotonic*)
  Definition _retpi A (a : A) : _PureITreeSpec A := fun p _ => p (ret a).

  Lemma retpi_monot : forall A (a : A), monotonici A (_retpi A a).
  Proof.
    unfold monotonici. intuition. unfold _retpi in *. auto.
  Qed.

  Lemma eutt_reta_or_div_aux : forall A (t : itree Void A), ~(exists a, ret a ≈ t) -> divergence t.
    Proof.
      intro A. pcofix CIH. pfold. unfold divergence_. intros. destruct (observe t) eqn : Heqt.
      - exfalso. specialize (itree_eta t) as H. rewrite Heqt in H. apply H0.
         exists r0. rewrite H. reflexivity.
       - constructor. right. eapply CIH; eauto. intro. apply H0.
         destruct H as [a Ha]. exists a. specialize (itree_eta t) as Ht. rewrite Heqt in Ht.
         rewrite Ht. rewrite tau_eutt. auto.
       - destruct e.
    Qed.

  (*All itrees with Void event type either just return a value a, or they diverge (requires the law of the excluded middle to prove) *)
  Lemma eutt_reta_or_div : forall A (t : itree Void A), (exists a, ret a ≈ t) \/ (divergence t).
    Proof.
      intros A t.  specialize (classic (exists a, ret a ≈ t) ) as Hlem. destruct Hlem; auto.
      right. apply eutt_reta_or_div_aux. auto.
    Qed.

  (*Proof that the predicate used in the bind function respects eutt*)
  Lemma bind_pred_resp_eutt : forall A B (f : A -> _PureITreeSpec B)
                                     (p : itree Void B -> Prop) (Hp : resp_eutt Void B p),
      resp_eutt Void A (fun (t : itree Void A) => (exists a, ret a ≈ t /\ f a p Hp) \/ 
                                                  (divergence t /\ p spin)).
  Proof.
    intros. intros t1 t2 Heutt. split; intros; destruct H.
    - destruct H as [ a [Hta Hfa] ]. left. exists a. rewrite Hta. auto.
    - rewrite Heutt in H. auto.
    - left. destruct H as [ a [Hta Hfa] ]. exists a. rewrite Hta. symmetry in Heutt. auto.
    - rewrite <- Heutt in H. auto.
  Qed.

(* map it into an itree whose return type is _PureITreeSpec, if that tree is inf, then deal separate
  Definition _iterpi (A B : Type) (body : A -> _PureITreeSpec (A + B) ) (init : A) : _PureITreeSpec B :=
    fun p Hp -> body a (fun (t: itree Void (A+B)) => ()  \/ (divergence t /\ p spin)  )
*)
  Lemma bind_pred_resp_eutt' : forall A B (f : A -> _PureITreeSpec B)
                               (p : itree Void B -> Prop) (Hp : resp_eutt Void B p) (w : _PureITreeSpec A),
      resp_eutt Void A (fun (t : itree Void A) => (exists a, ret a ≈ t /\ f a p Hp) \/
                                                  (divergence t /\ w divergence (divergence_resp_eutt A) /\ p spin )).
  Proof.
    intros. intros t1 t2 Heutt. split; intros; destruct H.
    - destruct H as [ a [Hta Hfa] ]. left. exists a. rewrite Hta. auto.
    - rewrite Heutt in H. auto.
    - left. destruct H as [ a [Hta Hfa] ]. exists a. rewrite Hta. symmetry in Heutt. auto.
    - rewrite <- Heutt in H. auto.
  Qed.    
  
  (*the bind function for the PureITreeSpec monad
    intuitively, you have two choices, prove the tree evaluates to a and prove f a p,
    or prove t is infinite and prove that the infinite predicate is in w*)
  Definition _bindpi A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B) :=
    fun (p : itree Void B -> Prop) (Hp : resp_eutt Void B p) =>
      w (fun (t : itree Void A) => (exists a, ret a ≈ t /\ f a p Hp) \/ 
                                   (divergence t /\  p spin ))
  (bind_pred_resp_eutt A B f p Hp).

  (*Possible alternate bind*)
  Definition _bindpi' A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B) :=
    fun (p : itree Void B -> Prop) (Hp : resp_eutt Void B p) =>
      w (fun (t : itree Void A) => (exists a, ret a ≈ t /\ f a p Hp) \/
                                   (divergence t /\ w divergence (divergence_resp_eutt A) /\ p spin) )
        (bind_pred_resp_eutt' A B f p Hp w).
 

  Lemma bindpi_monot : forall A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B),
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B (_bindpi A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *.
    set (fun (t : itree Void A) p0 Hp0 => (exists a, ret a ≈ t /\ f a p0 Hp0)\/ (divergence t /\ p spin))  as fp.
    enough (forall t, fp t p Hp -> fp t p' Hp').
    - eapply H with (p := fun t => fp t p Hp).
      + intros.  apply H3 in H4. 
        unfold fp in H4. destruct H4; auto.
        destruct H4. right. auto.
      + apply H2.
    - unfold fp. intros. destruct H3; auto. left.
      intros. destruct H3 as [a [Hvala Hfa] ].
      exists a. split; auto.
      eapply H0; eauto.
  Qed.

  Lemma bindpi_monot' : forall A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B),
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B ( _bindpi' A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *.
    set (fun (t : itree Void A) p0 Hp0 => (exists a, ret a ≈ t /\ f a p0 Hp0)\/ 
                                          (divergence t /\ w divergence (divergence_resp_eutt A) /\ p spin))  as fp.
    enough (forall t, fp t p Hp -> fp t p' Hp').
    - eapply H with (p := fun t => fp t p Hp).
      + intros.  apply H3 in H4. 
        unfold fp in H4. destruct H4; auto. right. destruct H4. destruct H5. split; auto.
      + apply H2.
    - unfold fp. intros. destruct H3; auto. left.
      intros. destruct H3 as [a [Hvala Hfa] ].
      exists a. split; auto.
      eapply H0; eauto.
  Qed.
  
  (*Definition of ret accounting for the proof of monotonicity*)
  Definition retpi A (a : A) : PureITreeSpec A :=
    exist _ (_retpi A a) (retpi_monot A a).

  (*Definition of bind accounting for the proof of monotonicity*)
  Definition bindpi A B (w : PureITreeSpec A) (f : A -> PureITreeSpec B) :=
    let '(exist _ w' Hw') := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist _ (_bindpi A B w' f') (bindpi_monot A B w' f' Hw' Hf').

  Definition bindpi' A B (w : PureITreeSpec A) (f : A -> PureITreeSpec B) :=
    let '(exist _ w' Hw') := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist _ (_bindpi' A B w' f') (bindpi_monot' A B w' f' Hw' Hf').

(* possible naturally written iter
 iter (body : A -> _PureITreeSpec (A + B) (a : A) :=
 fun p =>  body a (fun (t: itree Void (A + B) )
                (divergence t /\ p spin) \/
                (exists b, ret (inr b) ≈ t /\ p (ret b )) \/
                (exists a', ret (inl a')) ≈ t /\ body a' (iter body a' p)
) 

)


*)

  Lemma inf_tree_pred_resp_eutt : forall A B (p : itree Void B -> Prop), 
      resp_eutt Void (A + B) (fun (t : itree Void (A+B)) => divergence t /\ p spin ). 
  Proof.
    intros. intros t1 t2 Heutt. rewrite Heutt. reflexivity.
  Qed.

  Lemma term_b_pred_resp_eutt : forall A B (p : itree Void B -> Prop),
      resp_eutt Void (A + B) (fun (t : itree Void (A + B)) => exists b, ret (inr b) ≈ t /\ p (ret b)  ).
  Proof.
    intros. intros t1 t2 Heutt. split; intros.
    - destruct H. exists x. rewrite <- Heutt. auto.
    - destruct H. exists x. rewrite Heutt. auto.
  Qed.

  Lemma cont_a_pred_resp_eutt : forall A B (body : A -> PureITreeSpec (A + B) ) (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)
                                       ( F : (A -> PureITreeSpec (A + B) ) -> A -> _PureITreeSpec B ),
      resp_eutt Void ( A + B) (fun (t : itree Void (A + B)) => exists a' , ret (inl a') ≈ t /\ F body a' p Hp  ).
  Proof.
    intros. intros t1 t2 Heutt. split; intros.
    - destruct H. exists x. rewrite <- Heutt. auto.
    - destruct H. exists x. rewrite Heutt. auto.
  Qed.

(* maybe generalize body to A -> itree Void (A + B) -> Prop, and later prove, if forall a
   body respects eutt, then iter body a does and reformulate  *)

  (*may need to introduce notion of a well founded relation to the cont_a case, 
    this may induce another case where you know body a "infinitely loops"
*)

  Inductive iterF {A B : Type} (body : A -> PureITreeSpec (A + B) )
            (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : (A -> PureITreeSpec (A + B)) -> A -> _PureITreeSpec B ) : Prop :=

    | inf_tree : proj1_sig (body a) (fun (t : itree Void (A + B) )=> divergence t /\ p spin) (inf_tree_pred_resp_eutt A B p) -> iterF body a p Hp F
    | term_b : proj1_sig (body a) (fun t => exists b, ret (inr b)≈ t /\ p (ret  b) ) (term_b_pred_resp_eutt A B p) ->
        iterF body a p Hp F
    | cont_a
       : proj1_sig (body a) (fun t => exists a', ret (inl a') ≈ t /\ F body a' p Hp) (cont_a_pred_resp_eutt A B body a p Hp F) ->
         iterF body a p Hp F
.
Hint Constructors iterF.

Lemma iterF_monotone {A B} (body:  (A -> PureITreeSpec (A + B))) 
      (sim sim' : ((A -> PureITreeSpec (A + B) ) -> A -> _PureITreeSpec B )) (a : A)
      (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)
      (IN : iterF body a p Hp sim) (LE : sim <4= sim'):
  iterF body a p Hp sim'.
  Proof.
    induction IN; auto. apply cont_a.
    destruct (body a ) as [ba Hba] eqn : Heq.  simpl in *. eapply Hba; eauto. intros t. intros.
    destruct H0. destruct H0. exists x. split; auto. 
  Qed.

  Definition iter_ {A B} sim (body : A -> PureITreeSpec (A + B)) a p Hp :=
    iterF body a p Hp sim.
  Hint Unfold iter_.

  Lemma iterF_monotone' {A B} : monotone4 (@iter_ A B).
  Proof.
    do 2 red. intros. eapply iterF_monotone; eauto.
  Qed.

  Hint Resolve iterF_monotone' : paco.

  Definition _iter {A B}  : (A -> PureITreeSpec (A + B)) -> A ->  _PureITreeSpec B :=
    paco4 (@iter_ A B) bot4.

  Lemma iter_monot : forall A B (f : A -> PureITreeSpec (A + B) ) (a : A),
                              monotonici B (_iter f a).
    Proof.
      unfold monotonici. intros. generalize dependent a. pcofix CIH. pfold. intros. punfold H1.
      red. red in H1. inversion H1; simpl in *.
      - apply inf_tree. specialize (H spin).
        destruct (f a) as [fa Hfa]; simpl in *. eapply Hfa; eauto.
        intros. destruct H2. auto.
      - apply term_b. destruct (f a) as [fa Hfa]; simpl in *.
        eapply Hfa; eauto. intros. destruct H2 as [b Hb]. exists b. destruct Hb.
        auto.
      - apply cont_a. destruct (f a) as [fa Hfa]; simpl in *. eapply Hfa; eauto.
        intros. destruct H2 as [a' Ha']. exists a'. destruct Ha'. split; auto.
        right. eapply CIH. red. pclearbot. auto.
    Qed.

  Definition iter {A B} (body : A -> PureITreeSpec (A + B) ) (init : A) : PureITreeSpec B :=
    exist _ (_iter body init) (iter_monot A B body init).

(*there may be a way to reason about iteration in spec monads *)



  (*Monad equivalence relation for PureITreeSpec monad *)
  Global Instance PureITreeSpecEq : EqM PureITreeSpec :=
    fun A w1 w2 => forall (p : itree Void A -> Prop) (Hp : resp_eutt Void A p), proj1_sig w1 p Hp <-> proj1_sig w2 p Hp.

  
  Lemma ret_not_div : forall (A : Type) (E : Type -> Type) (a : A), ~ (@divergence E A (ret a)).
    Proof.
      intros. intro Hcontra. pinversion Hcontra.
    Qed.

  Lemma inv_ret : forall (A : Type) (E : Type -> Type) (a b : A),
        @eutt E A A eq (ret a) (ret b) -> a = b.
    Proof. 
      intros. pinversion H; subst. auto.
    Qed.
 

  Section SpecMonadCand1.
    Instance PureItreeSpecMonad : Monad PureITreeSpec :=
    {
      ret := retpi;
      bind := bindpi
    }.


  (*Monad law proofs*)
  Lemma retpi_bindpi : forall A B (f : A -> PureITreeSpec B) (a : A), 
      bind (ret a) f ≈ f a.
    Proof.
      intros. split.
      - cbn. unfold _bindpi. unfold _retpi. intros. 
        destruct H.
        + destruct H as [a0 [Hvala0 Hfa0] ].
          apply inv_ret in Hvala0. subst. auto.
        + exfalso. destruct H. eapply ret_not_div. eauto.
      - simpl. destruct (f a) as [fa Hfa] eqn : Heq. simpl. intros.
        left. exists a. split.
        + reflexivity.
        + rewrite Heq.  auto.
    Qed.

  Lemma bindpi_retpi : forall A (w : PureITreeSpec A), bind w (fun x => ret x) ≈ w.
  Proof.
    intros. destruct w as [ w Hw]. split.
    - intros. simpl in *. unfold _bindpi in H.
      unfold _retpi in H. simpl in H.
      eapply Hw.
      2: apply H.
      intros. destruct H0.
      + destruct H0 as [a [ Hvala Hpa]  ].
        eapply Hp; eauto. symmetry. auto.
      + destruct H0. apply div_spin_eutt in H0. eapply Hp; eauto.
    - simpl. intros. unfold _bindpi.
      eapply Hw. 2: apply H. intros. unfold _retpi.
      specialize (eutt_reta_or_div A i') as Hor. destruct Hor.
      + destruct H1 as [a Ha]. left. exists a. split; auto. eapply Hp; eauto.
      + right. split; auto. specialize (div_spin_eutt A i' H1) as H2. symmetry in H2. eapply Hp; eauto.
   Qed.

  Lemma bindpi_bindpi : forall (A B C : Type) (w : PureITreeSpec A) 
                               (f : A -> PureITreeSpec B) (g : B -> PureITreeSpec C),
      bind (bind w f) g ≈ bind w (fun a => bind (f a) g).
    Proof.
      intros. destruct w as [w Hw]. simpl. split; intros.
      - simpl in *. eapply Hw; try apply H. intros t0. intros. destruct H0.
        + destruct H0 as [a [Hreta Hfa] ].
          left. exists a. split; auto. destruct (f a) as [wfa Hwfa]. simpl in *.
          eapply Hwfa; try (apply Hfa). intros t1. intros. destruct H0; auto.
        + destruct H0. destruct H1.
          * destruct H1 as [b [Hretb Hgb ]  ]. exfalso. specialize (ret_not_div B Void b) as Hndiv.
            rewrite Hretb in Hndiv. apply Hndiv. apply spin_div.
          *  right. destruct H1. auto.
      - simpl in *. eapply Hw; try apply H. intros t0. intros. destruct H0.
        +  destruct H0 as [a [Hreta Hfa] ]. left. exists a. split; auto.
           destruct (f a) as [wfa Hwfa]. simpl in *. eapply Hwfa; try (apply Hfa). intros t1. intros.
           destruct H0; auto.
        + destruct H0. right. split; auto. right. split; auto. apply spin_div.
    Qed.


  Instance PureItreeSpecLaws : MonadLaws PureITreeSpec.
  Proof.
    constructor.
    - apply retpi_bindpi.
    - apply bindpi_retpi.
    - apply bindpi_bindpi.
  Qed.  

  Instance PureITreeIter : Iter (Kleisli PureITreeSpec) sum := @iter.
  
  Instance PureITreeIterUnfold : IterUnfold  (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B f a.
    constructor.
    (*this case went through without even needing coinduction???*)
    - intros. red. red in H. repeat red in H.
      punfold H. inversion H.
      + destruct (f a) as [fa Hfa] eqn : Heq; simpl in *.
        repeat red. rewrite Heq. red. eapply Hfa; eauto.
        intro t. intros. destruct H1. right. auto.
      + destruct (f a) as [fa Hfa] eqn : Heq; simpl in *.
        repeat red. rewrite Heq. red. eapply Hfa; eauto.
        intros t ?. destruct H1 as [b [Hb Hpb] ]. left. exists (inr b).
        split; auto.
      +  destruct (f a) as [fa Hfa] eqn : Heq; simpl in *.
         repeat red. rewrite Heq. red. eapply Hfa; eauto.
         intros t ?. left. destruct H1 as [a' [Ha' Hpa'] ]. pclearbot.
         exists (inl a'). split; auto.
    (*this case is probably where I need coinduction*)
    - intros. red. repeat red in H. destruct (f a) as [fa Hfa] eqn : Heq.
      red in H. destruct (iter f a) as [iterfa Hiterfa] eqn : Heq'.
      unfold CategoryOps.iter, PureITreeIter. rewrite Heq'.

  Admitted.
  

  Instance PureITreeOrderM : OrderM PureITreeSpec :=
    fun A (w1 w2 : PureITreeSpec A) => forall p Hp, proj1_sig w2 p Hp -> proj1_sig w1 p Hp.

  Instance PureItreeOrder : OrderedMonad PureITreeSpec.
  Proof.
    unfold OrderedMonad. intros. destruct w1 as [w1' Hw1']. destruct w2 as [w2' Hw2']. simpl in *.
    intros p Hp. simpl.
    unfold _bindpi. intros.  eapply H. simpl.
    eapply Hw2'; try (apply H1). intros t. intros. destruct H2; auto.
    destruct H2 as [a [Hreta Hf2a] ]. left. specialize (H0 a p Hp). exists a. auto.
  Qed.

  (*Definition of effect observation from pure itrees into pure itree specs *)
  Definition _obsip A (t : itree Void A) : _PureITreeSpec A := fun p _ => p t.

  Lemma obsip_monot : forall A (t : itree Void A), monotonici A (_obsip A t).
    Proof.
      unfold monotonici. intros. unfold _obsip in *. auto.
    Qed.

  Definition obsip A (t : itree Void A) : PureITreeSpec A :=
    exist _ (_obsip A t) (obsip_monot A t).

  (*Proof that this effect observation is a valid monad morphism*)
  Lemma obsip_pres_ret : forall A (a : A), obsip A (ret a) ≈ ret a.
    Proof.
      intros. intros p Hp. cbn. unfold _retpi, _obsip. tauto.
    Qed.

  Lemma obsip_pres_bind : forall A B (t : itree Void A) (f : A -> itree Void B),
        obsip B (bind t f) ≈ bind (obsip A t) (fun a => obsip B (f a)).
    Proof.
      intros. intros p Hp. cbn. unfold _obsip, _bindpi. split; intros.
      - specialize (eutt_reta_or_div A t) as Hor. destruct Hor.
        + destruct H0 as [a Hreta ]. left. exists a. split; auto.
          assert (p (bind (ret a) f) ). 
          * eapply Hp; eauto. rewrite <- Hreta. reflexivity.
          * simpl in H0. eapply Hp; eauto. symmetry. specialize (bind_ret a f) as H1. rewrite H1. reflexivity.
        + right. split; auto. apply div_spin_eutt in H0. specialize (spin_bind Void A B f) as H1.
          eapply Hp; eauto. rewrite <- H0 in H1. eapply Hp; eauto. rewrite <- H0. reflexivity.
      - destruct H.
        + destruct H as [a [Hreta Hpfa] ]. specialize (bind_ret a f) as H1.
          assert (bind (ret a) f ≈ f a ). {  rewrite H1. reflexivity. }
           rewrite Hreta in H. eapply Hp; eauto.
        + destruct H. apply div_spin_eutt in H.
          assert (bind t f ≈ spin). {  rewrite H. symmetry. apply spin_bind. }
          eapply Hp; eauto.
    Qed.

    Instance PureITreeEffectObs : EffectObs (itree Void) (PureITreeSpec) := obsip.

    Instance PureITreeMorph : MonadMorphism (itree Void) (PureITreeSpec) PureITreeEffectObs.
    Proof.
      constructor.
      - apply obsip_pres_ret.
      - apply obsip_pres_bind.
    Qed.
    (* not 100% sure but I think this actually is a partial correctness spec, or maybe not?  *)
  

  End SpecMonadCand1.

  Section SpecMonadCand2.
    
    Lemma div_imp_p_iff_p_spin : forall A (p : itree Void A -> Prop),
      (resp_eutt Void A p) ->
      (forall t, divergence t -> p t) <-> p spin.
      Proof.
        intros. split.
        - intros. apply H0. apply spin_div.
        - intros. apply div_spin_eutt in H1. eapply H; eauto.
      Qed.

    Instance PureITreeSpecMonad : Monad PureITreeSpec := 
      {
        ret := retpi;
        bind := bindpi';
      }.

     Lemma retpi_bindpi' : forall A B (f : A -> PureITreeSpec B) (a : A),
        bind (ret a) f ≈ f a.
     Proof.
       intros. split.
       - cbn. unfold _bindpi', _retpi. intros. destruct (f a) as [wfa Hwfa] eqn : Heqfa.
         simpl. destruct H. 
         + destruct H as [ a0 [Hreta0 Hfa0] ]. apply inv_ret in Hreta0. subst.
           rewrite Heqfa in Hfa0. simpl in *. auto.
         + destruct H. apply ret_not_div in H. contradiction.
       - intros. cbn. unfold _bindpi', _retpi. left. exists a. split; auto.
         reflexivity.
     Qed.

     Lemma bindpi'_retpi : forall A (w : PureITreeSpec A), bind w (fun x => ret x) ≈ w.
       Proof.
         intros. destruct w as [w Hw]. split.
         - cbn. unfold _bindpi'. eapply Hw. intros t.
           intros. destruct H.
           + destruct H as [ a [Hreta Hpa] ]. unfold _retpi in Hpa.
             eapply Hp; try apply Hpa. symmetry. auto.
           + destruct H.  apply div_spin_eutt in H as Htspin.
             enough (p spin). { eapply Hp; eauto. } tauto.
         - simpl. unfold _bindpi'. intros. eapply Hw; eauto.
           intros t. intros. unfold _retpi.
           specialize (eutt_reta_or_div A t) as Hor. destruct Hor.
           + left. destruct H1 as [a Hreta].  exists a. split; auto. eapply Hp; eauto.
           + right. split; auto. split.
             * unfold monotonici in Hw.
               assert (p spin). { apply div_spin_eutt in H1. eapply Hp; eauto. symmetry. auto. }
               (* maybe need w to be downwardly closed in some sense, maybe pays to continue with the other model,
                  come back to this later*)
               destruct (div_imp_p_iff_p_spin A p Hp) as [H3 H4]. specialize (H4 H2).
               (* w accepts p, div ⊆ p, therefore should w accept div, this seems like the hoare logic weakening rule,
                  when start having preconditions (like state)  will probably need contravariant weakening*)

               (* pureitree spec is a psot condition enricher, as is exceptions, 
                  state is a precondition and post condition enricher  *)
               admit. (* this case seems conceptually new ...  *)
             * eapply Hp; eauto.  symmetry. apply div_spin_eutt. auto.
       Admitted.
       End SpecMonadCand2.
  
  (* does this satisfy the monad laws? is it unique in some sense, if not what are the implications of
   this choice*)
  
  (* maybe could parameterize bind on a predicate is_val A a itree -> Prop, and that predicate
     determines how nonterminism is handled, that shouldn't be hard, my proof of monot
     didn't seem to rely on the def of is_val, likely bad choices would break monad laws?
     *)
                       

(* is this monotonic?   *)

End PureITree.

Section StateITree.
  Context (S : Type).
  
  Definition StateITree A := itree (stateE S) A.

  Definition _StateITreeSpec A := forall (p : itree Void (A * S) -> Prop), resp_eutt Void (A * S) p -> S -> Prop.

  Definition monotonicsi A (w : _StateITreeSpec A) := forall (p p' : itree Void (A * S) -> Prop) 
                                                             Hp Hp' s, (forall t, p t -> p' t) -> w p Hp s -> w p' Hp' s.

  Definition StateITreeSpec A := {w : _StateITreeSpec A | monotonicsi A w}.

  Definition _retsi A (a : A) : _StateITreeSpec A := fun p _ s => p (ret (a,s)).

  Lemma monot_retsi : forall A (a : A), monotonicsi A (_retsi A a).
    Proof.
      intros. unfold _retsi. intros p p' _ _ s. intros. apply H. auto.
    Qed.

  Definition retsi A (a : A) : StateITreeSpec A := exist _ (_retsi A a) (monot_retsi A a).

  Lemma bindsi_pred_eutt : forall A B (w : _StateITreeSpec A) (f : A -> _StateITreeSpec B) 
                                  (p : itree Void (B * S) -> Prop) (Hp : resp_eutt Void (B * S) p) (s : S), 
         resp_eutt Void (A * S) (fun t => (exists a s', ret (a,s') ≈ t /\ f a p Hp s') \/ divergence t /\ p spin).
  Proof.
    intros. intros t1 t2 Heutt. split; intros.
    - destruct H.
      + destruct H as [a [s' [Hretas Hfa ] ] ]. left. exists a. exists s'. split; auto.
        rewrite Hretas. auto.
      + right. rewrite <- Heutt. auto.
    - destruct H.
      + destruct H as [a [s' [Hretas Hfa ] ] ]. left. exists a. exists s'. split; auto.
        rewrite Heutt. auto.
      + right. rewrite <- Heutt in H. auto.
   Qed.

  Definition _bindsi A B (w : _StateITreeSpec A) (f : A -> _StateITreeSpec B) :=
    fun (p : itree Void (B * S) -> Prop) (Hp : resp_eutt Void (B * S) p) (s : S) =>
      w (fun (t : itree Void (A * S) )=> (exists a s', ret (a,s') ≈ t /\ f a p Hp s' )  \/ 
                                         (divergence t /\ p spin) )  
        (bindsi_pred_eutt A B w f p Hp s) s.

  Lemma monot_bindsi : forall A B (w : _StateITreeSpec A) (f : A -> _StateITreeSpec B), monotonicsi A w ->
      (forall a, monotonicsi B (f a)) -> monotonicsi B (_bindsi A B w f).
  Proof.
    unfold monotonicsi. intros. unfold _bindsi in *.
    set (fun (t : itree Void (A * S)) p0 Hp0 => (exists a s', ret (a,s') ≈ t /\ f a p0 Hp0 s') \/ (divergence t /\ p0 spin)) as fp.
    enough (forall t, fp t p Hp -> fp t p' Hp').
    - eapply H with (p := fun t => fp t p Hp); eauto.
    - unfold fp. intros. destruct H3.
      + left. destruct H3 as [a [s' [Hretas' Hfa] ] ].
        exists a. exists s'. split; auto. eapply H0; eauto.
      + right. destruct H3. split; auto.
  Qed.

  Definition bindsi A B (w : StateITreeSpec A) (f : A -> StateITreeSpec B) : StateITreeSpec B :=
             let '(exist _ w' Hw') := w in
             let f' := fun a => proj1_sig (f a) in
             let Hf' := fun a => proj2_sig (f a) in 
             exist _ (_bindsi A B w' f') (monot_bindsi A B w' f' Hw' Hf').

  Global Instance StateITreeSpecEq : EqM StateITreeSpec :=
    fun A (w1 w2 : StateITreeSpec A) => forall p Hp s, proj1_sig w1 p Hp s <-> proj1_sig w2 p Hp s.

  Global Instance StateITreeSpecMonad : Monad StateITreeSpec :=
    {
      ret := retsi;
      bind := bindsi;
    }.

    (*Monad law proofs*)
  Lemma retsi_bindsi : forall A B (f : A -> StateITreeSpec B) (a : A), 
      bind (ret a) f ≈ f a.
    Proof.
      intros. split.
      - cbn. unfold _bindsi, _retsi. intros. destruct H.
        + destruct H as [a0 [s' [Haa0 Hfa0] ] ]. apply inv_ret in Haa0. injection Haa0 as H. subst. auto.
        + destruct H. exfalso. eapply ret_not_div; eauto.
      - cbn. unfold _bindsi, _retsi. intros. left. exists a. exists s.
        split; auto. reflexivity.
   Qed.

  Lemma bindsi_retsi : forall A (w : StateITreeSpec A), bind w (fun x => ret x) ≈ w.
  Proof.
    intros. destruct w as [ w Hw]. split.
    - cbn. unfold _bindsi, _retsi. intros. eapply Hw; try (apply H). intros.
      destruct H0.
      + destruct H0 as [ a [s' [Hretas' Has'] ] ]. symmetry in Hretas'. eapply Hp; eauto.
      + destruct H0. apply div_spin_eutt in H0. eapply Hp; eauto.
    - cbn. unfold _bindsi, _retsi. intros. eapply Hw; try (apply H). intros.
      specialize (eutt_reta_or_div (A * S) t). intros. destruct H1.
      + destruct H1 as [ [a s']  Hretas']. left. exists a. exists s'. split; auto.
        eapply Hp; eauto.
      + right. split; auto. eapply Hp; eauto. apply div_spin_eutt in H1. symmetry. auto.
   Qed.

  Lemma bindsi_bindsi : forall A B C (w : StateITreeSpec A) (f : A -> StateITreeSpec B) (g : B -> StateITreeSpec C), 
      bind (bind w f) g ≈ bind w (fun a => bind (f a) g).
  Proof.
    intros. destruct w as [w Hw]. split; cbn.
    - unfold _bindsi. intros. eapply Hw; try (apply H). intros. simpl in H0. clear H.
      destruct H0.
      + destruct H as [a [s' H ] ]. destruct H. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *.
        left. exists a. exists s'. split; auto. rewrite Heq. simpl. eapply Hfa; (try apply H0).
        intros. destruct H1; auto.
      + destruct H. destruct H0.
        * destruct H0 as [b [s'' [Hretbs'' Hga] ] ]. exfalso.
          specialize (spin_div Void (B* S) ) as H0. rewrite <- Hretbs'' in H0. pinversion H0.
        * right. tauto.
   - unfold _bindsi. intros. eapply Hw; try (apply H). simpl in *. intros. clear H. destruct H0.
     + destruct H as [a [s' H] ]. destruct H. left. exists a. exists s'. split; auto.
       destruct (f a) as [fa Hfa]. simpl in *. eapply Hfa; try apply H0. intros.
       destruct H1; auto.
     + destruct H. right. split; auto. right. split; auto. apply spin_div.
  Qed.
        
  Global Instance StateITreeSpecMonadLaws : MonadLaws StateITreeSpec.
  Proof.
    constructor.
    - apply retsi_bindsi.
    - apply bindsi_retsi.
    - apply bindsi_bindsi.
  Qed.

  Global Instance StateITreeSpecOrderM : OrderM StateITreeSpec :=
    fun A (w1 w2 : StateITreeSpec A) => forall p Hp s, proj1_sig w2 p Hp s -> proj1_sig w1 p Hp s.

  Global Instance StateITreeSpecOrderLaws : OrderedMonad StateITreeSpec.
  Proof.
    intros A B w1 w2 f1 f2. intros. destruct w1 as [w1 Hw1]. destruct w2 as [w2 Hw2]. cbn in *.
    intros p Hp s. cbn. unfold _bindsi. intros. apply H. simpl. eapply Hw2; try apply H1.
    intros. destruct H2; auto.
    destruct H2 as [a [s' [Hretas' Hf2a] ] ]. left. exists a. exists s'. split; auto.
    apply H0. auto.
  Qed.

  Definition _obssi A (m : S -> itree Void (A * S)) : _StateITreeSpec A :=
    fun post Hp s => post (m s).

  Lemma monot_obssi : forall A (m : S -> itree Void (A * S)), monotonicsi A (_obssi A m).
  Proof.
    unfold monotonicsi. intros. apply H. auto.
  Qed.

  Definition obssi A (m : S -> itree Void (A * S) ) : StateITreeSpec A :=
    exist _ (_obssi A m) (monot_obssi A m).

  Definition ret_stateitree A (a : A) : (S -> itree Void (A * S) ):= fun s => ret (a,s).

  Definition bind_stateitree A B (m : S -> itree Void (A * S) ) (f : A -> (S -> itree Void (B * S))) : S -> (itree Void (B * S)) :=
    fun s => let t := m s in bind t (fun '(a,s') => f a s' ) .

  Global Instance StateTransformITreeMonad : Monad (fun A => S -> itree Void (A * S)) :=
    {
      ret := ret_stateitree;
      bind := bind_stateitree;
    }.

  Lemma obssi_pres_ret : forall A (a : A), obssi A (ret a) ≈ ret a.
  Proof.
    intros. cbn. intros p Hp s. split; intros; apply H.
  Qed.

  Lemma obssi_pres_bind : forall A B (m : S -> itree Void (A * S) ) (f : A -> S -> itree Void (B * S)),
      obssi B (bind m f) ≈ bind (obssi A m) (fun a => obssi B (f a) ).
  Proof.
    intros. cbn. intros p Hp s. split; intros.
    - simpl in *. unfold bind_stateitree in H. unfold _obssi in H.
      unfold _bindsi. unfold _obssi.
      specialize (eutt_reta_or_div _ (m s) ) as Hor. destruct Hor.
      * left. destruct H0 as [ [a s' ] Has']. exists a. exists s'. split; auto.
        eapply Hp; eauto. rewrite <- Has'. simpl. symmetry. specialize (bind_ret (a,s') (fun '(a0,s0) => f a0 s0) ) as H1.
        simpl in H1. rewrite H1. reflexivity.
      * right. split; auto. apply div_spin_eutt in H0. eapply Hp; eauto. rewrite H0. apply spin_bind.
    - simpl in *. unfold bind_stateitree. unfold _bindsi, _obssi in *. destruct H.
      + destruct H as [a [s' [Hretas' Hpfa] ] ]. eapply Hp; eauto. rewrite <- Hretas'.
        specialize (bind_ret (a,s') (fun '(a0,s0) => f a0 s0 ) ) as H1. simpl in H1. rewrite H1. reflexivity.
      + destruct H. eapply Hp; eauto. apply div_spin_eutt in H. rewrite H. symmetry. apply spin_bind.
  Qed.
   
End StateITree.
(*
  Definition _interpStateSpec : (stateE S) ~> (_StateSpec S) :=
    fun _ (ev : stateE S _) =>
      match ev with
        | Get _ => fun p s => p (s,s)
        | Put _ s => fun p s' => p (tt,s) end.

  Lemma monot_interpStateSpec : forall A ev, monotonic S (_interpStateSpec A ev).
    Proof.
      unfold monotonic. intros. cbv. destruct ev; auto.
    Qed.

  Definition monotonicis A (w : _StateITreeSpec A) := 
    forall (p p' : itree Void (A * S) -> Prop ) s, (forall i s', p (ret (i,s')) -> p' (ret (i,s')))
                                                                      -> w p s -> w p' s.

  Definition _retis A (a : A) : _StateITreeSpec A :=
    fun p s => p (ret (a,s)).

  Lemma retis_monot : forall A a, monotonicis A (_retis A a).
  Proof.
    unfold monotonicis. intros. unfold _retis in *. auto.
  Qed. *)
(* bind I think needs some coinduction, I'll leave it out for now
  Definition _bindis A B (m : _StateItreeSpec A) (f : A -> _StateItreeSpec B) :=
    fun p s => m (fun '(i,s') =>  ) s

    if i = tau ^ ω then p (i,s') since i has either type _StateItreeSpec A or _StateItreeSpec B
    else i = tau ^* (Ret a) then p (ret (a,s'))

    problem is the first case doesn't terminate, need more info on coinduction from Steve maybe?
*)

(*

  Definition StateITreeSpec A := {w : _StateITreeSpec A | monotonicis _ w}.

  Definition interpStateSpecCore : forall A, (stateE S A) -> (itree Void (StateSpec S A)) :=
    fun A ev => 
    ret (exist _ (_interpStateSpec A ev) (monot_interpStateSpec A ev)).

  Definition StateSpecT (M : Type -> Type) (A : Type) := (M (A * S)%type -> Prop) -> S -> Prop.
End StateITree. 
(*
  Global Instance StateSpecIter : Monad

  Definition interpStateSpec (A : Type) (t : itree (stateE S) A) : 
    StateSpecT  (itree Void) A := interp interpStateSpecCore t.

  *)
(*
  Definition _retsis A (a: A) : _StateItreeSpec A := fun p s => p (Itree.ret _ (a,s)).

  Definition _stateH A (ev : stateE S) :=
    match ev with
    | Get => fun 


  

  CoInductive t :=.
*)
*)
