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

  (* same as monot  *)
  Definition dmonot A (w : _PureITreeSpec A) :=
    forall (p p' : itree Void A -> Prop) Hp Hp', (forall t, p t <-> p' t) -> (w p Hp <-> w p' Hp').
  (* what if we identify a spec with the intersection of all of the preds it accepts*)
  Lemma monot_imp_dmonot : forall A (w : _PureITreeSpec A), monotonici A w -> dmonot A w.
  Proof.
    unfold monotonici, dmonot. intros. split.
    - apply H; auto. intros. apply H0. auto.
    - apply H; auto. intros. apply H0. auto.
  Qed.

  (* does not hold for many basic specs  *)
  Definition amonot A (w : _PureITreeSpec A) :=
    forall (p p' : itree Void A -> Prop) Hp Hp', (forall t, p t -> p' t) -> w p' Hp' -> w p Hp.

  (*Sigm*)
  Definition PureITreeSpec A := {w : _PureITreeSpec A | monotonici A w}.

  (*The set of predicates that accept divergent trees*)
  Definition _div_spec A : _PureITreeSpec A := fun p _ => p spin.

  Lemma div_spec_monot : forall A, monotonici A (_div_spec A).
    Proof.
      unfold monotonici, _div_spec. auto.
    Qed.

  Lemma div_spec_amonot : forall A , amonot A (_div_spec A).
  Proof.
    unfold amonot, _div_spec. intros. auto.
  Abort.
  Definition div_spec A := exist _ (_div_spec A) (div_spec_monot A).

  (*Morally, this is the return function. This is paired with a proof that all such specs are monotonic*)
  Definition _retpi A (a : A) : _PureITreeSpec A := fun p _ => p (ret a).

  Lemma retpi_monot : forall A (a : A), monotonici A (_retpi A a).
  Proof.
    unfold monotonici. intuition. unfold _retpi in *. auto.
  Qed.

  Lemma retpi_amonot : forall A (a : A), amonot A ( _retpi A a ).
  Proof.
    unfold amonot, _retpi. intros.
    Abort.

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

  
  (*the bind function for the PureITreeSpec monad
    intuitively, you have two choices, prove the tree evaluates to a and prove f a p,
    or prove t is infinite and prove that the infinite predicate is in w*)
  Definition _bindpi A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B) :=
    fun (p : itree Void B -> Prop) (Hp : resp_eutt Void B p) =>
      w (fun (t : itree Void A) => (exists a, ret a ≈ t /\ f a p Hp) \/ 
                                   (divergence t /\  p spin ))
  (bind_pred_resp_eutt A B f p Hp).
 

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

  
  (*Definition of ret accounting for the proof of monotonicity*)
  Definition retpi A (a : A) : PureITreeSpec A :=
    exist _ (_retpi A a) (retpi_monot A a).

  (*Definition of bind accounting for the proof of monotonicity*)
  Definition bindpi A B (w : PureITreeSpec A) (f : A -> PureITreeSpec B) :=
    let '(exist _ w' Hw') := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist _ (_bindpi A B w' f') (bindpi_monot A B w' f' Hw' Hf').
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

  Lemma resp_eutt_or : forall A (p p' : itree Void A -> Prop), 
      resp_eutt _ _ p -> resp_eutt _ _ p' -> resp_eutt _ _ (fun t => p t \/ p' t).
  Proof.
    intros. intros t1 t2 Ht. split; intros.
    - destruct  H1.
      + left. eapply H; eauto. symmetry. auto.
      + right. eapply H0; eauto. symmetry. auto.
    - destruct H1.
      + left. eapply H; eauto.
      + right. eapply H0; eauto.
  Qed.

  Definition iterF_body {A B : Type} (body : A -> PureITreeSpec (A + B) )
            (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : (A -> PureITreeSpec (A + B)) -> A -> _PureITreeSpec B ) :=
    fun (t : itree Void (A + B) ) =>( divergence t /\ p spin ) \/
                                    (exists b, ret (inr b) ≈ t /\ p (ret b)  ) \/
                                    (exists a', ret (inl a') ≈ t /\ F body a' p Hp ).

  Lemma iterF_body_resp_eutt : forall (A B : Type)  (body : A -> PureITreeSpec (A + B) )
            (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : (A -> PureITreeSpec (A + B)) -> A -> _PureITreeSpec B ),
      resp_eutt _ _ (iterF_body body a p Hp F).
  Proof.
    intros. eapply resp_eutt_or; try eapply resp_eutt_or; intros.
    - apply inf_tree_pred_resp_eutt.
    - apply term_b_pred_resp_eutt.
    - apply cont_a_pred_resp_eutt. auto.
  Qed.

  

(* maybe generalize body to A -> itree Void (A + B) -> Prop, and later prove, if forall a
   body respects eutt, then iter body a does and reformulate  *)

  (*may need to introduce notion of a well founded relation to the cont_a case, 
    this may induce another case where you know body a "infinitely loops"
*)
  (* this may be some kind of generalization of loop invariants with well founded relations  *)
  (* change so that body a is   *)

(*
  Inductive iterF {A B : Type} (body : A -> PureITreeSpec (A + B) )
            (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : (A -> PureITreeSpec (A + B)) -> A -> _PureITreeSpec B ) : Prop :=

    | inf_tree : proj1_sig (body a) (fun (t : itree Void (A + B) )=> divergence t /\ p spin) (inf_tree_pred_resp_eutt A B p) -> iterF body a p Hp F
    | term_b : proj1_sig (body a) (fun t => exists b, ret (inr b)≈ t /\ p (ret  b) ) (term_b_pred_resp_eutt A B p) ->
        iterF body a p Hp F
    | cont_a
       : proj1_sig (body a) (fun t => exists a', ret (inl a') ≈ t /\ F body a' p Hp) (cont_a_pred_resp_eutt A B body a p Hp F) ->
         iterF body a p Hp F
.

*)

  Variant iterF {A B : Type} (body : A -> PureITreeSpec (A + B))
          (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt Void B p) (F : (A -> PureITreeSpec (A + B)) -> A -> _PureITreeSpec B ) : Prop :=
    | iterF_con : proj1_sig (body a) (iterF_body body a p Hp F) (iterF_body_resp_eutt A B body a p Hp F) -> iterF body a p Hp F.

Hint Constructors iterF.
Lemma iterF_monotone {A B} (body:  (A -> PureITreeSpec (A + B))) 
      (sim sim' : ((A -> PureITreeSpec (A + B) ) -> A -> _PureITreeSpec B )) (a : A)
      (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)
      (IN : iterF body a p Hp sim) (LE : sim <4= sim'):
  iterF body a p Hp sim'.
  Proof.
    induction IN; constructor; auto.
    destruct (body a) as [fa Hfa] eqn : Heq. simpl in *.
    unfold iterF_body in *. eapply Hfa; try apply H.
    intros. destruct H0; try destruct H0; auto.
    right. right. destruct H0 as [ a' [Hret Hsim] ]. exists a'. auto.
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
      unfold monotonici. intros. generalize dependent a.
      pcofix CIH. pfold. intros. punfold H1.
      red. red in H1. inversion H1; simpl in *.
      constructor. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *.
      eapply Hfa; try apply H0. intros t. intros.
      unfold iterF_body in *.
      destruct H2 as [ ? | [? | ?] ].
      - left. destruct H2. split; auto.
      - destruct H2 as [b [Hret Hpb]  ]. right. left. exists b. split; auto.
      - destruct H2 as [a' [Hret Hpaco] ]. pclearbot. right. right.
        exists a'. split; auto.
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

  Instance PureITreeIter : Iter (Kleisli PureITreeSpec) sum := @iter.

  Instance PureITreeIterUnfold : IterUnfold  (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B f a.
    constructor.
    (*this case went through without even needing coinduction???*)
    - intros. red. repeat red in H.
      punfold H. inversion H.
      unfold cat, Cat_Kleisli. destruct (f a) as [fa Hfa] eqn : Heq; simpl in *.
      unfold _bindpi. unfold iterF_body in H0. eapply Hfa; eauto.
      intro t. intros. destruct H1 as [ ? | [? | ?] ]; auto.
      + destruct H1 as [b [Hretb Hpb] ]. left. exists (inr b). simpl. auto.
      + left. destruct H1 as [a' [Hreta' Hpacoa' ] ]. pclearbot.
        exists (inl a'). simpl. auto.
    (*this case is probably where I need coinduction*)
    - revert a.  pcofix CIH. unfold cat, Cat_Kleisli in *. intros.
      pfold. red. constructor. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *.
      unfold _bindpi in H0. unfold iterF_body. eapply Hfa; eauto.
      clear H0. intros t. intros. destruct H; auto.
      destruct H as [ [a' | b] [? ?] ]; simpl in *.
      + right. right. exists a'. split; auto. right. apply CIH.
        destruct (f a') as [fa' Hfa'] eqn : Heq'. simpl. unfold _bindpi. 
        punfold H0. inversion H0; subst. rewrite Heq' in H1. simpl in *.
        unfold iterF_body in H1. eapply Hfa'; eauto. intros t'. intros.
        destruct H2 as [? | [? | ?] ]; auto.
        * destruct H2 as [b [? ?] ]. left. exists (inr b). auto.
        * destruct H2 as [a'' [? ?] ]. left. exists (inl a''). pclearbot.
          auto.
      + right. left. exists b. auto.
  Qed.
 
  Lemma not_ret_eutt_spin : forall A E (a : A), ~ (ret a ≈ @spin E A).
  Proof.
    intros. intro Hcontra. specialize (spin_div E A) as Hdiv. rewrite <- Hcontra in Hdiv.
    pinversion Hdiv.
  Qed.


  Ltac clear_ret_eutt_spin :=
    match goal with | H : ret ?a ≈ spin  |- _ => exfalso; eapply not_ret_eutt_spin; eauto
                    | H : spin ≈ ret ?a  |- _ => exfalso; symmetry in H; eapply not_ret_eutt_spin; eauto
                    end.
  
  Instance PureITreeIterNatural : IterNatural (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B C. intros. constructor.
    - intros. generalize dependent a. pcofix CIH. intros. pfold. repeat red in H. punfold H0. destruct H0.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. constructor.
      cbn. rewrite Heq. simpl. unfold _bindpi. eapply Hfa; eauto.
      intros t ?. unfold iterF_body in H0.
      destruct H0.
      + destruct H0 as [ Ht [? | ? ] ].
        * destruct H0 as [b [? ?] ]. specialize (spin_div Void B) as Hcontra. rewrite <- H0 in Hcontra. pinversion Hcontra.
        * right. split; auto. destruct H0. unfold iterF_body. left. split; auto. apply spin_div.
      + clear H. destruct H0.
        * destruct H as [b [ ? ?] ]. left. exists (inr b). split; auto. destruct H0.
          -- destruct H0 as [b' [Hab Hgbp] ].  pinversion Hab. subst. clear Hab.
             cbn. destruct (g b) as [gb Hgb] eqn : Heq'. simpl in *.
             unfold _bindpi. simpl. eapply Hgb; eauto. intros t' ?.
             specialize (eutt_reta_or_div C t') as Hor. destruct Hor.
             ++ left. destruct H1 as [c Hc]. exists c. split; auto. unfold _retpi. unfold iterF_body.
                right. left. exists c. split; try reflexivity.
                eapply Hp; eauto.
             ++ right. split; auto. unfold iterF_body. left. 
                specialize (div_spin_eutt C t' H1) as H2. 
                split; try apply spin_div. eapply Hp; eauto. symmetry. auto.
          -- destruct H0. pinversion H0.
        * destruct H as [a' [? ?] ]. pclearbot. left. exists (inl a').
          split; auto. simpl. unfold _bindpi. unfold _retpi. left. exists a'. unfold id. 
          split; try reflexivity.
          unfold iterF_body. right. right. exists a'. split; try reflexivity. right.
          apply CIH. unfold _bindpi. assumption.
    - intros. generalize dependent a. pcofix CIH. intros. pfold. red.
      repeat red in H0.
      constructor.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. punfold H0. destruct H0. simpl in H.
      cbn in H. unfold bindpi, _bindpi in H. rewrite Heq in H. simpl in *. eapply Hfa; try apply H.
      intros t ?. unfold iterF_body. destruct H0.
      + destruct H0 as [ [a' | b] [? ?] ].
        * right. right. exists a'. split; auto. right. apply CIH.
          cbn in H1. unfold _bindpi in H1. unfold _retpi, id in H1. destruct H1.
           -- destruct H1 as [a'' [Ha' ?] ].
             unfold id in Ha'. apply inv_ret in Ha'. subst. unfold iterF_body in H1.
             destruct H1.
             ++ destruct H1. pinversion H1.
             ++ destruct H1.
                ** destruct H1 as [? [? ?] ]. apply inv_ret in H1. discriminate.
                ** destruct H1 as [a'' [? ?] ]. pclearbot. apply inv_ret in H1. injection H1. intros.
                   subst. assumption.
           -- destruct H1. pinversion H1.
        * right. left. exists b. split; auto. left. exists b. split; try reflexivity.
          cbn in H1. unfold bindpi, _bindpi in H1. destruct (g b) as [gb Hgb] eqn : Heq'. simpl in *.
          eapply Hgb; try apply H1. unfold _retpi. intros t' ?.
          destruct H2.
          -- destruct H2 as [c [? ?] ]. unfold iterF_body in H3. destruct H3.
             ++ destruct H3. pinversion H3.
             ++ destruct H3.
                ** destruct H3 as [c' [? ?] ]. apply inv_ret in H3. injection H3. intros. subst.
                   eapply Hp; eauto. symmetry. auto.
                ** destruct H3 as [ a'' [? _ ] ]. apply inv_ret in H3. discriminate.
          -- destruct H2. unfold iterF_body in H3. destruct H3; try destruct H3.
             ++ eapply Hp; try eapply spin_div; eauto. apply div_spin_eutt. auto.
             ++ destruct H3 as [ c [Hcontra _ ] ]. clear_ret_eutt_spin.
             ++ destruct H3 as [ a'' [Hcontra _] ]. clear_ret_eutt_spin.
     + destruct H0. unfold iterF_body in H1. left. split; auto. right.
       split; try apply spin_div. destruct H1; try tauto. destruct H1.
       * destruct H1 as [c [? _ ] ]. clear_ret_eutt_spin.
       * destruct H1 as [a'' [? _] ]. clear_ret_eutt_spin.
   Qed.
      
  (*I am sorry, I will come up for some automation for this eventually*)
  Instance PureITreeDinatural : IterDinatural (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B C. intros. constructor.
    (* can't coinduct in this case it seems, fingers crossed I don't need to *)
    - intros. cbn. unfold bindpi, _bindpi. destruct (f a) as [fa Hfa] eqn : Heq. simpl.
      cbn in H. punfold H. destruct H. cbn in H. unfold bindpi, _bindpi in H. rewrite Heq in H. simpl in *.
      eapply Hfa; try apply H. intros t ?. destruct H0.
      + destruct H0 as [ [b | c]  [? ?] ].
        * left. exists (inl b). split; auto. cbn. cbn in H1. destruct (g b ) as [gb Hgb] eqn : Heq'.
          simpl in *. pfold. constructor. cbn. unfold bindpi, _bindpi. rewrite Heq'. simpl. 
          eapply Hgb; try apply H1. intros t' ?. 
          unfold iterF_body in H2. destruct H2.
          -- right. destruct H2. split; auto.
             unfold iterF_body. left. split; auto.
             apply spin_div.
          -- destruct H2.
             ++ destruct H2 as [c [? ?] ].
                left. exists (inr c). split; auto. cbn. unfold _retpi.
                unfold iterF_body. right. left. exists c. split; auto. reflexivity.
             ++ destruct H2 as [a' [? ?] ]. left. exists (inl a'). split; auto.
                cbn. pclearbot. punfold H3. destruct H3. cbn in H3. unfold bindpi, _bindpi in H3.
                destruct (f a') as [fa' Hfa'] eqn : Heq''. simpl in *. eapply Hfa'; try apply H3.
                intros t'' ?. destruct H4.
                ** unfold iterF_body. right. destruct H4 as [ [b' | c] ? ].
                   --- destruct H4. right. exists b'. split; auto.
                       clear H. clear H3. clear Heq Heq' Heq''.
                       clear H1. left. cbn in H5.
                        generalize dependent b'. generalize dependent t''. pcofix CIH. intros.
                       (* might need some kind of coinductive hyp here *)
                       pfold. constructor. cbn in H5.
                       destruct (g b') as [gb' Hgb'] eqn : Heq. simpl in *.
                       cbn. unfold bindpi, _bindpi. rewrite Heq. simpl. eapply Hgb'; try apply H5.
                       intros t''' ?.
                       destruct H as [? | [? | ?] ].
                       +++ right. destruct H. split; auto. unfold iterF_body.
                           left. split; auto; apply spin_div.
                       +++ destruct H as [c [? ?] ]. left. exists (inr c).
                           split; auto. cbn. red. unfold iterF_body. right. left. exists c.
                           split; auto. reflexivity.
                       +++ destruct H as [a'' [? ?] ]. left. exists (inl a'').
                           split; auto. cbn. pclearbot. punfold H1.
                           destruct H1. cbn in H1. unfold bindpi, _bindpi in H1.
                           destruct (f a'') as [fa'' Hfa''] eqn : Heq'. simpl in *.
                           eapply Hfa''; try apply H1.
                           intros t4 ?. destruct H3 as [ [ [b'' | c'] ]  | [? ?] ] .
                           *** destruct H3. unfold iterF_body. right. right. exists b''.
                               split; auto. right. apply CIH with (t'' := t4); auto.
                               cbn in H6. destruct (g b'') as [gb'' Hgb''] eqn : Heq''. simpl in *.
                               eapply Hgb''; try apply H6. intros t5 ?. auto.
                           *** destruct H3. cbn in H6. unfold _retpi in H6.
                               unfold iterF_body in H6. destruct H6 as [? | [? | ?] ].
                               ++++ destruct H6. pinversion H6.
                               ++++ destruct H6 as [c'' [? ?] ]. apply inv_ret in H6.
                                    injection H6. intros. subst. unfold iterF_body.
                                    right. left. exists c'. split; auto.
                               ++++ destruct H6 as [a''' [? ?] ].  apply inv_ret in H6. discriminate.
                          *** unfold iterF_body in H6. unfold iterF_body. destruct H6 as [? | [? | ?] ].
                              ++++ left. tauto.
                              ++++ destruct H6 as [c [? ?] ].
                                   clear_ret_eutt_spin.
                              ++++ destruct H6 as [? [? ?] ]. clear_ret_eutt_spin.
                    --- cbn in H4. unfold _retpi in H4. left. exists c. destruct H4.
                        split; auto. destruct H5 as [? | [? | ?] ].
                        +++ destruct H5. pinversion H5.
                        +++ destruct H5 as [ c' [ ? ?  ] ]. apply inv_ret in H5. injection H5. intros.
                            subst. auto.
                        +++ destruct H5 as [a'' [? ?] ]. apply inv_ret in H5. discriminate.
                ** destruct H4. red. red in H5.
                   destruct H5 as [? | [? | ?] ]; try (destruct H5 as [? [? ?] ]; clear_ret_eutt_spin ).
                   left. tauto.
       * left. cbn in H1. unfold _retpi in H1. exists (inr c). split; auto.
         cbn. unfold _retpi, id. unfold iterF_body in H1. destruct H1 as [? | [? | ?] ].
         -- destruct H1. pinversion H1.
         -- destruct H1 as [c' [? ? ] ]. apply inv_ret in H1. injection H1. intros. subst. auto.
         -- destruct H1 as [a' [? _] ]. apply inv_ret in H1. discriminate.
    + destruct H0. right. split; auto. unfold iterF_body in H1. destruct H1 as [? | [? | ? ] ].
      * destruct H1. auto.
      * destruct H1 as [? [? ?] ]. clear_ret_eutt_spin.
      * destruct H1 as [? [? ?] ]. clear_ret_eutt_spin.
  - intros. generalize dependent a. pcofix CIH.
    intros. pfold. constructor. cbn. cbn in H0. unfold bindpi, _bindpi in *. 
    destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H0.
    intros t ?. clear H0. destruct H.
    + destruct H as [ [b | c] [? ?]  ].
      * left. exists (inl b). split; auto. cbn in H0. red in H0. punfold H0. destruct H0.
        cbn in H0. unfold bindpi, _bindpi in H0. destruct (g b) as [gb Hgb] eqn : Heq'.
        simpl in *. cbn. rewrite Heq'. simpl. eapply Hgb; try apply H0. clear H0. intros t' ?.
        destruct H0.
        -- unfold iterF_body. right. destruct H0 as [ [a' | c] ? ].
           ++ right. exists a'. destruct H0. split; auto. right. apply CIH.
              cbn. cbn in H1. unfold bindpi, _bindpi. destruct (f a') as [fa' Hfa'] eqn : Heq''.
              simpl in *. eapply Hfa'; try apply H1. clear H1. intros t'' ?.
              unfold iterF_body in H1. destruct H1 as [ ? | [? | ?] ]; auto.
              ** destruct H1 as [c [? ?] ]. left. exists (inr c). cbn. auto.
              ** destruct H1 as [b' [? ?] ]. left. exists (inl b'). split; auto.
                 pclearbot. cbn. assumption.
           ++ cbn in H0. unfold _retpi in H0. left. exists c.
              destruct H0. split; auto. destruct H1 as [? | [? | ?] ].
              ** destruct H1. pinversion H1.
              ** destruct H1 as [c' [? ?] ]. apply inv_ret in H1. injection H1 as ?. subst. auto.
              ** destruct H1 as [?  [? ?] ]. apply inv_ret in H1. discriminate.
        -- destruct H0. unfold iterF_body. destruct H1 as [ ? | [? | ?] ]; 
                                             try tauto; destruct H1 as [? [? ?] ]; clear_ret_eutt_spin.
     * cbn in H0. unfold _retpi, id in H0. left. exists (inr c). split; auto.
       cbn. red. red. right. left. exists c. split; auto; try reflexivity.
   + right. destruct H. split; auto. red. left. split; auto. apply spin_div.
  Qed.

  Definition bind_inl_id {A B} : Kleisli PureITreeSpec (A + (A + B)) (A + B) :=
    fun x => match x with
               | inl a => ret (inl a)
               | inr b => ret b end.

  Definition _iterF_body_bot {A B : Type} (f : A -> PureITreeSpec (A + B )) (a : A) :=
    fun p Hp => iterF_body f a p Hp bot4.

  Lemma f_leq_iter_f : forall (A B : Type) (f : Kleisli (PureITreeSpec) A (A + (A + B)) ) (a : A),
                              f a >>= bind_inl_id <≈ iter f a.
  Proof.
    intros A B f a p Hp Hf. cbn. unfold bindpi, _bindpi, bind_inl_id.
    punfold Hf. destruct Hf. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H.
    intros t Ht. destruct Ht as [? | [? | ?] ]; auto.
    - destruct H0 as [b [? ?] ]. left. exists (inr b). split; auto.
    - destruct H0. destruct H0 as [H1 Hco]. left. exists (inl x). split; auto. unfold retpi, _retpi. simpl.
      pclearbot. fold (@_iter A (A + B)) in Hco.
    Abort.
    (*
    generalize dependent a. pcofix CIH. intros. cbn in Hf. unfold bind_inl_id, bindpi, _bindpi in Hf. 
    destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. pfold. constructor. rewrite Heq.
    simpl. unfold iterF_body. eapply Hfa; try apply Hf. intros t Ht. simpl in Ht.
    destruct Ht as [Ht | Ht]; auto. right. destruct Ht as [ [a' | [a' | b] ] [ ? ?] ].
    - simpl in *. unfold _retpi in H0. right. exists a'. split; auto. right. apply CIH.
      unfold bindpi, _bindpi, bind_inl_id. destruct (f a') as [fa' Hfa'] eqn : Heq'. simpl.
    - simpl in *. unfold _retpi in H0. left. exists (inl a'). split; auto.
    - simpl in *. unfold _retpi in H0. left. exists (inr b). split; auto.
   *)
  Instance PureITreeIterCodiagonal : IterCodiagonal (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B f. constructor.
    - intros. generalize dependent a. pcofix CIH. intros. cbn in H0. punfold H0.
      pfold. destruct H0. constructor. cbn in H. cbn. punfold H.  destruct H. 
      unfold bindpi, _bindpi. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H.
      intros t ?. destruct H0 as [? | [? | ?] ].
      + destruct H0. destruct H1 as [? | [? | ?] ].
        * destruct H1. right. split; auto. unfold iterF_body. left. auto.
        * destruct H1 as [? [? ?] ]. clear_ret_eutt_spin.
        * destruct H1 as [ ? [? ?] ]. clear_ret_eutt_spin.
      + destruct H0 as [ [a' | b] [? ?] ].
        * left. exists (inr (inl a')). split; auto. cbn. unfold _retpi. destruct H1 as [? | [? | ? ] ].
          -- destruct H1. pinversion H1.
          -- destruct H1 as [? [? ?] ]. apply inv_ret in H1. discriminate.
          -- destruct H1 as [a'' [? ?] ]. apply inv_ret in H1. injection H1. intros. subst.
             pclearbot. unfold iterF_body. right. right. exists a'. unfold id. split; try reflexivity.
             right. apply CIH. auto.
        * destruct H1 as [? | [? | ?] ].
          -- destruct H1. pinversion H1.
          -- destruct H1 as [b' [? ?] ]. apply inv_ret in H1. injection H1. intros. subst.
             left. exists (inr (inr b) ). split; auto. cbn. unfold _retpi. red.
             right. left. exists b. split; auto; reflexivity.
          -- destruct H1 as [? [? ?] ]. apply inv_ret in H1. discriminate.
     + destruct H0 as [a' [? ?] ]. pclearbot. punfold H1. destruct H1. 
       left. exists (inl a'). split; auto.  cbn. unfold _retpi. cbn. 
       right. right. exists a'. split; try reflexivity. right. apply CIH.
       unfold _iter. pfold. red. constructor. cbn. pfold. red. constructor.
       destruct (f a') as [fa' Hfa'] eqn : Heq'. simpl in *. 
       eapply Hfa'; try apply H1. intros t' ?. unfold iterF_body. destruct H2 as [ ? | [? | ?] ].
       * left. destruct H2. split; auto.
       * right. destruct H2 as [ [a'' | b] [? ?]  ].
         -- left. exists (inl a''). split; auto.
         -- left. exists (inr b). split; auto.
       * destruct H2 as [a'' [? ?] ]. pclearbot.
         right. right. exists a''. split; auto.
         left. unfold iterF_body in H3. auto.
         (*annoying to see but effectively assumption with extra steps*)
         destruct (iter f a'') as [ifa Hifa] eqn : Heq''. unfold iter in Heq''. injection Heq'' as Heq'''.
         unfold _iter in Heq'''. rewrite Heq'''. rewrite Heq''' in H3. eapply Hifa; try apply H3.
         auto.
         (* I think there might be something odd going on here*)
    - 


      intros. punfold H. generalize dependent a.  pcofix CIH. intros.  cbn in H0. pfold. constructor.
      destruct H0. cbn in H. cbn.  unfold bindpi, _bindpi in H. pfold. constructor.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H. 
      rename H into Ha.
      intros t ?. destruct H.
      + destruct H as [ [a' | [a' | b] ] ?  ].
        * destruct H. cbn in H0. unfold _retpi in H0. destruct H0 as [?|  [? | ?] ].
          -- destruct H0. pinversion H0.
          -- destruct H0 as [b [? ?] ]. apply inv_ret in H0. discriminate.
          -- destruct H0 as [a'' [? ?] ]. apply inv_ret in H0. injection H0. intros. subst.
             pclearbot.
             unfold iterF_body. right. right. exists a'. split; auto. left. 
             pfold. punfold H1. constructor. destruct H1. cbn in H1. unfold bindpi, _bindpi in H1.
             destruct (f a') as [fa' Hfa'] eqn : Heq'. simpl in *. eapply Hfa'; try apply H1. clear H1.
             intros t' ?. cbn in H1. destruct H1.
             ++ destruct H1 as [ [a'' | [a'' | b] ] ?  ].
                ** cbn in H1. unfold _retpi in H1. cbn in H1.  destruct H1.
                   red in H2.  destruct H2 as [? | [? | ?] ] .
                   --- destruct H2. pinversion H2.
                   --- destruct H2 as [b [? ?] ]. apply inv_ret in H2. discriminate.
                   --- destruct H2 as [a''' [? ?] ]. pclearbot. apply inv_ret in H2.
                       injection H2 as H2. subst. red. right. right. exists a''. split; auto.
                       left. (* pcofix CIH'. *)
                       pfold. punfold H3. destruct H3. cbn in H2. 
                       unfold bindpi, _bindpi in H2. red. constructor.
                       destruct (f a'') as [fa'' Hfa''] eqn : Heq''. simpl in *. eapply Hfa'';
                                                                                   try apply H2.
                       intros t''. simpl. intros. destruct H3 as [ [ [a''' |  [a''' | b] ]  ?] | ?]. 
                       +++ cbn in H3. unfold _retpi in H3. destruct H3.
                            red in H4. destruct H4 as [? | [? | ?] ].
                            *** destruct H4. pinversion H4.
                            *** destruct H4 as [? [? ?] ]. apply inv_ret in H4 as H4. discriminate.
                            *** destruct H4 as [a4 [? ?] ]. apply inv_ret in H4. injection H4 as H4. subst.
                                pclearbot. red. punfold H5. destruct H5. cbn in H4. unfold bindpi, _bindpi in H4.
                                right. right. exists a'''. split; auto. left. pfold. constructor.
                                destruct (f a''') as [fa''' Hfa'''] eqn : Heq'''. simpl in *. eapply Hfa'''; try apply H4.
                                intros t''' ?. simpl in H5. destruct H5 as [ [ [a4 | b] ? ]  | ?].
                                ---- cbn in H5. unfold _retpi in H5. destruct H5.
                                     right. right. exists a4. split; auto. left. pfold.
                                     red in H6.
                                     constructor. destruct (f a4) as [fa4 Hfa4] eqn : Heq4.
                                     destruct H6 as [? | [? | ?] ].
                                     ++++ destruct H6. pinversion H6.
                                     ++++ destruct H6 as [? [? ?] ]. apply inv_ret in H6. discriminate.
                                     ++++ destruct H6 as [a5 [? ?] ]. pclearbot. apply inv_ret in H6. injection H6 as H6.
                                          subst. simpl. punfold H7. destruct H7. cbn in H6. unfold bindpi, _bindpi in H6.
                                          rewrite Heq4 in H6. simpl in *. eapply Hfa4; try apply H6.
                                          intros t4 Ht4. destruct Ht4.
                                          **** destruct H7 as [ [a5 | [a5 | b] ] [ ? ?] ].
                                               ----- cbn in H8. unfold _retpi in H8. unfold iterF_body.
            (*                                   
                       cbn. clear H2.
                       right. right. exists a''
                       +++ apply inv_ret in H2. discriminate.
                       +++  pclearbot. punfold H3. apply inv_ret in H2. injection H2 as H2. subst.
                           red in H3. destruct H3. cbn in H2. unfold bindpi, _bindpi in H2.
                           unfold iterF_body. right. right. exists a''. split; auto.
                           left. pfold. constructor. destruct (f a'') as [fa'' Hfa''] eqn : Heq''.
                           simpl in *. eapply Hfa''; try apply H2. intros t'' ?.
                           unfold iterF_body.
                           destruct H3. right.
                           *** destruct H3 as [ [ a4 | [a4 |b ] ]  [? ?] ].
                               ---- right. exists a4. split; auto. cbn in H4. unfold _retpi in H4.

                   right. right. exists a''. split; auto.
                   left. pfold. constructor. unfo
             left.
            

             right. right. exists a'. split; auto. left.
             pfold. punfold H1. constructor. destruct H1. cbn in H1. unfold bindpi, _bindpi in H1.
             destruct (f a') as [fa' Hfa'] eqn : Heq'. simpl in *. eapply Hfa'; try apply H1.
             intros t' ?. destruct H2.
             ++ destruct H2 as [ [ a'' | [a'' | b] ] ? ].
                ** cbn in H2. unfold _retpi in H2. destruct H2.
                   unfold iterF_body. right. right. exists a''. split; auto.
                   left. pcofix CIH'. *)
         Admitted.


  (*Definition of effect observation from pure itrees into pure itree specs *)
  Definition _obsip A (t : itree Void A) : _PureITreeSpec A := fun p _ => p t.
(*
  Definition f A : A -> itree Void nat := fun (a : A) => ret 2.

  Lemma ex : forall p Hp, _obsip nat (bind spin f) p Hp.
    intros. unfold _obsip. *)

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

  Instance StateITreeEffectObs : EffectObs (fun A => S -> itree Void (A * S) ) (StateITreeSpec):=
    obssi.

  Program Instance StateITreeMonadMorphism : MonadMorphism (fun A => S -> itree Void (A * S)) StateITreeSpec StateITreeEffectObs.
  Next Obligation. apply obssi_pres_ret. Qed.
  Next Obligation. apply obssi_pres_bind. Qed.


  Definition _encode A (post : itree Void (A * S) -> Prop ) (Hpost : resp_eutt _ _ post) (pre : S -> Prop) : _StateITreeSpec A :=
    fun p Hp s => pre s /\ forall t, post t -> p t.

  Lemma encode_monot : forall A post Hpost pre, monotonicsi A ( _encode A post Hpost pre).
  Proof.
    intros. intro. intros. unfold _encode in *. destruct H0. split; auto.
  Qed.

  Definition encode A post Hpost pre :=
    exist _ (_encode A post Hpost pre) (encode_monot A post Hpost pre).


   
End StateITree.
  Local Open Scope nat_scope.

  Lemma is_n_resp_eutt :forall (n : nat), resp_eutt Void _ (fun t => t ≈ ret (tt,n) ).
  Proof.
    intros n t1. intros. rewrite H. tauto.
  Qed.
  
  Definition skip_if_4_spec := encode nat unit (fun t => t ≈ ret (tt, 4)) (is_n_resp_eutt 4) (fun n => n = 4).

  Definition diverge_if_not_4 := fun n => if (n =? 4) then ret (tt, 4) else @spin Void _.

  Lemma m_sats_skip_spec : DijkstraProp (fun A => nat -> itree Void (A * nat)) (StateITreeSpec nat) (StateITreeEffectObs nat ) unit skip_if_4_spec diverge_if_not_4.
  Proof.
    unfold DijkstraProp. intros p Hp. intros. unfold skip_if_4_spec, diverge_if_not_4  in *. simpl in *. unfold _encode, _obssi in *.
    destruct H. rewrite H. rewrite Nat.eqb_refl. apply H0. reflexivity.
  Qed.

  Definition inc_if_4_spec := encode nat unit (fun t => t ≈ ret (tt, 4)) (is_n_resp_eutt 4) (fun n => n = 5).

  Lemma e2 : ~ ( DijkstraProp (fun A => nat -> itree Void (A * nat) )  (StateITreeSpec nat) 
                              (StateITreeEffectObs nat) unit inc_if_4_spec diverge_if_not_4). 
  Proof.
    unfold DijkstraProp. intro Hcontra. repeat red in Hcontra. unfold inc_if_4_spec, diverge_if_not_4, _encode in Hcontra. simpl in *.
    unfold _encode in *. 
    set (p' := fun t : itree Void (unit * nat) => t ≈ ret (tt, 4) ). 
    assert (resp_eutt _ _ p').
    {
       unfold p'. intros t1 t2. intros. rewrite H. tauto.
    }
     specialize ( Hcontra p' H 5). simpl in *. unfold p' in Hcontra. 

    enough (ret (tt,4) ≈ @spin Void (unit * nat)).
    - specialize (spin_div Void (unit * nat)) as H1. rewrite <- H0 in H1. pinversion H1.
    - symmetry. eapply Hcontra; eauto.
  Qed.
  (* going to want some machinery for aiding in the disproving of dijkstra triples  *)


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
