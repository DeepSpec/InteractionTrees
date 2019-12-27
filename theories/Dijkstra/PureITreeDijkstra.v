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
     Dijkstra.PureITreeBasics
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

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

  Lemma cont_a_pred_resp_eutt : forall A B 
                                       ( F : A -> Prop ),
      resp_eutt Void ( A + B) (fun (t : itree Void (A + B)) => exists a' , ret (inl a') ≈ t /\ F a'  ).
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

  Definition iterF_body' {A B : Type} 
            (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : A -> Prop ) :=
    fun (t : itree Void (A + B) ) =>( divergence t /\ p spin ) \/
                                    (exists b, ret (inr b) ≈ t /\ p (ret b)  ) \/
                                    (exists a', ret (inl a') ≈ t /\ F a').

  Variant iterF_body {A B : Type}  
            (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : A -> Prop )
            (t : itree Void (A + B)) : Prop :=
    | inf_tau (Ht: divergence t) (Hspin : p spin)
    | term_b (b : B) (Hretb : ret (inr b) ≈ t ) (Hb : p (ret b)) 
    | cont_a (a' : A) (Hreta : ret (inl a') ≈ t) (Hcorec : F a')
.

 Lemma iterF_body_equiv : forall A B 
            (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : A -> Prop )
            (t : itree Void (A + B)), iterF_body p Hp F t <-> iterF_body p Hp F t.
   Proof.
     split; intros; auto.
   Qed.

Hint Constructors iterF_body.

  Lemma iterF_body'_resp_eutt : forall (A B : Type) 
            (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : A -> Prop ),
      resp_eutt _ _ (iterF_body' p Hp F).
  Proof.
    intros. eapply resp_eutt_or; try eapply resp_eutt_or; intros.
    - apply inf_tree_pred_resp_eutt.
    - apply term_b_pred_resp_eutt.
    - apply cont_a_pred_resp_eutt. 
  Qed.

  Lemma iterF_body_resp_eutt :forall (A B : Type)
            (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)  (F : A -> Prop ),
      resp_eutt _ _ (iterF_body p Hp F).
  Proof.
    intros. intros t1 t2 Heutt. split; intros; inversion H; subst; auto.
    - apply inf_tau; auto. rewrite Heutt in Ht. auto.
    - eapply term_b; eauto. rewrite Hretb. auto.
    - eapply cont_a; eauto. rewrite Hreta. auto.
    - apply inf_tau; auto. rewrite Heutt. auto.
    - eapply term_b; eauto. rewrite Hretb. symmetry. auto.
    - eapply cont_a; eauto. rewrite Hreta. symmetry. auto.
  Qed.

  

  Variant iterF {A B : Type} (body : A -> PureITreeSpec (A + B))
          (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt Void B p) (F : A -> Prop ) : Prop :=
    | iterF_con : proj1_sig (body a) (iterF_body p Hp F) (iterF_body_resp_eutt A B p Hp F) -> iterF body a p Hp F.

Hint Constructors iterF.
Lemma iterF_monotone {A B} (body:  (A -> PureITreeSpec (A + B))) 
      (sim sim' : A -> Prop) (a : A)
      (p : itree Void B -> Prop) (Hp : resp_eutt Void B p)
      (IN : iterF body a p Hp sim) (LE : sim <1= sim'):
  iterF body a p Hp sim'.
  Proof.
    induction IN; constructor; auto.
    destruct (body a) as [fa Hfa] eqn : Heq. simpl in *.
    eapply Hfa; try apply H. intros. inversion H0; eauto.
  Qed.

  Definition iter_ {A B} sim (body : A -> PureITreeSpec (A + B)) a p Hp : Prop :=
    iterF body a p Hp sim.
  Hint Unfold iter_.

  Lemma iterF_monotone' {A B} body p Hp : monotone1 (fun sim a => @iter_ A B sim body a p Hp).
  Proof.
    do 2 red. intros. eapply iterF_monotone; eauto.
  Qed.

  Hint Resolve iterF_monotone' : paco.

  Definition _iter {A B} :=
    fun (f : A -> PureITreeSpec (A + B) ) (a : A) (p : itree Void B -> Prop) (Hp : resp_eutt _ _ p) => 
      paco1 (fun (F : A -> Prop) a => @iter_ A B F f a p Hp ) bot1 a.

  

  Lemma iter_monot : forall A B (f : A -> PureITreeSpec (A + B) ) (a : A),
                              monotonici B (_iter f a).
    Proof.
      unfold monotonici. intros. generalize dependent a.
      pcofix CIH. pfold. intros. punfold H1.
      red. red in H1. inversion H1; simpl in *.
      constructor. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *.
      eapply Hfa; try apply H0. intros t. intros. inversion H2; subst; eauto.
      pclearbot. eapply cont_a; eauto.
    Qed.

  Definition iterp {A B} (body : A -> PureITreeSpec (A + B) ) (init : A) : PureITreeSpec B :=
    exist _ (_iter body init) (iter_monot A B body init).

(*there may be a way to reason about iteration in spec monads *)



  (*Monad equivalence relation for PureITreeSpec monad *)
  Global Instance PureITreeSpecEq : EqM PureITreeSpec :=
    fun A w1 w2 => forall (p : itree Void A -> Prop) (Hp : resp_eutt Void A p), proj1_sig w1 p Hp <-> proj1_sig w2 p Hp.
 
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

  Instance PureITreeIter : Iter (Kleisli PureITreeSpec) sum := @iterp.

 
  Lemma not_ret_eutt_spin : forall A E (a : A), ~ (Ret a ≈ @spin E A).
  Proof.
    intros. intro Hcontra. simpl in Hcontra. specialize (spin_div E A) as Hdiv. rewrite <- Hcontra in Hdiv.
    pinversion Hdiv.
  Qed.


  Ltac clear_ret_eutt_spin :=
    match goal with | H : ret ?a ≈ spin  |- _ => simpl in H; exfalso; eapply not_ret_eutt_spin; eauto
                    | H : Ret ?a ≈ spin  |- _ => exfalso; eapply not_ret_eutt_spin; eauto
                    | H : spin ≈ ret ?a  |- _ => exfalso; symmetry in H; eapply not_ret_eutt_spin; eauto
                    | H : divergence (ret _ ) |- _ => pinversion H
                    end.
  
  Ltac invert_evidence :=
    intros; repeat match goal with 
                   | H : _ /\ _ |- _ => destruct H
                   | H : _ \/ _ |- _ => destruct H 
                   | H : iterF_body _ _ _ _ |- _ => inversion H; clear H; subst
                   | H : exists a : ?A, _ |- _ => destruct H as [?a ?H]
                   | x : ?A + ?B |- _ => destruct x as [?a | ?b]
                   | H : upaco1 _ _ _ |- _ => pclearbot
           end.

  Ltac invert_ret := simpl in *; match goal with | H : Ret ?a ≈ Ret ?b |- _ => 
                                                   apply inv_ret in H; try discriminate; try (injection H as H);
                                                   subst end.


  Ltac basic_solve := invert_evidence; try clear_ret_eutt_spin; try invert_ret.

  Instance PureITreeIterUnfold : IterUnfold  (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B f a.
    constructor.
    (*this case went through without even needing coinduction???*)
    - intros. red. repeat red in H. punfold H. destruct H.
      cbn. unfold bindpi, _bindpi. destruct (f a) as [fa Hfa]; simpl in *.
      eapply Hfa; eauto. intros t ?Ht. inversion Ht; eauto.
      + left. exists (inr b). split; auto.
      + left. exists (inl a'). split; auto. pclearbot. auto.
    (*very suspicious that I no longer need to coinduct, I think I will move this onto a refactor branch to experiment on*)
    - revert a. (* pcofix CIH. *) intros. cbn in H. pfold. unfold bindpi, _bindpi in H.
      constructor. destruct (f a) as [fa Hfa]; simpl in *. eapply Hfa; try apply H.
      intros t ?Ht. simpl in Ht. basic_solve; auto.
      + eapply cont_a; try apply H0. cbn in H1.
        red in H1. auto.
      + eapply term_b; try apply H0. auto.
  Qed.

  Instance PureITreeIterNatural : IterNatural (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B C. intros. constructor.
    - intros. generalize dependent a. pcofix CIH. intros. pfold. repeat red in H. 
      punfold H0. destruct H0.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. constructor.
      cbn. rewrite Heq. simpl. unfold _bindpi. eapply Hfa; eauto.
      intros t ?Ht. basic_solve.
      + right. split; auto. apply inf_tau; auto. apply spin_div.
      + left. exists (inr b). split; auto. cbn. unfold bindpi, _bindpi. simpl.
        destruct (g b) as [gb Hgb] eqn : Heq'. simpl in *. eapply Hgb; try apply H1. intros ?t ?Ht.
        clear H. specialize (eutt_reta_or_div C t0) as Hor. basic_solve.
        * left. exists a0. unfold _retpi. split; auto. eapply term_b; try reflexivity. eapply Hp; eauto.
        * right. split; auto. eapply inf_tau; try apply spin_div. eapply Hp; eauto. symmetry. apply div_spin_eutt. auto.
      + left. exists (inl a'). split; auto. cbn. unfold _bindpi, _retpi, id. left. exists a'.
        split; try reflexivity. eapply cont_a; try reflexivity. right. apply CIH; auto.
    - intros. generalize dependent a. pcofix CIH. intros. pfold. red.
      repeat red in H0.
      constructor.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. punfold H0. destruct H0. simpl in H.
      cbn in H. unfold bindpi, _bindpi in H. rewrite Heq in H. simpl in *. eapply Hfa; try apply H.
      intros t ?. simpl in *. basic_solve.
      + cbn in H1. unfold _bindpi, _retpi in H1. basic_solve. unfold id in *. basic_solve.
        eapply cont_a; eauto. auto.
      + cbn in H1. unfold bindpi, _bindpi in H1. eapply term_b; try apply H0.
        left. exists b. split; try reflexivity. destruct (g b) as [gb Hgb] eqn : Heq'.
        simpl in *. eapply Hgb; try apply H1. intros ?t ?Ht. simpl in *. basic_solve.
        * unfold _retpi in H3. basic_solve. eapply Hp; eauto. symmetry. auto.
        * apply div_spin_eutt in H2. eapply Hp; eauto.
      + apply inf_tau; auto. right. split; auto. apply spin_div.
   Qed.
      
  (*I am sorry, I will come up for some automation for this eventually*)
  Instance PureITreeDinatural : IterDinatural (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B C. intros. constructor.
    (* can't coinduct in this case it seems, fingers crossed I don't need to *)
    - intros. cbn. unfold bindpi, _bindpi. destruct (f a) as [fa Hfa] eqn : Heq. simpl.
      cbn in H. punfold H. destruct H. cbn in H. unfold bindpi, _bindpi in H. rewrite Heq in H. simpl in *.
      eapply Hfa; try apply H. intros t ?. simpl in H0.
      basic_solve; auto.
      + rename a0 into b. left. exists (inl b). split; auto. cbn. cbn in H1. clear H. clear H0.
        generalize dependent b. pcofix CIH.
        intros. pfold. constructor. cbn. unfold bindpi, _bindpi.
        destruct (g b) as [gb Hgb] eqn : ?Heq. simpl in *. eapply Hgb; try apply H1.
        intros ?t ?Ht. basic_solve.
        * right. split; auto. apply inf_tau; auto. apply spin_div.
        * rename b0 into c. left. exists (inr c). split; auto. cbn. unfold _retpi.
          eapply term_b; eauto. reflexivity.
        * left. exists (inl a'). split; auto. cbn. punfold Hcorec. destruct Hcorec. cbn in H.
          unfold bindpi, _bindpi in H. destruct (f a') as [fa' Hfa'] eqn :?Heq. simpl in *.
          eapply Hfa'; try apply H. intros ?t ?Ht. simpl in *. basic_solve.
          -- cbn in H2. rename a0 into b'. eapply cont_a; eauto. auto.
          -- cbn in H2. rename b0 into c. unfold _retpi in H2. basic_solve.
             eapply term_b; try apply Hb. auto.
          -- apply inf_tau; auto.
      + cbn in H1. unfold _retpi in H1. basic_solve. rename b into c. left.
        exists (inr c). auto.
  - intros. generalize dependent a. pcofix CIH.
    intros. pfold. constructor. cbn. cbn in H0. unfold bindpi, _bindpi in *. 
    destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H0.
    intros t ?. simpl in *. basic_solve.
    + rename a0 into b. left. exists (inl b). split; auto. cbn. cbn in H1. red in H1.
      punfold H1. destruct H1. cbn in H1. unfold bindpi, _bindpi in H1. destruct (g b) as [gb Hgb] eqn : ?Heq.
      simpl in *. eapply Hgb; try apply H1. intros ?t ?Ht. simpl in *. clear H1.
      basic_solve.
      * cbn in H2. eapply cont_a; try apply H1. right. apply CIH. cbn.
        unfold bindpi, _bindpi. destruct (f a0) as [fa0 Hfa0] eqn : ?Heq. simpl in *.
        eapply Hfa0; try apply H2. intros ?t ?Ht. basic_solve; auto.
        -- rename b0 into c. left. exists (inr c). split; auto.
        -- rename a' into b'. left. exists (inl b'). split; auto.
      * cbn in H2. unfold _retpi in H2. basic_solve.
        rename b0 into c. eapply term_b; try apply Hb. auto.
      * apply inf_tau; auto.
    + cbn in H1. unfold _retpi, id in H1. left. rename b into c. exists (inr c). split; auto.
      cbn. unfold _retpi. eapply term_b; eauto. reflexivity. 
    + right. split; auto. apply inf_tau; auto. apply spin_div.
  Qed.

  Instance PureITreeIterCodiagonal : IterCodiagonal (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B f. constructor.
    - intros. generalize dependent a. pcofix CIH. intros. cbn in H0. punfold H0.
      pfold. destruct H0. constructor. cbn in H. cbn. punfold H.  destruct H. 
      unfold bindpi, _bindpi. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H.
      intros t ?. simpl in *. basic_solve.
      + right. split; auto.
      + left. exists (inr (inr b) ). split; auto. clear H. cbn. unfold _retpi.
        eapply term_b; try apply Hb0. reflexivity.
      + left. exists (inr (inl a0) ). clear H. split; auto. cbn. unfold _retpi. 
        eapply cont_a; unfold id; try reflexivity. right. apply CIH. apply Hcorec.
      + left. exists (inl a'). split; auto. cbn. unfold _retpi. 
        eapply cont_a; try reflexivity. clear H. right. apply CIH. red. pfold.
        red. constructor. punfold Hcorec. red in Hcorec. destruct Hcorec. destruct (f a') as [fa' Hfa'] eqn : ?Heq.
        simpl in *. red. pfold. constructor. rewrite Heq0. simpl in *.
        eapply Hfa'; try apply H. clear H. intros ?t ?Ht. auto.
    - intros. punfold H. generalize dependent a. pcofix CIH. intros. cbn in H0. pfold. constructor.
      destruct H0. cbn in H. cbn.  unfold bindpi, _bindpi in H. pfold. constructor.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H. 
      rename H into Ha.
      intros t ?. simpl in *. basic_solve.
      + cbn in H0. unfold _retpi in H0. basic_solve. eapply cont_a; try apply H. 
        clear H.  left.
        generalize dependent a0.
        pcofix CIH'. intros. pfold. constructor. clear Ha. punfold Hcorec.
        destruct Hcorec. cbn in H. unfold bindpi, _bindpi in H. simpl in *. 
        destruct (f a0) as [fa0 Hfa0] eqn : ?Heq. simpl in *. eapply Hfa0; try apply H.
        clear H. intros ?t ?Ht. simpl in *. basic_solve.
        * cbn in H0. unfold _retpi in H0. basic_solve. eapply cont_a; try apply H. auto.
        * cbn in H0. unfold _retpi in H0. basic_solve. eapply term_b; try apply H. eapply cont_a; try reflexivity. 
          right. apply CIH. punfold Hcorec.
        * cbn in H0. unfold _retpi, id in H0. basic_solve. eapply term_b; try apply H. 
          eapply term_b; try reflexivity. auto.
        * apply inf_tau; auto.
      + cbn in H0. unfold _retpi, id in H0. basic_solve. eapply term_b; try apply H. eapply cont_a; try reflexivity.
        right. apply CIH. punfold Hcorec.
      + cbn in H0. unfold _retpi, id in H0. basic_solve. eapply term_b; try apply H. eapply term_b; try reflexivity.
        auto.
      + apply inf_tau; auto.
   Qed.

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

    
  Lemma obsip_eutt : forall A (t1 t2 : itree Void A), t1 ≈ t2 <-> obsip A t1 ≈ obsip A t2.
  Proof.
    split; intros; unfold obsip, _obsip in *; simpl in *.
    - intros p Hp. simpl. split; intros; eapply Hp; eauto.
      symmetry. auto.
    - set (fun t => t ≈ t1) as p. 
      assert (Hp : resp_eutt _ _ p).
      + intros t3 t4. unfold p. split; intros.
        * rewrite <- H1. symmetry. auto.
        * rewrite H0. auto.
      + specialize (H p Hp). simpl in *. unfold p in H. symmetry. apply H. reflexivity.
  Qed.


  Lemma obsip_pres_iter_right : forall A B (f : A -> itree Void (A + B) ) (a : A)
            (p : itree Void B -> Prop) (Hp : resp_eutt Void B p),
     proj1_sig (obsip B (iter f a)) p Hp -> proj1_sig (iterp (fun x => obsip _ (f x) ) a) p Hp.
  Proof.
    intros. generalize dependent a. pcofix CIH. intros. pfold. constructor.
    cbn. red.
    simpl. specialize (unfold_iter_ktree f a) as Hunfold.
    cbn in H0. red in H0. symmetry in Hunfold. eapply Hp in H0; 
                                                 try (rewrite <- Hunfold; reflexivity).
    specialize (eutt_reta_or_div _ (f a) ) as [Hret | Hdiv]; basic_solve.
    - eapply cont_a; try apply Hret. right. apply CIH. cbn. red. eapply Hp; eauto. rewrite <- Hret.
        match goal with | |- _ ≈ ITree.bind _ ?g => 
                          specialize (bind_ret (inl a0) g) as Hbind_ret end.  rewrite Hbind_ret.
        rewrite tau_eutt. reflexivity.
    - eapply term_b; try apply Hret. eapply Hp; eauto.
      rewrite <- Hret. match goal with | |- _ ≈ ITree.bind _ ?g =>
                              specialize (bind_ret (inr b) g) as Hbind_ret end.
        rewrite Hbind_ret. reflexivity.
    - apply div_spin_eutt in Hdiv as Hspin. apply inf_tau; auto.
      eapply Hp; eauto. rewrite Hspin. apply spin_bind.
   Qed.

  Ltac proof_by_contra := match goal with | |- ?P => destruct (classic P) as [ ? | Hcontra];
                                                     auto end.

  Lemma obsip_pres_iter_left : forall A B (f : A -> itree Void (A + B) ) (a : A)
                             (p : itree Void B -> Prop) (Hp : resp_eutt Void B p),
      proj1_sig (iterp (fun x => obsip _ (f x) ) a) p Hp -> proj1_sig (obsip B (iter f a)) p Hp.
  Proof. (*
    intros. cbn. red. cbn in H. red in H. cbn in H.
    punfold H. destruct H. cbn in H. red in H. 
    basic_solve; auto.
    - apply div_spin_eutt in H as H1. eapply Hp; eauto.
      specialize (unfold_iter_ktree f a) as Hunfold. rewrite Hunfold. rewrite H1.
      symmetry. apply spin_bind.
    - rename H into Hretb. rename H0 into Hb. specialize (unfold_iter_ktree f a) as Hunfold.
      eapply Hp; eauto. rewrite Hunfold. rewrite <- Hretb.
      match goal with | |- ITree.bind _ ?g ≈ _ => specialize (bind_ret (inr b) g) 
      as Hbind_ret end. simpl in *. rewrite Hbind_ret. reflexivity.
    - specialize (unfold_iter_ktree f a) as Hunfold. eapply Hp; eauto;
      try (rewrite Hunfold; reflexivity). 
      (* assert (_iter (fun x : A=> obsip (A + B) (f x) ) a'  p Hp); auto. *)
      eapply Hp; eauto.
      + rewrite <- H. match goal with | |- ITree.bind _ ?g ≈ _ => 
                                             specialize (bind_ret (inl a') g) as Hbind_ret end.
        rewrite Hbind_ret. reflexivity. 
      + (* I have unfolded in some sense, I want to have a coinductive hyp here *) *)
   (* red in H.
    assert (KTree.iter f a ≈ iter f a \/ KTree.iter f a ≈ iter f a).
    - pcofix CIH. 
    Abort.



 punfold H. destruct H. cbn in H. red in H. 
    destruct H as [? | [? | ?] ].
    - destruct H. apply div_spin_eutt in H as H1. eapply Hp; eauto.
      specialize (unfold_iter_ktree f a) as Hunfold. rewrite Hunfold. rewrite H1.
      symmetry. apply spin_bind.
    - destruct H as [b [Hretb  Hb ] ]. specialize (unfold_iter_ktree f a) as Hunfold.
      eapply Hp; eauto. rewrite Hunfold. rewrite <- Hretb.
      match goal with | |- ITree.bind _ ?g ≈ _ => specialize (bind_ret (inr b) g) 
      as Hbind_ret end. rewrite Hbind_ret. reflexivity.
    - 
    exfalso. apply Hcontra. exfalso *)
  Abort.

  (*Other direction is odd, because I can't just straightforwardly coinduct*)

  Lemma obsip_pres_iter : forall A B (f : A -> itree Void (A + B) ) (a : A),
        obsip _ (iter f a) ≈ iterp (fun (x : A) => obsip (A + B) (f x) ) a.
  Proof.
    intros. constructor.
    -  apply obsip_pres_iter_right.
    - intros. cbn. red. cbn in H. unfold obsip, _obsip in H. simpl in H.
      red in H. punfold H. destruct H. simpl in *.
      cbn in H.
  Abort.

  Instance PureITreeEffectObs : EffectObs (itree Void) (PureITreeSpec) := obsip.

  Instance PureITreeMorph : MonadMorphism (itree Void) (PureITreeSpec) PureITreeEffectObs.
  Proof.
    constructor.
    - apply obsip_pres_ret.
    - apply obsip_pres_bind.
  Qed.

End PureITree.
