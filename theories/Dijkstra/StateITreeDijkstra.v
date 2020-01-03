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

Section StateITree.
  Context (S : Type).
  
  Definition StateITree A := itree (stateE S) A.

  Definition _StateITreeSpec A := forall (p : itree Void (S * A) -> Prop), resp_eutt Void (S * A) p -> S -> Prop.

  Definition monotonicsi A (w : _StateITreeSpec A) := forall (p p' : itree Void (S * A) -> Prop) 
                                                             Hp Hp' s, (forall t, p t -> p' t) -> w p Hp s -> w p' Hp' s.

  Definition StateITreeSpec A := {w : _StateITreeSpec A | monotonicsi A w}.

  Definition _retsi A (a : A) : _StateITreeSpec A := fun p _ s => p (ret (s,a)).

  Lemma monot_retsi : forall A (a : A), monotonicsi A (_retsi A a).
    Proof.
      intros. unfold _retsi. intros p p' _ _ s. intros. apply H. auto.
    Qed.

  Definition retsi A (a : A) : StateITreeSpec A := exist _ (_retsi A a) (monot_retsi A a).

  Lemma bindsi_pred_eutt : forall A B (f : A -> _StateITreeSpec B) 
                                  (p : itree Void (S * B) -> Prop) (Hp : resp_eutt Void _ p), 
         resp_eutt Void _ (fun t => (exists a s', ret (s',a) ≈ t /\ f a p Hp s') \/ divergence t /\ p spin).
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
    fun (p : itree Void (S * B) -> Prop) (Hp : resp_eutt _ _ p) (s : S) =>
      w (fun t=> (exists a s', ret (s',a) ≈ t /\ f a p Hp s' )  \/ 
                                         (divergence t /\ p spin) )  
        (bindsi_pred_eutt A B f p Hp) s.

  Lemma monot_bindsi : forall A B (w : _StateITreeSpec A) (f : A -> _StateITreeSpec B), monotonicsi A w ->
      (forall a, monotonicsi B (f a)) -> monotonicsi B (_bindsi A B w f).
  Proof.
    unfold monotonicsi. intros. unfold _bindsi in *.
    set (fun (t : itree Void (S * A)) p0 Hp0 => (exists a s', ret (s',a) ≈ t /\ f a p0 Hp0 s') \/ (divergence t /\ p0 spin)) as fp.
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
      specialize (eutt_reta_or_div _ t). intros. destruct H1.
      + destruct H1 as [ [s' a]  Hretas']. left. exists a. exists s'. split; auto.
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
          specialize (spin_div Void (S * B) ) as H0. rewrite <- Hretbs'' in H0. pinversion H0.
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

  Definition _obssi A (m : S -> itree Void (S * A)) : _StateITreeSpec A :=
    fun post Hp s => post (m s).

  Lemma monot_obssi : forall A (m : S -> itree Void (S * A)), monotonicsi A (_obssi A m).
  Proof.
    unfold monotonicsi. intros. apply H. auto.
  Qed.

  Definition obssi A (m : S -> itree Void (S * A) ) : StateITreeSpec A :=
    exist _ (_obssi A m) (monot_obssi A m).

  Definition ret_stateitree A (a : A) : (S -> itree Void (S * A) ):= fun s => ret (s,a).

  Definition bind_stateitree A B (m : S -> itree Void (S * A) ) (f : A -> (S -> itree Void (S * B))) : S -> (itree Void (S * B)) :=
    fun s => let t := m s in bind t (fun '(s',a) => f a s' ) .

  Global Instance StateTransformITreeMonad : Monad (fun A => S -> itree Void (S * A)) :=
    {
      ret := ret_stateitree;
      bind := bind_stateitree;
    }.

  Lemma obssi_pres_ret : forall A (a : A), obssi A (ret a) ≈ ret a.
  Proof.
    intros. cbn. intros p Hp s. split; intros; apply H.
  Qed.

  Lemma obssi_pres_bind : forall A B (m : stateT S (itree Void) A ) (f : A -> stateT S (itree Void) B ),
      obssi B (bind m f) ≈ bind (obssi A m) (fun a => obssi B (f a) ).
  Proof.
    intros. cbn. intros p Hp s. split; intros.
    - simpl in *. unfold bind_stateitree in H. unfold _obssi in H.
      unfold _bindsi. unfold _obssi.
      specialize (eutt_reta_or_div _ (m s) ) as Hor. destruct Hor.
      * left. destruct H0 as [ [s' a ] Has']. exists a. exists s'. split; auto.
        eapply Hp; eauto. rewrite <- Has'. simpl. symmetry. specialize (bind_ret (s',a) (fun '(s0,a0) => f a0 s0) ) as H1.
        simpl in H1.  auto. rewrite H1. reflexivity.
      * right. split; auto. apply div_spin_eutt in H0. eapply Hp; eauto. rewrite H0. apply spin_bind.
    - simpl in *. unfold bind_stateitree. unfold _bindsi, _obssi in *. destruct H.
      + destruct H as [a [s' [Hretas' Hpfa] ] ]. eapply Hp; eauto. rewrite <- Hretas'.
        specialize (bind_ret (s',a) (fun '(s0,a0) => f a0 s0 ) ) as H1. simpl in H1. rewrite H1. reflexivity.
      + destruct H. eapply Hp; eauto. apply div_spin_eutt in H. rewrite H. symmetry. apply spin_bind.
  Qed.

  Instance StateITreeEffectObs : EffectObs (stateT S (itree Void) ) (StateITreeSpec):=
    obssi.

  Program Instance StateITreeMonadMorphism : MonadMorphism (stateT S (itree Void) ) StateITreeSpec StateITreeEffectObs.
  Next Obligation. apply obssi_pres_ret. Qed.
  Next Obligation. apply obssi_pres_bind. Qed.


  Definition _encode A (post : itree Void (S * A) -> Prop ) (Hpost : resp_eutt _ _ post) (pre : S -> Prop) : _StateITreeSpec A :=
    fun p Hp s => pre s /\ forall t, post t -> p t.

  Lemma encode_monot : forall A post Hpost pre, monotonicsi A ( _encode A post Hpost pre).
  Proof.
    intros. intro. intros. unfold _encode in *. destruct H0. split; auto.
  Qed.

  Definition encode A post Hpost pre :=
    exist _ (_encode A post Hpost pre) (encode_monot A post Hpost pre).

  Variant iterF_body {A B : Type} (p : itree Void (S * B) -> Prop ) (Hp : resp_eutt _ _ p)
          (F : A -> S -> Prop ) (t : itree Void (S * (A + B) )) : Prop :=
  | inf_tau (Ht : divergence t) (Hspin : p spin) 
  | term_b (b : B) (s : S) (Ht : (ret (s,(inr b))) ≈ t) (Hbs : p (ret (s,b) ))
  | cont_a (a' : A) (s : S) (Hreta : ret (s,inl a') ≈ t ) (Hcorec : F  a' s )

.

  Hint Constructors iterF_body.

  Lemma iterF_body_resp_eutt : forall A B 
          (p : itree Void (S * B) -> Prop ) (Hp : resp_eutt _ _ p) (F : A -> S -> Prop ), 
    resp_eutt _ _ (iterF_body p Hp F).
  Proof.
    intros. intros t1 t2 Heutt. split; intros; inversion H; subst.
    - apply inf_tau; auto. rewrite <- Heutt. auto.
    - eapply term_b; eauto. rewrite <- Heutt. auto.
    - eapply cont_a; eauto. rewrite <- Heutt. auto.
    - apply inf_tau; auto. rewrite Heutt. auto.
    - eapply term_b; eauto. rewrite Heutt. auto.
    - eapply cont_a; eauto. rewrite Heutt. auto.
  Qed.

  Variant iterF {A B : Type} (body : A -> StateITreeSpec (A + B) ) (a : A) (s : S)
          (p : itree Void (S * B) -> Prop ) (Hp : resp_eutt _ _ p) 
          (F : A -> S -> Prop ) : Prop :=
    | iterF_cons (Hiter : proj1_sig (body a) (iterF_body p Hp F) (iterF_body_resp_eutt A B p Hp F) s).

  Hint Constructors iterF.
  Lemma iterF_monotone {A B} (body:  (A -> StateITreeSpec (A + B))) 
        sim sim'  (a : A) (s : S)
        (p : itree Void (S * B) -> Prop) (Hp : resp_eutt Void (S * B) p)
        (IN : iterF body a s p Hp sim) (LE : sim <2= sim'):
    iterF body a s p Hp sim'.
  Proof.
    induction IN; constructor; auto.
    destruct (body a) as [fa Hfa]; simpl in *. eapply Hfa; try apply Hiter.
    intros. inversion H; subst; eauto.
  Qed.
 
  Definition iter_ {A B} sim (body : A -> StateITreeSpec (A + B) ) a p Hp s : Prop :=
    iterF body a s p Hp sim.

  Hint Unfold iter_.

  Lemma iterF_monotone' {A B} body p Hp : monotone2 (fun sim a s  => @iter_ A B sim body a p Hp s).
  Proof.
    repeat red. intros. eapply iterF_monotone; eauto.
  Qed.

  Hint Resolve iterF_monotone' : paco.

  Definition iter_paco {A B} := fun (f : A -> StateITreeSpec (A + B) ) (a : A) (p : itree Void (S * B) -> Prop )
                                (Hp : resp_eutt _ _ p) (s : S) => 
                              paco2 (fun (F : A -> S -> Prop) a s => iter_ F f a p Hp s ) bot2  a s.

  Ltac punf2 H := punfold H; try apply iterF_monotone'.

  Lemma iter_monot : forall A B (f : A -> StateITreeSpec (A + B) ) (a : A),
    monotonicsi _ (iter_paco f a).
  Proof.
    intros. repeat intro. generalize dependent a. generalize dependent s. pcofix CIH.
    intros. pfold. punf2 H1. constructor. destruct H1. destruct (f a) as [fa Hfa]. simpl in *.
    eapply Hfa; try apply Hiter. intros t ?Ht. inversion Ht; subst; eauto.
    pclearbot. eapply cont_a; eauto.
  Qed.

  Definition iterp {A B} f a := exist _ (@iter_paco A B f a) (iter_monot A B f a).



  Lemma not_ret_eutt_spin : forall A E (a : A), ~ (Ret a ≈ @spin E A).
  Proof.
    intros. intro Hcontra. simpl in Hcontra. specialize (spin_div E A) as Hdiv. rewrite <- Hcontra in Hdiv.
    pinversion Hdiv.
  Qed.

  Ltac clear_ret_eutt_spin :=
    match goal with 
               | H : ret ?a ≈ spin  |- _ => simpl in H; exfalso; eapply not_ret_eutt_spin; eauto
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

  Ltac gen_dep2 a s := generalize dependent a; generalize dependent s.

  Ltac dest_dep f a := destruct (f a) as [?fa ?Hfa] eqn : ?Heq; simpl in *.

  Instance StateITreeIter : Iter (Kleisli StateITreeSpec) sum := @iterp.

  Instance StateITreeUnfold : IterUnfold (Kleisli StateITreeSpec) sum.
  Proof.
    intros A B f a. constructor; intros.
    - red. repeat red in H. cbn. unfold bindsi, _bindsi. punf2 H. destruct H. dest_dep f a. 
      eapply Hfa; try apply Hiter. intros t ?Ht. inversion Ht; subst; auto.
      + left. exists (inr b). exists s0. split; auto.
      + pclearbot. left. exists (inl a'). exists s0. auto.
    - cbn in H. unfold bindsi, _bindsi in H. pfold. constructor. dest_dep f a.
      eapply Hfa; try apply H. intros. simpl in *. basic_solve; eauto.
      + eapply cont_a; try apply H0. auto.
      + eapply term_b; try apply H0; auto.
  Qed.

  Lemma iterF_body_proper : forall A B (p p' : itree Void (S * B) -> Prop ) Hp Hp' (F F' : A -> S -> Prop) t,
      (forall t, p t -> p' t) -> (forall a s, F a s -> F' a s) ->      
      iterF_body p Hp F t -> iterF_body p' Hp' F' t.
  Proof.
    intros. 
    inversion H1; subst; eauto.
  Qed.

  Instance StateITreeIterNatural : IterNatural (Kleisli StateITreeSpec) sum.
  Proof.
    intros A B C. intros. constructor.
    - gen_dep2 a s. pcofix CIH. intros. cbn in H0. red in H0. pfold. constructor. cbn. 
      unfold bindsi, _bindsi. punf2 H0. destruct H0. dest_dep f a. eapply Hfa; try apply Hiter.
      clear Hiter. intros t ?Ht. basic_solve; eauto.
      + right. split; auto. apply inf_tau; auto. apply spin_div.
      + left. exists (inr b). exists s0. split; auto. cbn. unfold bindsi, _bindsi.
        dest_dep g b. eapply Hfa0; try apply H0. intros. 
        specialize (eutt_reta_or_div _ t0) as Hor. basic_solve; auto.
        * left. destruct a0 as [s1 c]. exists c. exists s1. split; auto. unfold _retsi.
          eapply term_b; try reflexivity. eapply Hp; eauto.
        * right. split; eauto. apply inf_tau; try apply spin_div.
          eapply Hp; try apply H. symmetry. apply div_spin_eutt. auto.
      + left. exists ( inl a'). exists s0. split; auto. cbn. unfold _bindsi, _retsi.
        left. exists a'. exists s0. split; try reflexivity. eapply cont_a; try reflexivity.
        right. apply CIH. pclearbot. auto.
    - intros. gen_dep2 a s. cbn. unfold _bindsi. pcofix CIH. 
      intros. pfold. constructor. punf2 H0. destruct H0. cbn in Hiter.
      unfold bindsi, _bindsi in Hiter. dest_dep f a. eapply Hfa; try apply Hiter. clear Hiter.
      simpl.  intros. basic_solve; auto.
      + cbn in H0. unfold _bindsi, _retsi in H0. basic_solve. unfold id in H0. basic_solve. pclearbot. 
        eapply cont_a; eauto. auto.
      + cbn in H0. unfold bindsi, _bindsi in H0. eapply term_b; try apply H.
        left. exists b. exists s'. split; try reflexivity. dest_dep g b. eapply Hfa0; try apply H0.
        intros ?t ?Ht. simpl in *. basic_solve.
        * unfold _retsi in H2. basic_solve. eapply Hp; eauto. symmetry. auto.
        * apply div_spin_eutt in H1. eapply Hp; eauto.
      + apply inf_tau; auto. right. split; auto. apply spin_div.
  Qed.

  Instance StateITreeIterDinatural : IterDinatural (Kleisli StateITreeSpec) sum.
  Proof.
    intros A B C f g. constructor.
    - intros. cbn. unfold bindsi, _bindsi. cbn in H. punf2 H. destruct H. cbn in Hiter. unfold bindsi, _bindsi in Hiter.
      dest_dep f a. eapply Hfa; try apply Hiter. clear Hiter. simpl. intros ?t ?Ht. basic_solve; auto.
      + cbn in H0. rename a0 into b. left. exists (inl b). exists s'. split; auto.
        cbn. 
        clear H.
        gen_dep2 b s'. pcofix CIH. intros. pfold. constructor. cbn. unfold bindsi, _bindsi.
        dest_dep g b. eapply Hfa0; try apply H0. clear H0. intros. basic_solve; auto using spin_div.
        * rename b0 into c. left. exists (inr c). exists s0. split; auto. cbn. unfold _retsi.
          eapply term_b; eauto. reflexivity.
        * left. exists (inl a'). exists s0. split; auto. cbn. pclearbot. punf2 Hcorec. destruct Hcorec.
          cbn in Hiter. unfold bindsi, _bindsi in Hiter. dest_dep f a'. eapply Hfa1; try apply Hiter. clear Hiter.
          simpl. intros. basic_solve; auto using spin_div.
          -- cbn in H0. auto. eapply cont_a; eauto. auto.
          -- cbn in H0. unfold _retsi in H0. basic_solve; auto using spin_div. eapply term_b; try apply Hbs.
             auto.
      + cbn in H0. unfold _retsi in H0. basic_solve; auto using spin_div. rename b into c. left.
        exists (inr c). exists s'. split; auto.
    - gen_dep2 a s. pcofix CIH. intros. cbn in H0. pfold. unfold bindsi, _bindsi in H0. constructor.
      cbn. unfold bindsi, _bindsi. dest_dep f a. eapply Hfa; try apply H0. clear H0. simpl.
      intros. basic_solve; auto using spin_div.
      + cbn in H0. left. rename a0 into b. exists (inl b). exists s'. split; auto.
        cbn. punf2 H0. destruct H0. cbn in Hiter. unfold bindsi, _bindsi in Hiter. dest_dep g b.
        eapply Hfa0; try apply Hiter. clear Hiter. simpl. intros. basic_solve; auto using spin_div.
        * eapply cont_a; try apply H0. right. apply CIH. cbn. unfold bindsi, _bindsi. cbn in H1.
          dest_dep f a0. eapply Hfa1; try apply H1. clear H1. intros. basic_solve; auto using spin_div.
          -- rename b0 into c. left. exists (inr c). exists s0. split; auto.
          -- left. rename a' into b'. exists (inl b'). exists s0. split; auto. pclearbot.  auto.
        * cbn in H1. unfold _retsi in H1. basic_solve. rename b0 into c. eapply term_b; try apply Hbs; auto.
     + cbn in H0. unfold _retsi in H0. left. rename b into c. exists (inr c). exists s'.
       split; auto. cbn. unfold _retsi. eapply term_b; try apply H0; auto. reflexivity.
  Qed.

  Instance StateITreeIterCodiagonal : IterCodiagonal (Kleisli StateITreeSpec) sum.
  Proof.
    intros A B f. constructor.
    - gen_dep2 a s. pcofix CIH. intros. cbn in H0. pfold. constructor. cbn. unfold bindsi, _bindsi.
      punf2 H0. destruct H0. cbn in Hiter. punf2 Hiter. destruct Hiter. dest_dep f a. eapply Hfa; try apply Hiter.
      clear Hiter. intros. basic_solve; auto using spin_div.
      + left. exists (inr (inr b) ). exists s0. split; auto. cbn. unfold _retsi.
        eapply term_b; try apply Hbs0. reflexivity.
      + left. exists (inr (inl a0)). exists s0. split; auto. cbn. unfold _retsi. 
        apply cont_a with (a' := a0) (s1 := s0); try reflexivity. pclearbot. right. apply CIH. auto.
      + left. exists (inl a'). exists s0. split; auto. cbn. unfold _retsi. 
        eapply cont_a with (a'0 := a') (s1 := s0); try reflexivity. right. apply CIH. pclearbot.
        punf2 Hcorec. destruct Hcorec. pfold. constructor. cbn. pfold. constructor.
        dest_dep f a'. eapply Hfa0; try apply Hiter. clear Hiter. auto.
    - gen_dep2 a s. pcofix CIH. intros. pfold. constructor. cbn. cbn in H0. punf2 H0. destruct H0.
      cbn in Hiter. unfold bindsi, _bindsi in Hiter. pfold. constructor. dest_dep f a.
      eapply Hfa; try apply Hiter. clear Hiter. simpl. intros. basic_solve; auto using spin_div.
      + cbn in H0. unfold _retsi in H0. eapply cont_a; try apply H.
        clear H. left.
        gen_dep2 a0 s'. pcofix CIH'. intros. basic_solve; auto using spin_div.
        pclearbot. pfold. constructor. punf2 Hcorec. destruct Hcorec. cbn in Hiter. unfold bindsi, _bindsi in Hiter.
        dest_dep f a0. eapply Hfa0; try apply Hiter. clear Hiter. simpl. intros.
        basic_solve; auto.
        * cbn in H0. unfold _retsi in H0. basic_solve. eapply cont_a; try apply H. right. apply CIH'.
          pclearbot. punf2 Hcorec. destruct Hcorec. cbn in Hiter. unfold bindsi, _bindsi in Hiter.
          eapply cont_a with (a' := a1) (s0 := s'0) ; try reflexivity. left. pfold. constructor. auto.
        * cbn in H0. unfold _retsi in H0. basic_solve. pclearbot. eapply term_b; try apply H.
          eapply cont_a; try reflexivity. auto.
        * eapply term_b; try apply H. cbn in H0. unfold _retsi in H0. basic_solve. eapply term_b; try apply Hbs; reflexivity.
     + cbn in H0. unfold _retsi in H0. basic_solve. eapply term_b; try apply H.
       eapply cont_a; try reflexivity. right. apply CIH. pclearbot. apply Hcorec.
     + cbn in H0. unfold _retsi in H0. basic_solve. eapply term_b; try apply H. eapply term_b; try apply Hbs; reflexivity.
  Qed.

  Program Definition get_spec : StateITreeSpec S :=
    fun p _ s => p (ret (s,s)).
  Next Obligation.
  intro. auto.
  Qed.

  Program Definition put_spec (s : S) : StateITreeSpec unit :=
    fun p _ _ => p (ret (s,tt) ).
  Next Obligation.
  intro. auto.
  Qed.

  Definition HandlerStateITree : (stateE S) ~> (StateITreeSpec) :=
    fun _ ev =>
      match ev with 
      | Get _ => get_spec
      | Put _ s => put_spec s
      end.
  
  (*MonadIter type parameters reversed for just Iter*)
  Instance StateITreeMonadIter  : MonadIter StateITreeSpec := fun B A => @iterp A B.

  Definition InterpStateITreeSpec := interp HandlerStateITree.

  Definition get_handle : S -> (itree Void (S * S) ) :=
    fun s => ret (s,s).

  Definition put_handle (s : S) : S -> (itree Void (S * unit )) :=
    fun _ => ret (s, tt).

  Definition HandlerState : (stateE S) ~> (stateT S (itree Void)) :=
    fun _ ev =>
      match ev with
      | Get _ => get_handle
      | Put _ s => put_handle s
      end.

  

  Lemma interp_obs : forall (A : Type) (t : itree (stateE S) A ),
      InterpStateITreeSpec A t ≈ obs A (interp_state HandlerState t). 
  Proof.
    intros. constructor; intros.
    - cbn in H. cbn. red. (*for terminating t's it maybe is fine*) admit.
    - cbn in H. unfold _obssi in H. cbn.
      gen_dep2 t s. pcofix CIH. intros. pfold. constructor.
      destruct (observe t) eqn : Heq; simpl.
      + unfold _retsi. simpl in *. assert (t ≈ ret r0).
        { specialize (itree_eta t) as H. rewrite Heq in H. rewrite H. reflexivity. }
        eapply term_b with (s0 := s) (b := r0); try reflexivity. eapply Hp; eauto.
        rewrite H. specialize @interp_state_ret with (E := stateE S) as Hret.
        specialize (Hret Void A S HandlerState s r0). rewrite Hret. reflexivity.
      + unfold _retsi. apply cont_a with (a' := t0) (s0 :=s); try reflexivity.
        right. apply CIH. eapply Hp; eauto. 
        assert (t ≈ t0). { specialize (itree_eta t) as H. rewrite Heq in H. rewrite H. rewrite tau_eutt. reflexivity. }
        rewrite H. reflexivity.
      + destruct e.
        * repeat red. left. exists s. exists s. split; try reflexivity.  cbn. unfold _retsi. 
          eapply cont_a with (s0 := s); try reflexivity. right. apply CIH.  eapply Hp; eauto.
          specialize @unfold_interp_state with (E := stateE S) (t := t) as H.
          specialize (H Void S HandlerState s). rewrite H. rewrite Heq.
          simpl. cbn. rewrite bind_ret. simpl. rewrite tau_eutt. reflexivity.
        * repeat red. left. exists tt. exists s0. split; try reflexivity. repeat red.
          eapply cont_a; try reflexivity. right. apply CIH. eapply Hp; eauto.
          specialize @unfold_interp_state with (E := stateE S) (t := t) as H. specialize (H Void S HandlerState s).
          rewrite Heq in H. simpl in H. unfold put_handle in H. simpl in H. rewrite bind_ret in H. simpl in *.
          rewrite H. rewrite tau_eutt. reflexivity.
   Admitted.

End StateITree.


