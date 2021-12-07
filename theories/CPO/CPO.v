From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
.

Require Import Lia.

Definition sequence (T : Type) : Type := nat -> T.

Definition advance {T} (seq : sequence T) : sequence T :=
  fun n => seq (S n).

Definition advance_n {T} (n : nat) (seq : sequence T) : sequence T :=
  fun m => seq (n + m).

Definition map {A B} (f : A -> B) (seq : sequence A) :=
  fun n : nat => f (seq n).

Definition apply_seq {A B} (seq : sequence (A -> B)) (a : A) : sequence B :=
  map (fun f => f a) seq.

Class weak_cpo (T : Type) := {
  weak_leq : T -> T -> Prop;
  strong_leq : T -> T -> Prop;
  sup : sequence T -> T;
  weak_eq : T -> T -> Prop;
  strong_eq : T -> T -> Prop;
  }.

Class pointed_weak_cpo {T : Type} (C : weak_cpo T) := {
   bot : T;
  }.

(*Not sure if this is the best way to formulate, seems to break how I have written the laws *)

Definition monotone_seq {T} `{weak_cpo T} (seq : sequence T) : Prop :=
  forall (n m : nat), n <= m -> strong_leq (seq n) (seq m).

Definition monotone_fun {D1 D2} `{weak_cpo D1} `{weak_cpo D2} (f : D1 -> D2) : Prop :=
  forall t1 t2, strong_leq t1 t2 -> strong_leq (f t1) (f t2).

Definition weak_monotone_fun {D1 D2} `{weak_cpo D1} `{weak_cpo D2} (f : D1 -> D2) : Prop :=
  forall t1 t2, weak_leq t1 t2 -> weak_leq (f t1) (f t2).

Variant supremum {T} `{weak_cpo T} (seq : sequence T) (s : T) : Prop :=
  | supr (Hmon : monotone_seq seq) (Hub : (forall n, weak_leq (seq n) s ) ) 
         (Hlub : forall (upper_bound : T), (forall n, weak_leq (seq n) upper_bound) -> weak_leq s upper_bound ).

Fixpoint frepeat {A : Type} (f : A -> A) (n : nat) (init : A) :=
  match n with
  | 0 => init
  | S m => f (frepeat f m init) 
  end.

Definition strong_seq_eq {T} `{weak_cpo T} (f g : sequence T) : Prop := forall x, strong_eq (f x) (g x).

Definition scott_continuous {D1 D2} `{weak_cpo D1} `{weak_cpo D2} (f : D1 -> D2) : Prop :=
  forall (seq : sequence D1 ), monotone_seq seq ->
    weak_eq (f (sup seq)) (sup (map f seq)) .

Class weak_cpo_laws {T} (C : weak_cpo T) := {
  weak_eq_eq : Equivalence weak_eq;
  weak_leq_preorder : PreOrder weak_leq;
  weak_leq_po : PartialOrder weak_eq weak_leq;
  strong_eq_eq : Equivalence strong_eq;
  strong_leq_preorder : PreOrder strong_leq;
  strong_leq_po : PartialOrder strong_eq strong_leq;
  weaken_eq : forall t1 t2, strong_eq t1 t2 -> weak_eq t1 t2;
  weaken_leq : forall t1 t2, strong_leq t1 t2 -> weak_leq t1 t2;
  sup_correct : forall (seq : sequence T), monotone_seq seq -> supremum seq (sup seq);
  fun_eq_proper_sup : Proper (strong_seq_eq ==> strong_eq) sup;
  advance_weak_eq : forall seq, monotone_seq seq -> weak_eq (sup seq) (sup (advance seq) )
  }.

Class pointed_weak_cpo_laws {T} (C : weak_cpo T) (PC : pointed_weak_cpo C) := {
  bot_correct : forall t, strong_leq bot t;
}.

Lemma weak_eq_S_advance (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (n : nat) (seq : sequence T) :
  monotone_seq seq ->
  weak_eq (sup (advance_n (S n) seq)) (sup (advance (advance_n n seq) ) ).
Proof.
  intros.
  unfold advance, advance_n. cbn. destruct H.
  assert (strong_seq_eq  (fun m : nat => seq (S (n + m))) ((fun n0 : nat => seq (n + S n0)) )).
  red. intros. assert (S (n + x) = n + S x ). lia. rewrite H. reflexivity.
  apply weaken_eq0.
  setoid_rewrite H. reflexivity.
Qed.

Lemma weak_eq_advance_n (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (n : nat) (seq : sequence T) :
  monotone_seq seq ->
  weak_eq (sup seq) (sup (advance_n n seq) ).
Proof.
  destruct H. generalize dependent seq.
  induction n; intros seq Hseq; cbn; try reflexivity.
  rewrite weak_eq_S_advance; auto. 2 : econstructor; auto.
  rewrite <- advance_weak_eq0; auto.
  red. unfold advance_n. intros. eapply Hseq. lia.
Qed.


Definition fix_seq {T} (f : T -> T) `{C : weak_cpo T} `{pointed_weak_cpo T} : sequence T := fun n => frepeat f n bot.

Lemma fix_seq_monotone_fun {T} (f : T -> T) (C : weak_cpo T) (PC : pointed_weak_cpo C) `{@weak_cpo_laws T C} `{@pointed_weak_cpo_laws T C PC} : monotone_fun f -> monotone_seq (fix_seq f).
Proof.
  intros Hf n m Hnm. induction Hnm.
  - destruct H. reflexivity.
  - cbn. unfold fix_seq in *. destruct H. etransitivity; eauto.
    red in Hf. clear IHHnm Hnm n. induction m. destruct H0. apply bot_correct0.
    cbn. eapply Hf. auto.
Qed.

Definition weak_cpo_fix {T} (f : T -> T) `{pointed_weak_cpo T} : T := sup (fix_seq f).

(*this lemma doesn't work in this weak weak_cpo framework we lose the convenience that scott cont
  is monotonicity. That is unfortunate but monotonicity should be easier to prove 
 *)
(*
Lemma scott_continuous_monotone : forall (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (f : T -> T),
    scott_continuous f -> forall t1 t2, strong_leq t1 t2 -> strong_leq (f t1) (f t2).
Proof.
  intros. unfold scott_continuous in H0. rename H0 into Hscott.
  set (fun n => match n with | 0 => t1 | _ => t2 end ) as seq.
  assert (monotone_seq seq). 
  { red. intros. induction H0.
    - destruct H. reflexivity. 
    - destruct n; cbn; auto. destruct H. reflexivity.
  } apply Hscott in H0 as Hseq. Abort.
(* *)*)

Lemma scott_continuous_fix_aux1 : forall (T : Type) (C : weak_cpo T) (PC : pointed_weak_cpo C) `{@weak_cpo_laws T C} 
                                    `{@pointed_weak_cpo_laws T C PC} (f : T -> T),
    scott_continuous f -> monotone_fun f -> weak_eq (f (sup (fix_seq f) ) ) (sup (map f (fix_seq f) ) ).
Proof.
  intros. assert (weak_cpo_laws C); auto. destruct H. unfold fix_seq. unfold map.
  rewrite H1. 2 : apply fix_seq_monotone_fun; auto.
  unfold map. reflexivity.
Qed.

Lemma scott_continuous_fix : forall (T : Type) (C : weak_cpo T) (PC : pointed_weak_cpo C) `{@weak_cpo_laws T C} 
                               `{@pointed_weak_cpo_laws T C PC} (f : T -> T),
    scott_continuous f -> monotone_fun f -> weak_eq (weak_cpo_fix f) (f (weak_cpo_fix f)).
Proof.
  intros. unfold weak_cpo_fix.
  assert (weak_cpo_laws C); auto.
  destruct H. rewrite scott_continuous_fix_aux1; auto.
  unfold fix_seq, map. rewrite advance_weak_eq0.
  unfold advance. cbn. reflexivity. apply fix_seq_monotone_fun; auto.
Qed.


Definition const_seq {T} `{weak_cpo T} (seq : sequence T) t : Prop :=
  forall n, strong_eq t (seq n).

Lemma supremum_const_seq : forall (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (seq : sequence T) (t : T),
    const_seq seq t -> supremum seq t.
Proof.
  intros. red in H0. constructor.
  - red. intros. destruct H. do 2 rewrite <- H0. reflexivity.
  - intros. destruct H. apply weaken_leq0. rewrite (H0 n). reflexivity.
  - intros. destruct H.
    assert (forall n, weak_eq t (seq n) ). intros. apply weaken_eq0. auto.
    rewrite (H 0). auto.
Qed.

Lemma supremum_unique : forall (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (seq : sequence T) (t1 t2 : T),
    supremum seq t1 -> supremum seq t2 -> weak_eq t1 t2.
Proof.
  intros. destruct H0. destruct H1.
  destruct H. apply weak_leq_po0. do 3 red. unfold flip.
  split; auto.
Qed.

Lemma sup_const_seq : forall (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (seq : sequence T) (t : T),
    const_seq seq t -> weak_eq t (sup seq).
Proof.
  intros. assert (monotone_seq seq).
  { red. intros. red in H0. destruct H. do 2 rewrite <- H0. reflexivity. } 
  apply supremum_const_seq in H0; auto. assert (weak_cpo_laws C); auto. destruct H. apply sup_correct0 in H1.
  eapply supremum_unique; eauto.
Qed.

Lemma weak_eq_fix_aux {T} {C : weak_cpo T} {PC : pointed_weak_cpo C}
      `{@weak_cpo_laws T C} `{@pointed_weak_cpo_laws T C PC} (f g : T -> T) (t : T) :
  Proper (weak_eq ==> weak_eq) f ->
  monotone_fun f ->
  monotone_fun g ->
  pointwise_relation T weak_eq f g -> supremum (fix_seq f) t -> supremum (fix_seq g) t.
Proof.
  intros Hf1 Hf2 Hg Hfg Hft. destruct H. red in Hf2. red in Hg.
  assert (forall n, weak_eq (frepeat g n bot) (frepeat f n bot) ).
  { intros. induction n; cbn; eauto. apply weak_leq_po0. cbn. destruct H0;
    split; cbn; apply weaken_leq0; apply bot_correct0. setoid_rewrite <- IHn.
    rewrite Hfg. reflexivity. }
  constructor. apply fix_seq_monotone_fun; auto. econstructor; eauto.
  -  destruct Hft. intros. unfold fix_seq in *. specialize (Hub n).
     rewrite H. auto.
  - intros. destruct Hft. eapply Hlub.
    intros. symmetry in H. setoid_rewrite H; eauto.
Qed.
(*does scott cont imply this properness ? probably not...*)

Lemma weak_eq_fix {T} {C : weak_cpo T} {PC : pointed_weak_cpo C} 
      `{@pointed_weak_cpo_laws T C PC}
      `{@weak_cpo_laws T C} (f g : T -> T) :
  Proper (weak_eq ==> weak_eq) f ->
  monotone_fun f ->
  monotone_fun g ->
  pointwise_relation T weak_eq f g ->
  weak_eq (weak_cpo_fix f) (weak_cpo_fix g).
Proof.
  intros. eapply supremum_unique with (seq := fix_seq f) ; eauto.
  unfold weak_cpo_fix. destruct H0. apply sup_correct0. apply fix_seq_monotone_fun; auto.
  econstructor; eauto.
  eapply (weak_eq_fix_aux g); eauto.
  - repeat intro. red in H4. destruct H0. symmetry in H4.
    do 2 rewrite H4. eauto.
  - red. intros. destruct H0. symmetry. eauto.
  - destruct H0. apply sup_correct0. 
    apply fix_seq_monotone_fun; auto. econstructor; eauto.
Qed. (* maybe I should write this more generally in terms of sup and monotone sequences *)

Global Instance proper_supremum {T} {C : weak_cpo T} `{@weak_cpo_laws T C} {seq} : Proper (weak_eq ==> flip impl) (supremum seq).
Proof.
  repeat intro. destruct H1. destruct H. constructor; auto. 
  setoid_rewrite H0. auto. setoid_rewrite H0. auto.
Qed.
