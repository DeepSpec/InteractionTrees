From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
.


Definition sequence (T : Type) : Type := nat -> T.

Definition advance {T} (seq : sequence T) : sequence T :=
  fun n => seq (S n).

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
  bot : T;
  }.




Definition monotone_seq {T} `{weak_cpo T} (seq : sequence T) : Prop :=
  forall (n m : nat), n <= m -> strong_leq (seq n) (seq m).

Definition monotone_fun {T} `{weak_cpo T} (f : T -> T) : Prop :=
  forall t1 t2, strong_leq t1 t2 -> strong_leq (f t1) (f t2).

Variant supremum {T} `{weak_cpo T} (seq : sequence T) (s : T) : Prop :=
  | supr (Hmon : monotone_seq seq) (Hub : (forall n, weak_leq (seq n) s ) ) 
         (Hlub : forall (upper_bound : T), (forall n, weak_leq (seq n) upper_bound) -> weak_leq s upper_bound ).

Fixpoint frepeat {A : Type} (f : A -> A) (n : nat) (init : A) :=
  match n with
  | 0 => init
  | S m => f (frepeat f m init) 
  end.

Definition strong_seq_eq {T} `{weak_cpo T} (f g : sequence T) : Prop := forall x, strong_eq (f x) (g x).

Definition scott_continuous {T} `{weak_cpo T} (f : T -> T) : Prop :=
  forall (seq : sequence T ), monotone_seq seq ->
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
  bot_correct : forall t, strong_leq bot t;
  sup_correct : forall (seq : sequence T), monotone_seq seq -> supremum seq (sup seq);
  fun_eq_proper_sup : Proper (strong_seq_eq ==> strong_eq) sup; 
  advance_weak_eq : forall seq, monotone_seq seq -> weak_eq (sup seq) (sup (advance seq) )
  }.

Definition fix_seq {T} (f : T -> T) `{weak_cpo T} : sequence T := fun n => frepeat f n bot.

Lemma fix_seq_monotone_fun {T} (f : T -> T) (C : weak_cpo T) `{@weak_cpo_laws T C} : monotone_fun f -> monotone_seq (fix_seq f).
Proof.
  intros Hf n m Hnm. induction Hnm.
  - destruct H. reflexivity.
  - cbn. unfold fix_seq in *. destruct H. etransitivity; eauto.
    red in Hf. clear IHHnm Hnm n. induction m. apply bot_correct0.
    cbn. eapply Hf. auto.
Qed.

Definition weak_cpo_fix {T} (f : T -> T) `{weak_cpo T} : T := sup (fix_seq f).

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

Lemma scott_continuous_fix_aux1 : forall (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (f : T -> T),
    scott_continuous f -> monotone_fun f -> weak_eq (f (sup (fix_seq f) ) ) (sup (map f (fix_seq f) ) ).
Proof.
  intros. assert (weak_cpo_laws C); auto. destruct H. unfold fix_seq. unfold map.
  rewrite H0. 2 : apply fix_seq_monotone_fun; auto.
  unfold map. reflexivity.
Qed.

Lemma scott_continuous_fix : forall (T : Type) (C : weak_cpo T) `{@weak_cpo_laws T C} (f : T -> T),
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
