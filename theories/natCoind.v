Fixpoint Fn {A:Type} (step: A -> A)  (f0 : A) (n:nat) :=
  match n with
  | O => f0 
  | S n => step (Fn step f0 n)
  end.

(* TODO: generalize for hetero relations *)
Definition RTopN {A} (Rs: (A-> A->Prop)->(A -> A->Prop)) (n:nat) :=
  Fn Rs (fun _ _ => True) (* Top *) n.

Lemma RTopNS {A} (Rs: (A-> A->Prop)->(A -> A->Prop)) (n:nat) :
  RTopN Rs (S n)= Rs (RTopN Rs n).
Proof using.
  reflexivity.
Qed.

(* greatest fixpoint if F is continuous *)
Definition GFPC {A} (Rs: (A-> A->Prop)->(A -> A->Prop))
           (a1 a2: A): Prop:=
  forall n, RTopN Rs n a1 a2.

Require Import Coq.Relations.Relation_Definitions.
Definition continuousRelF
           {A} (Rs: (A-> A->Prop)->(A -> A->Prop)):=
            inclusion _
              (@GFPC _ Rs)
              (Rs (@GFPC _ Rs)).

Require Import ITree.Equivalence.
Require Import ITree.ITree.
Require Import ITree.inversion.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.

Print eutt.
Require Import Paco.paco.
Lemma equivCoind {A:Type} (Rs : (A -> A -> Prop) -> A -> A -> Prop) (a b : A)
      (cont: continuousRelF Rs)
      (mono: monotone2 Rs):
  (@GFPC _ Rs) a b <->
  paco2.paco2 Rs bot2 a b.
Proof using.
  split. revert a b.
  - pcofix equivCoind. intros a b Hyp.
    econstructor.
    + intros.  right. eauto.
    + apply cont in Hyp.
      eapply mono; eauto.
  - intros Hyp n.
    revert dependent a. revert b.
    induction n; simpl; intros; [ hnf; auto  |].
    rewrite RTopNS. intros.
    inversion Hyp. subst.
    eapply mono; eauto.
    intros.
    eapply IHn. unfold bot2 in LE.
    apply LE in PR. clear LE. tauto.
Qed.


(* example application to Eutt *)
Section Eutt.
  Context {E} {invertTauEq : InvertTauEq E}.
  Lemma euttCont {T}: continuousRelF (@eutt_ E T).
  Proof using invertTauEq.
    intros x y Hp.
    specialize (Hp 1) as Hp1.
    rewrite RTopNS in Hp1.
    hnf in Hp1.
    hnf.
    repnd.
    split; auto.
    intros t1 t2 H1t H2t.
    specialize (Hp1 _ _ H1t H2t).
    inverts Hp1; auto;[constructor; fail|].
    constructor.
    intros xx n. clear H.
    specialize (Hp (S n)).
    rewrite RTopNS in Hp.
    hnf in Hp. repnd.
    GC.
    specialize (Hp _ _ H1t H2t).
    remember (Vis e k1) as d1.
    remember (Vis e k2) as d2.
    destruct Hp; subst; try discriminate.
    apply invertDoEq in Heqd1.
    exrepnd. subst. simpl in *.
    apply invertTauEq in Heqd2.
    exrepnd. subst.
    eauto.
  Defined.

  Lemma equivCoindEutt {T} (a b : itree E T):
    (@GFPC _ (@eutt_ E T)) a b <->
    eutt _ _ a b.
  Proof using invertTauEq.
    apply equivCoind; [apply euttCont| ].
    apply @monotone_eutt_.
  Qed.

End Eutt.


Require Import Coq.Classes.RelationClasses.

Definition contRelProp {A:Type}(P: (A -> A -> Prop) -> Prop): Prop:=
  forall (R: nat -> A -> A-> Prop),
    (forall n, P (R n)) -> P (fun a1 a2 => forall n, R n a1 a2).

Lemma contRelPropRefl {A}:
  @contRelProp A Reflexive.
Proof using.
  firstorder.
Qed.

Lemma contRelPropSymm {A}:
  @contRelProp A Symmetric.
Proof using.
  firstorder.
Qed.

Lemma contRelPropTrans {A}:
  @contRelProp A Transitive.
Proof using.
  firstorder.
Qed.

(* contRelProp is not trivially provable. is there a property
that is provably not continuous?*)
Lemma contRelPropUnprovable {A} X:
  @contRelProp A X.
Proof using.
  hnf.
  firstorder.
Abort.
