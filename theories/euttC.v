Require Import ITree.inversion.
Require Import ITree.natCoind.
Require Import Coq.Relations.Relation_Definitions.
Require Import ITree.ITree.
Require Import ITree.Equivalence.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.
Require Import Coq.Classes.RelationClasses.
(*
Require Import Coq.Logic.FunctionalExtensionality.
Import EqNotations.
Require Import Coq.Logic.Eqdep_dec.
Require Import EqdepFacts.
 *)

Section euttC.
  Context {E: Type -> Type} {R:Type}.

  (** when proving equivalence, this is more
convenient (C for conclusion (vs. hypothesis)). when eliminating, this produces
more cases, so, you may want to use the 
equivalence to transform
euttIndC (which iterates this defn) to
euttInd. *)

  Inductive euttC (eutt : relation (itree E R)) :
    relation (itree E R) :=
  | Eutt_Ret : forall r, euttC eutt (Ret r) (Ret r)
  | Eutt_Vis : forall X (e : E X) k1 k2,
      (forall x, eutt (k1 x) (k2 x)) ->
      euttC eutt (Vis e k1) (Vis e k2)
  | Eutt_TauLR : forall (e1 e2 : itree E R),
      eutt e1 e2 -> (* coinduction hypothesis is allowed here *)
      euttC eutt (Tau e1) (Tau e2)
  | Eutt_TauL : forall (e1 e2: itree E R),
      euttC eutt e1 e2 -> (* coinduction hypothesis is NOT allowed here *)
      euttC eutt (Tau e1) e2
  | Eutt_TauR : forall (e1 e2: itree E R),
      euttC eutt e1 e2 -> (* coinduction hypothesis is NOT allowed here *)
      euttC eutt e1 (Tau e2).

  Lemma euttCMono {Ra Rb :  relation (itree E R)}:
    inclusion _ Ra Rb -> inclusion _ (euttC Ra)  (euttC Rb).
  Proof using.
    intros Hinc.
    hnf in Hinc.
    hnf.
    intros ? ? Hu.
    induction Hu; try constructor; eauto.
  Qed.

End euttC.

Section Eff.
  Context {E:Type->Type}.
  (* Equivalence, including stuttering steps *)
  Definition euttInd {T} :=
    @GFPC _ (@eutt_ E T).

  Definition euttIndC  {T} :=
    @GFPC _ (@euttC E T).


  Lemma untausVis  {T U : Type} (o: E U) k e:
    untaus' E T e (Vis o k)
    -> e=(Vis o k).
  Proof using.
    intros Hp.
    inverts Hp; auto.
  Qed.

  Lemma untausRet  {T: Type}  e v:
    untaus' E T e (Ret v)
    -> e=(Ret v).
  Proof using.
    intros Hp.
    inverts Hp; auto.
  Qed.

  Lemma invertDoEqIf {T X1 X2 : Type} (e1 : E X1)
        (e2 : E X2)
        (k1 : X1 -> itree E T)  (k2 : X2 -> itree E T):
    {p:X1=X2 | transport p e1=e2 /\ @transport _ _ _ (fun U => U -> itree E T) p k1=k2}  ->    (Vis e1 k1) = (Vis e2 k2) 
  .
    intros Hyp. exrepnd. subst.
    reflexivity.
  Qed.

  Context {invertDoEq2 : InvertTauEq E}.

  Lemma invertEuttVis  {T X : Type} (e : E X)
        (k1 k2 : X -> itree E T) (n : nat):
    euttC (RTopN euttC n) (Vis e k1) (Vis e k2) ->
    forall x : X, RTopN euttC n (k1 x) (k2 x).
  Proof using invertDoEq2.
    intros Hyp.
    remember (Vis e k1) as la.
    remember (Vis e k2) as lb.
    induction Hyp; try discriminate; eauto.
    apply invertDoEq in Heqla. exrepnd.
    subst. simpl in *.
    apply invertDoEq2 in Heqlb. subst.
    assumption.
  Qed.

  Hint Constructors euttC : freeDB.
  
  Lemma RTopSN_eutt_stronger {T} n
        (a b : itree E T):
    (RTopN euttC (S n) a b) ->
    (RTopN euttC n a b).
  Proof using.
    revert a b.
    induction n;[ reflexivity | ].
    intros ? ? Hyp.
    rewrite RTopNS.
    rewrite RTopNS in Hyp.
    induction Hyp;
      try constructor; eauto with freeDB.
  Qed.

  Lemma RTopLe_eutt_stronger {T} n m
        (a b : itree E T):
    n <= m
    ->
    (RTopN euttC m a b) ->
    (RTopN euttC n a b).
  Proof using.
    intros Hle Hr.
    induction Hle; eauto.
    apply RTopSN_eutt_stronger in Hr.
    eauto.
  Qed.

  
  Definition euttCPreserves
             A (P: (itree E A -> itree E A -> Prop) -> Prop) :=
    forall R, P R -> P (euttC R).

    Lemma  RTopNEuttCPreserves {A}
         (P: (itree E A -> itree E A -> Prop) -> Prop):
    (P (fun _ _ => True))
    -> euttCPreserves A P
    -> forall n, P (RTopN euttC n).
  Proof using.
    intros.
    induction n; eauto.
  Qed.

  Locate Reflexive.
  Lemma euttCRefl {T} : 
    euttCPreserves T Reflexive.
  Proof using.
    intros ? Hr. intros a.
    destruct a; try constructor; eauto.
  Qed.


  Lemma  GFPCEuttCPreserves {A}
         (P: (itree E A -> itree E A -> Prop) -> Prop)
         (Pc: @contRelProp _ P):
    (P (fun _ _ => True))
    -> euttCPreserves A P
    ->  P (@GFPC _ euttC).
  Proof using.
    intros.
    apply Pc.
    apply RTopNEuttCPreserves; assumption.
  Qed.
  
  Lemma euttCDelay {T} R:
    Reflexive R
    -> 
    forall (e: itree E T), euttC R (Tau e) e.
  Proof using.
    intros Hr.
    intros e.
    eapply Eutt_TauL.
    apply euttCRefl. assumption.
  Qed.

  Lemma euttCSymm {T} : 
    euttCPreserves T Symmetric.
  Proof using.
    intros ? Hr. intros a b Ha.
    induction Ha; try constructor; eauto.
  Qed.


  Global Instance euttCNsymm {T} n : Symmetric (RTopN (@euttC E T) n).
  Proof using.
    pose proof (fun X => @RTopNEuttCPreserves T _
                                           X euttCSymm) as Hx.
    firstorder.
  Qed.

  Global Instance euttCNrefl {T} n : Reflexive (RTopN (@euttC E T) n).
  Proof using.
    pose proof (fun X => @RTopNEuttCPreserves T _
                                           X euttCRefl) as Hx.
    firstorder.
  Qed.

  Global Instance euttCIndSymm {T} : Symmetric (@euttIndC T).
  Proof using.
    apply contRelPropSymm . apply euttCNsymm .
  Qed.

  Global Instance euttCIndRefl {T} : Reflexive (@euttIndC T).
  Proof using.
    apply contRelPropRefl . apply euttCNrefl .
  Qed.




  Theorem notTrans:
    ~ (forall n, @Transitive (itree E nat)
                        (RTopN (euttC) n)).
  Proof using.
    intros Hc.
    specialize (Hc 1).
    hnf in Hc.
    set (x := (Tau (Ret 1)):  itree E nat).
    set (y := (Tau (Ret 2)):  itree E nat).
    set (z := (Ret 2):  itree E nat).
    specialize (Hc x y z).
    subst x y z.
    simpl in Hc.
    rewrite RTopNS in Hc.
    dimp Hc.
    - constructor. hnf. auto.
    - clear Hc.
      remember (Tau (Ret 1)) as l.
      assert (l= (Ret 1) \/ l= Tau (Ret 1))
        by sp.
      clear Heql.
      remember ((Ret 2)) as r.
      induction hyp; subst; try discriminate;
        [dorn H |].
      + congruence.
      + discriminate.
      + 
        apply IHhyp; auto.
        clear IHhyp.
        dorn H; try discriminate; subst.
        * inversion H; sp.
    - unfold RTopN.
      eauto with freeDB.
  Qed.

  
  Lemma euttIndCEquiv  {T} n a1 a2:
    RTopN (@eutt_ E T) n a1 a2
    <->
    RTopN (@euttC E T) n a1 a2.
  Abort. (* not provable. the steps don't match up exactly; the accounding is different for deyals *)

  (* this should be provable. proving this is important. euttIndC is probably not continuous because
it allows the use of two different 
constructors for the same proof.
So, we may want to use both @euttInd and 
@euttIndC and switch between them as per 
convenience. *)


  Definition Delays (n:nat) {T} (p: itree E T):
    itree E T:=
    Fn (Tau) p n.
  
  Lemma untausAsDelay {T} t a:
    untaus' E T t a
    -> exists n, a = Delays n t.
  Proof using.
    intros.
    induction H.
    - exrepnd. subst. exists (S n).
      reflexivity.
    - exists 0. reflexivity.
  Qed.

  (*
This is refutable unless one addds the hypothesis:
NoTaus t1.
If t1 starts with a Delay and t2 does not,
the hypothesis can match the delays to decrement
the number m. The conclusion cannot do that
because the delays wont match up
   *)
  Lemma DelayAddR {T : Type}
        (t1 t2 : itree E T) (m : nat):
    RTopN euttC m t1 (Tau t2)
    -> RTopN euttC m t1 t2.
  Proof using.
    intros Hyp.
    destruct m;[hnf; auto |].
    rewrite RTopNS in *.
    change (Tau t2) with (Delays 1 t2) in Hyp.
    remember 0 as mm.
    clear Heqmm.
    remember  (Delays (S mm) t2) as d.
    induction Hyp;
      unfold Delays in *; simpl in *; try discriminate.  - inversion Heqd. subst.
                                                           GC.
  Abort.

  Lemma  EuttCPreservesDelayL {T}:
    euttCPreserves T
                   (fun R => forall a b, R a b -> R (Tau a) b).
  Proof using.
    intros R Hr a b He.
    eapply Eutt_TauL; eauto.
  Qed.

  Lemma  RTopNEuttCDelay{T} (a b: itree E T) m:
    RTopN euttC m a b
    -> RTopN euttC m (Tau a) b.
  Proof using.
    pose proof (fun X => @RTopNEuttCPreserves T _
                                           X EuttCPreservesDelayL) as Hx.
    firstorder.
  Qed.

  Lemma  RTopNEuttCDelayR {T} (a b: itree E T) m:
    RTopN euttC m a b
    -> RTopN euttC m a (Tau b).
  Proof using.
    intros.
    symmetry.
    symmetry in H.
    revert H. apply RTopNEuttCDelay.
  Qed.
  
  Require Import Arith Wf.
  Lemma DelayAddR {T : Type}
        (t1 t2 : itree E T) (n nn m : nat):
    nn <= n
    -> RTopN euttC (n+m) t1 (Delays nn t2)
    -> RTopN euttC m t1 t2.
  Proof using.
    intros Hle Hyp.
    revert dependent t2.
    revert t1. revert dependent n.
    induction nn as [| nn IHnn ] ; intros;
      [ revert Hyp;
        apply RTopLe_eutt_stronger; Omega.omega |]. 
    simpl in *.
    destruct n as [ | n]; [Omega.omega |].
    simpl in Hyp.
    rewrite RTopNS in Hyp.
    remember  (Delays (S nn) t2) as d.
    generalize dependent nn.
    induction Hyp; intros ? ? ? ?;
                          unfold Delays in *; simpl in *;
      try discriminate.
    - inversion Heqd. subst. eapply RTopNEuttCDelay.
      apply S_le_inj in Hle.
      eapply IHnn; eauto.
    - subst.
      apply RTopNEuttCDelay.
      eapply IHHyp; eauto.
    - inversion Heqd. subst.
      GC.
      destruct nn.
      + revert Hyp. simpl.
        rewrite <- RTopNS.
        apply RTopLe_eutt_stronger. Omega.omega.
      + eapply (IHnn n); eauto. Omega.omega.
        revert Hyp. simpl.
        rewrite <- RTopNS.
        apply RTopLe_eutt_stronger. Omega.omega.
  Qed.

  Lemma DelayAddL {T : Type}
        (t1 t2 : itree E T) (n nn m : nat):
    nn <= n
    -> RTopN euttC (n+m) (Delays nn t2) t1 
    -> RTopN euttC m t2 t1.
  Proof using.
    intros ? Hh.
    symmetry.
    symmetry in Hh.
    revert Hh.
    apply DelayAddR. assumption.
  Qed.

  (* this is refutable. see the comment for
DelayAddR *)
  Lemma DelaysEuttC {T} (t1 t2 : itree E T) n1 n2 m:
    RTopN euttC (m + Nat.min n1 n2)
          (Delays n1 t1) (Delays n2 t2)
    -> RTopN euttC (m)
            t1 t2.
  Abort.

  Lemma DelaysAddLR {T} (t1 t2 : itree E T) n1 n2 m:
    RTopN euttC (m + (n1 + n2))
          (Delays n1 t1) (Delays n2 t2)
    -> RTopN euttC (m)
            t1 t2.
  Proof using.
    intros Hyp.
    rewrite plus_assoc in Hyp.
    rewrite plus_comm in Hyp.
    apply DelayAddR in Hyp;[| Omega.omega].
    rewrite plus_comm in Hyp.
    revert Hyp.
    apply DelayAddL. Omega.omega.
  Qed.

  Lemma DelaysRemoveLR {T} (t1 t2 : itree E T) n1 n2 m:
    RTopN euttC (m)
          t1 t2
    ->
    RTopN euttC m
          (Delays n1 t1) (Delays n2 t2).
  Proof using.
    intros Hyp.
    induction n1; simpl.
    - induction n2; unfold Delays; simpl; eauto.
      apply RTopNEuttCDelayR. assumption.
    - unfold Delays. simpl.
      apply RTopNEuttCDelay.
      assumption.
  Qed.      

  Lemma DelaysGFPCLRIff {T} (t1 t2 : itree E T) n1 n2:
    euttIndC (Delays n1 t1) (Delays n2 t2)
    <-> euttIndC  t1 t2.
  Proof using.
    split;  intros Hyp.
    -  intros n.
       specialize (Hyp (n+(n1+n2))).
       apply DelaysAddLR in Hyp.
       assumption.
    - intros n. apply DelaysRemoveLR. eauto.
  Qed.

  Hint Constructors untaus': freeDB.
  Lemma finiteTausEuttC 
        (T : Type) (a1 a2 : itree E T):
    (forall n : nat, RTopN euttC n a1 a2) ->
    finite_taus a1 -> finite_taus a2.
  Proof using.
    unfold finite_taus, untaus.
    intros Hc Hf.
    exrepnd.
    rename Hf0 into Hu. revert dependent a2.
    induction Hu; intros ? ?; eauto.
    - apply IHHu.
      apply (DelaysGFPCLRIff _ _  1 0). assumption.
    - hnf in Hf1.
      specialize (Hc 1).
      rewrite RTopNS in Hc.
      induction Hc; try tauto; eauto;[| | ].
      + eexists; split; eauto with freeDB. reflexivity.
      + eexists; split; eauto with freeDB. reflexivity.
      + specialize (IHHc Hf1). exrepnd.
        eexists; eauto with freeDB.
  Qed.

  Lemma finiteTausEuttCIff
        (T : Type) (a1 a2 : itree E T):
    (forall n : nat, RTopN euttC n a1 a2) ->
    finite_taus a1 <-> finite_taus a2.
  Proof using.
    intros Hyp.
    split;[eauto using finiteTausEuttC |].
    apply finiteTausEuttC.
    pose proof (@euttCIndSymm T).
    firstorder.
  Qed.

  Lemma impliesEuttC {T} a1 a2:
    (@euttIndC  T) a1 a2
    ->
    (@euttInd  T) a1 a2.
  Proof using invertDoEq2.
    intros Hn.
    hnf in Hn.
    hnf. intros n. revert  a1 a2 Hn.
    induction n; intros; [hnf; auto |].
    rewrite RTopNS.
    hnf.
    split;[apply finiteTausEuttCIff; assumption |].
    intros t1 t2 H1t H2t.
    hnf in H1t, H2t.
    repnd.
    hnf.
    apply untausAsDelay in H1t.
    apply untausAsDelay in H2t.
    exrepnd.
    subst.
    rename n0 into n2.
    pose proof Hn as Hnb.
    (* t1 and t2 must be (Ret _) or (Do _) *)
    specialize (Hn (1+ (n1 + n2))).
    apply DelaysAddLR in Hn.
    rewrite RTopNS in Hn.
    hnf in H1t0.
    hnf in H2t0.
    inverts Hn; simpl in *; try contradiction; [|];
      constructor;[].
    clear H.
    GC. intros.
    apply IHn.
    clear IHn.
    revert Hnb invertDoEq2. 
    clear.
    intros ?  ? n.
    rename Hnb into Hn.
    specialize (Hn ((S n)+ (n1 + n2))).
    apply DelaysAddLR in Hn.
    rewrite RTopNS in Hn.
    apply invertEuttVis with (x0:=x) in Hn.
    assumption.
  Qed.

  SearchAbout eutt_.
  Fixpoint unDelays {T}(n:nat) (t: itree E T) {struct n}: nat * itree E T :=
    match n with
    |0 => (0, t)
    | S n =>
      match t with
      | Ret _ => (n, t)
      | Vis _ _ => (n, t)
      | Tau t => pairMapl S (unDelays n t)
      end
    end.

  Lemma impliesEuttIndWLOG {T} a1 a2 n:
    fst (unDelays n a2) <= fst (unDelays n a1) (* WLOG because of symmetry *)
    ->   RTopN (@eutt_ E T)  n a1 a2
    -> 
    RTopN euttC  n a1 a2.
  Proof using.
    revert a1 a2.
    induction n; auto;[].
    intros ? ? ? Hr.
    rewrite RTopNS in *.
    hnf in Hr. repnd.
    remember ((unDelays (S n) a1)) as a1c.
    destruct a1c as [a1nd a1d].
    simpl in *.
  Abort.

  Lemma impliesEuttInd {T} a1 a2 n:
    RTopN (@eutt_ E T)  n a1 a2
    -> 
    RTopN euttC   n a1 a2.
  Proof using.
  Abort.

  
  Lemma impliesEuttInd {T} a1 a2:
    (@euttIndC  T) a1 a2
    <->
    (@euttInd  T) a1 a2.
  Abort.


  (** we we dont want to use euttC for destructing,
     we can convert the hypothesis to eutt (deepspec)
     and get better elim principles *)
  Lemma euttCCont {T}:
    inclusion _
              (@GFPC _ (@euttC E T))
              (@euttC _ _ (@GFPC _ (@euttC E T))) .
  Proof using invertDoEq2.
    intros x y Hp.
    specialize (Hp 1) as Hp1.
    rewrite RTopNS in Hp1.
    induction Hp1; [ constructor; eauto | constructor
                     | | | eauto].
    - clear H. intros x n. specialize (Hp (S n)).
      rewrite RTopNS in Hp.
      eauto using invertEuttVis.
    - clear H.
      constructor. intros n.
      (*    induction n; [ hnf; auto|].
    rewrite RTopNS. *)
      specialize (Hp (2+ n)).
      rewrite plus_comm in Hp.
      apply (@DelaysAddLR _ _ _ 1 1 n) in Hp. assumption.
    - eapply Eutt_TauL; eauto.
      apply IHHp1.
      clear IHHp1 Hp1.
      apply (DelaysGFPCLRIff _ _ 1 0) . assumption.
    - eapply Eutt_TauR; eauto.
      apply IHHp1.
      clear IHHp1 Hp1.
      apply (DelaysGFPCLRIff _ _ 0 1) . assumption.
  Qed.
  Print Assumptions euttCCont.

  Section NonTrivRel.
    Context  {T:Type}.

    Lemma untausInfDelay (u : itree E T):
      untaus' _ _ u (infDelay)
      -> u = infDelay.
    Admitted.
    
    Example euttIndCCounterEx (a:T):
      ~((@euttIndC  T) (Ret a) infDelay).
    Proof using.
      intros Hc.
      hnf in Hc.
      specialize (Hc 1).
      rewrite RTopNS in Hc.
      remember (Ret a) as l.
      remember infDelay as r.
      induction Hc;
        try (rewrite infDelayUnfold in Heqr;
             discriminate);[].
      subst. clear Hc.
      rewrite infDelayUnfold in Heqr.
      inverts Heqr.
      auto.
    Qed.

  End NonTrivRel.
End Eff.
