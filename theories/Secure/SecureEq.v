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
     Dijkstra.TracesIT
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Variant nonempty (A : Type) : Prop := ne (a : A).

Class Preorder :=
  {
    L : Type;
    leq : L -> L -> Prop;
  }.

(* will need more propositional constrainst on Preorders *)

Section SecureUntimed.
  Context {E : Type -> Type} {R1 R2 : Type}.
  Context (Label : Preorder).
  Context (priv : forall A, E A -> L).
  Context (RR : R1 -> R2 -> Prop).


  Inductive secure_eqitF (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop := 

    (* eqitF constructors *)
    | secEqRet r1 r2 : RR r1 r2 -> secure_eqitF b1 b2 l vclo sim (RetF r1) (RetF r2)
    | secEqTau t1 t2 : sim t1 t2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) (TauF t2)
    | secEqTauL t1 ot2 (CHECK : b1) : secure_eqitF b1 b2 l vclo sim (observe t1) ot2 -> secure_eqitF b1 b2 l vclo sim (TauF t1) ot2
    | secEqTauR ot1 t2 (CHECK : b2) : secure_eqitF b1 b2 l vclo sim ot1 (observe t2) -> secure_eqitF b1 b2 l vclo sim ot1 (TauF t2)
    (* info_flow protecting coinductive constructors *)
    | EqVisPriv {A} (e : E A) k1 k2 (SECCHECK : leq (priv A e) l) : 
        ((forall a, vclo sim (k1 a) (k2 a) : Prop)) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (VisF e k2)
    | EqVisUnPrivTauLCo {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim (k1 a) t2) -> secure_eqitF b1 b2 l vclo sim (VisF e k1) (TauF t2)
    | EqVisUnPrivTauRCo {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim t1 (k2 a)) -> secure_eqitF b1 b2 l vclo sim (TauF t1) (VisF e k2)
    | EqVisUnPrivVisCo {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l) :
        (forall a b, vclo sim (k1 a) (k2 b)) -> secure_eqitF b1 b2 l vclo sim (VisF e1 k1) (VisF e2 k2)
    (* info_flow protecting inductive constructors *)
    | EqVisUnPrivLInd {A} (e : E A) k1 t2 (CHECK : b1) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe (k1 a)) (observe t2) ) ->
        secure_eqitF b1 b2 l vclo sim (VisF e k1) (observe t2)
    | EqVisUnPrivRInd {A} (e : E A) t1 k2 (CHECK : b2) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, secure_eqitF b1 b2 l vclo sim (observe t1) (observe (k2 a) )) ->
        secure_eqitF b1 b2 l vclo sim (observe t1) (VisF e k2)
    (*| (halt : E A) k (Hempty : empty A) (r) : forall r', RR r' r -> eqit_secure (Vis halt k) (Ret r)
      SecureOutput

      cofix t := Vis SecretOutput (fun _ => t)
      cofix t := Tau t ≅ Tau Tau Tau ...

     *)
  .

  Hint Constructors secure_eqitF : core.

  Definition secure_eqit_ (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => secure_eqitF b1 b2 l vclo sim (observe t1) (observe t2).

  Hint Unfold secure_eqit_ : core.

  Lemma secure_eqitF_mono b1 b2 l x0 x1 vclo vclo' sim sim'
        (IN: secure_eqitF b1 b2 l vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    secure_eqitF b1 b2 l vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma secure_eqit_mono b1 b2 l vclo (MON: monotone2 vclo) : monotone2 (secure_eqit_ b1 b2 l vclo).
  Proof.
    do 2 red. intros; eapply secure_eqitF_mono; eauto.
  Qed.

  Hint Resolve secure_eqit_mono : paco.

  Definition eqit_secure b1 b2 l := paco2 (secure_eqit_ b1 b2 l id) bot2.

  (* want and eqitC_secure which could help prove some interesting stuff

   *)


  (*
    Note that this is not reflexive (think it is symmetric and transitive) 
    Suppose SecureFlip : E bool has privilege 1 and trigger SecureFlip is 
    observed at privilege 0. We end to prove eqit_secure false false 0 of it 
    requires us to show forall a b, eqit_secure false false 0 (Ret a) (Ret b)
    this is false, suppose a = true and b = false and the relation is equality

   *)


End SecureUntimed.

Hint Resolve secure_eqit_mono : paco.

Hint Constructors secure_eqitF : core.

Definition NatPreorder : Preorder :=
  {|
  L := nat;
  leq := fun n m => n <= m
  |}.

Section SecureUntimedUnReflexive.
  
  Variant NonDet : Type -> Type :=
    | SecureFlip : NonDet bool
    | PublicOut : NonDet unit
    | Halt : NonDet void

. 

(* 
CoInductive itree E R :=
...
| Vis {A : Type} (e : E A) (k : A -> itree E R)

suppose A := void

k ≅ empty_cont

bind (Vis Halt k1) k2 ≅ Vis Halt k1 

E := HaltE unit

Definition halt : itree E R := Vis HaltE (fun _ => Tau Tau ...)

*)

  Definition priv_counter : forall A, NonDet A -> nat :=
    fun _ e =>
      match e with
      | SecureFlip => 1
      | PublicOut => 0 
      | Halt => 10
      end.
  

  Variant Exc : Type -> Type :=
    Throw : Exc void.

  Definition refl_counter : itree NonDet bool := trigger SecureFlip. (* b := Flip; return b *)

  Lemma refl_counter_counter : ~ eqit_secure NatPreorder priv_counter eq true true 0 refl_counter refl_counter.
    Proof.
      intro Hcontra. punfold Hcontra; try eapply secure_eqit_mono; eauto.
      red in Hcontra. cbn in *. inv Hcontra; ITrace.inj_existT; subst.
      - cbv in SECCHECK. inv SECCHECK.
      - specialize (H0 true false). pclearbot. pinversion H0; try eapply secure_eqit_mono; eauto.
        discriminate.
      - rewrite H3 in H0. clear H3. specialize (H0 true). cbn in *.
        inv H0; ITrace.inj_existT; subst. specialize (H2 false). rewrite H in H2.
        inv H2. discriminate.
      -  rewrite H in H0. injection H0; intros; ITrace.inj_existT; subst; ITrace.inj_existT; subst.
         specialize (H1 true). cbn in *. inv H1; ITrace.inj_existT; subst; ITrace.inj_existT; subst.
         rewrite H6 in H3. specialize (H3 false). cbn in *. inv H3; discriminate.
    Qed.


    Lemma halt_eq_all : forall R (t : itree NonDet R) k , eqit_secure NatPreorder priv_counter eq true true 0 (Vis Halt k) t.
    Proof.
      intros. pfold. red. cbn. constructor; auto; try intros; try contradiction.
      intro Hc; inv Hc.
    Qed.
    (*transitivity problems in presence of E void *)
    Definition refl_counter2 : itree NonDet unit := ITree.bind refl_counter (fun b : bool => if b then Ret tt else trigger PublicOut).
    (* b := SecretFlip; if b then return tt else PublicOut; return tt*)
    Lemma refl_counter2_counter : ~ eqit_secure NatPreorder priv_counter eq true true 0 refl_counter2 refl_counter2.
      Proof.
        unfold refl_counter2. intro Hcontra. punfold Hcontra; try eapply secure_eqit_mono; eauto.
        red in Hcontra. cbn in Hcontra. inv Hcontra; ITrace.inj_existT; subst.
        - inv SECCHECK.
        - specialize (H0 true false). pclearbot. punfold H0; try eapply secure_eqit_mono; eauto.
          red in H0. cbn in *. inv H0; ITrace.inj_existT; subst.
          cbn in *. apply SECCHECK; auto.
        - rewrite H3 in H0; clear H3. specialize (H0 true). cbn in *.
          inv H0; ITrace.inj_existT; subst; ITrace.inj_existT.
          specialize (H2 false). rewrite H in H2. cbn in *. inv H2; 
          ITrace.inj_existT; subst; apply SECCHECK1; constructor.
        - rewrite <- H0 in H. injection H; intros; ITrace.inj_existT; subst; ITrace.inj_existT; subst.
          specialize (H1 true). inv H1; ITrace.inj_existT; subst.
          rewrite H6 in H3. specialize (H3 false). cbn in *.
          inv H3; ITrace.inj_existT; subst. apply SECCHECK1; constructor.
      Qed.
          

Section eqit_secureC.
  (* might not be the order I eventually want but whatever*)
  Context {E: Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  Context (Label : Preorder) (priv : forall A, E A -> L) (l : L).


  Variant eqit_secure_trans_clo (b1 b2 b1' b2' : bool) (r : itree E R1 -> itree E R2 -> Prop) : 
    itree E R1 -> itree E R2 -> Prop :=
        eqit_secure_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit_secure Label priv RR1 b1 b1' l t1 t1')
      (EQVr: eqit_secure Label priv RR2 b2 b2' l t2 t2')
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      eqit_secure_trans_clo b1 b2 b1' b2' r t1 t2.

  Hint Constructors eqit_secure_trans_clo : core.

  Definition eqit_secureC b1 b2 := eqit_secure_trans_clo b1 b2 false false.
  Hint Unfold eqit_secureC : core.

  Lemma eqit_secureC_mon b1 b2 r1 r2 t1 t2 
    (IN : eqit_secureC b1 b2 r1 t1 t2)
    (LE: r1 <2= r2) : 
    eqit_secureC b1 b2 r2 t1 t2.
  Proof.
    destruct IN; eauto.
  Qed.


  

End eqit_secureC.
(*
Lemma eqit_secureC_wcompat :  forall b1 b2 E R1 R2 (RR : R1 -> R2 -> Prop ) vclo
      Label priv l
      (MON : monotone2 vclo)
      (CMP : compose (eqit_secureC RR Label priv l b1 b2) vclo <3= 
             compose vclo (eqit_secureC RR Label priv l b1 b2))
, (forall A, E A -> nonempty A) -> wcompatible2 (@secure_eqit_ E R1 R2 Label priv RR b1 b2 l vclo) 
                                         (eqit_secureC RR Label priv l b1 b2) .
Proof.
  (*Pay attention to where you use the nonempty condition, this might be false*)
  intros. constructor.
  { red. intros; eapply eqit_secureC_mon; eauto. }
  intros. dependent induction PR. 
  (* figure out the monotone thing*)
  punfold EQVl. punfold EQVr. red in EQVl. red in EQVr.
  red in REL. red. hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y. hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
    (* EqVisUnPrivRLInd slight problem with syntactic form of the constructor,
       nothing deep *)
    remember (RetF r1) as rr1. assert (rr1 = observe (Ret r1)); subst; auto.
    rewrite H4. constructor; eauto. intros. eapply H1; eauto.
  - unfold compose in CMP. remember (TauF t1) as x. hinduction EQVl before r; intros; subst; try inv Heqx;
    try inv CHECK; eauto.
    + remember (TauF t4) as y. pclearbot. 
      (* think I might have a lead on the problem, should H0 have vclo not id here?*)
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; eauto.
      * constructor. gclo. econstructor; eauto with paco.
      * eapply EqVisUnPrivTauRCo; eauto. intros. 
        eapply MON;
           try (intros; eapply gpaco2_clo; auto; apply PR).
        eapply CMP.
        econstructor; try eapply H0; eauto.
        (* in analogous case in other proof, I had more evidence about vclo
           seems like it should be coming from a coinductive case somewhere around here
         *)
        (* this seems problematic, perhaps I use vclo in some incorrect way
           if vclo was specialized to id, this would be fine*)
        admit.
      * assert (TauF t1 = observe (Tau t1)); auto. rewrite H4. eapply EqVisUnPrivRLInd; eauto.
        intros. eapply H1; eauto.
    + pclearbot. remember (TauF t3) as y.
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto.
      * pclearbot. apply EqVisUnPrivTauLCo; auto. intros. eapply MON.
        -- eapply CMP. econstructor; try apply H1; eauto.
           (* r vclo issue *) admit.
        -- intros. gclo.
      admit. (*Iwant b1 to be true here but O don't know if it is *)
      * admit.
      * admit.
  - inv CHECK. remember (TauF t1) as x. 
    hinduction EQVl before r; intros; try inv Heqx; try inv CHECK; subst; eauto. 
    + constructor; eauto. eapply IHREL; eauto. pclearbot. punfold H0.
    + constructor; eauto; intros. eapply IHREL; eauto. specialize (H0 a).
      pclearbot. punfold H0.
  - inv CHECK. remember (TauF t2) as y.
    hinduction EQVr before r; intros; try inv Heqy; try inv CHECK; subst; eauto.
    + constructor; auto. eapply IHREL; eauto. pclearbot. punfold H0.
    + constructor; auto. intros. specialize (H0 a). pclearbot. punfold H0.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; try inv Heqx; try inv CHECK; subst; 
    ITrace.inj_existT; subst; eauto.
    + pclearbot. remember (VisF e0 k3) as y.
      hinduction EQVr before r; intros; try inv Heqy; try inv CHECK; subst;
      ITrace.inj_existT; subst; eauto.
      * constructor; auto. intros. eapply MON.
        -- eapply CMP. pclearbot. econstructor; eauto; try apply H0. apply H1.
        -- intros. apply gpaco2_clo; auto.
      * pclearbot. assert (TauF t1 = observe (Tau t1) ); auto. rewrite H3. 
        eapply EqVisUnPrivTauLCo; eauto. intros.
        eapply MON.
        -- eapply CMP. pclearbot. econstructor; eauto.
           apply H1. apply H0.
        -- intros. apply gpaco2_clo; auto.
      * pclearbot. eapply EqVisUnPrivVisCo; eauto. intros.
        eapply MON.
        -- eapply CMP. pclearbot. red. econstructor; eauto.
           apply H1. apply H0.
        -- intros. apply gpaco2_clo; auto.
      * (* inductive case *) 
        assert (VisF e0 k0 = observe (Vis e0 k0)); auto. rewrite H4.
        remember (Vis e0 k0) as t. constructor; auto; subst. intros.
        eapply H1; eauto. 
    + pclearbot. remember (VisF e0 k0) as x.
      hinduction EQVr before r; intros; subst; try inv Heqx; try inv CHECK;
      ITrace.inj_existT; subst; try contradiction; eauto.
    + pclearbot. remember (VisF e k3) as x.
      hinduction EQVr before r; intros; subst; try inv Heqx; try inv CHECK;
      ITrace.inj_existT; subst; try contradiction; eauto.
  - remember (VisF e k1) as x. 
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ITrace.inj_existT; subst; 
    try contradiction.
    + constructor; eauto.
    + pclearbot. remember (TauF t2) as y.
      hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK;
      ITrace.inj_existT; subst; eauto.
      * constructor. apply gpaco2_clo. pclearbot.
        assert (nonempty A0); auto. inv H3.
        econstructor; eauto. apply H1.
        Unshelve. all : auto.
        (* seems like I can just go through and do all of these manually, annoying but doable*)
        (* basically reverse of the other problem need to prove r but have vclo r*)
        admit.
      *  eapply EqVisUnPrivTauRCo; eauto. intros.
         eapply MON.
         -- eapply CMP; eauto. econstructor; eauto.
            apply H1. pclearbot. apply H0.
         -- intros. apply gpaco2_clo. auto.
      * assert (TauF t0 = observe (Tau t0)); auto. rewrite H4.
        eapply EqVisUnPrivRLInd; eauto. intros. eapply H1; eauto.
   + pclearbot. remember (TauF t2) as y.
      hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK;
      ITrace.inj_existT; subst; eauto.
      * pclearbot. apply EqVisUnPrivTauLCo; auto.
        intros. eapply MON.
        -- eapply CMP; eauto. econstructor; eauto.
            apply H1. 
         -- intros. apply gpaco2_clo. auto.
      * pclearbot. apply EqVisUnPrivVisCo; auto.
        intros. eapply MON.
        -- eapply CMP; eauto. econstructor; eauto.
           apply H1. apply H0.
        -- intros. apply gpaco2_clo. auto.
      * assert (VisF e1 k0 = observe (Vis e1 k0) ); auto. rewrite H4.
        remember (Vis e1 k0) as t. constructor; auto; subst. intros.
        eapply H1; eauto.
    + constructor; auto. intros. eapply H1; eauto.
  - remember (VisF e k2) as x.
    hinduction EQVr before r; intros; subst; try inv Heqx; try inv CHECK; ITrace.inj_existT; subst; 
    try contradiction; eauto.
    + pclearbot. remember (TauF t0) as y.
      hinduction EQVl before r; intros; subst; try inv Heqy; try inv CHECK; ITrace.inj_existT; subst; try contradiction; eauto.
      * constructor. apply gpaco2_clo. pclearbot. econstructor; eauto.
        apply H1. admit. (* vclo r problem again *)
      * eapply EqVisUnPrivTauLCo; eauto. intros. pclearbot.
        eapply MON.
        -- eapply CMP; eauto. econstructor; eauto. apply H0.
           apply H1.
        -- intros; apply gpaco2_clo; auto.
      * assert (TauF t1 = observe (Tau t1)); auto. rewrite H4.
        eapply EqVisUnPrivLInd; eauto. intros. eapply H1; eauto.
    + pclearbot. remember (TauF t1) as y.
      hinduction EQVl before r; intros; subst; try inv Heqy; try inv CHECK; ITrace.inj_existT; subst; try contradiction; eauto.
      * pclearbot. eapply EqVisUnPrivTauRCo; eauto. intros.
        eapply MON.
        -- eapply CMP. econstructor; eauto. apply H1.
        -- intros. apply gpaco2_clo. auto.
      * constructor; auto. intros. eapply MON.
        -- eapply CMP. econstructor; eauto. pclearbot.
           apply H0. apply H1.
        -- intros. apply gpaco2_clo. auto.
      * assert (VisF e1 k0 = observe (Vis e1 k0) ); auto.  rewrite H4. eapply EqVisUnPrivLInd; eauto. intros. eapply H1; eauto.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; ITrace.inj_existT; subst; eauto.
    + pclearbot. remember (VisF e2 k3) as y. 
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; ITrace.inj_existT; subst; eauto.
      * pclearbot. constructor; eauto. intros.
        eapply MON.
        -- eapply CMP. econstructor; eauto. apply H1. apply H0.
        -- intros. apply gpaco2_clo. auto.
      * pclearbot. eapply EqVisUnPrivTauLCo; eauto.
        intros. eapply MON.
        -- eapply CMP. econstructor; eauto. apply H1. apply H0.
        -- intros. apply gpaco2_clo. auto.
      * pclearbot. constructor; eauto. intros.
        eapply MON.
        -- eapply CMP. econstructor; eauto. apply H1.
           apply H0.
        -- intros. apply gpaco2_clo. auto.
      * assert (VisF e1 k0 = observe (Vis e1 k0)); auto. rewrite H4.
       eapply EqVisUnPrivRLInd; eauto. intros. eapply H1; eauto.
   + pclearbot. remember (VisF e2 k0) as y. 
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; ITrace.inj_existT; subst; eauto.
     * pclearbot.  eapply EqVisUnPrivTauRCo; eauto. intros.
       eapply MON.
       -- eapply CMP. econstructor; eauto. apply H1. apply H0.
       -- intros. apply gpaco2_clo. auto.
     * constructor. apply gpaco2_clo. econstructor; eauto.
       apply H1. pclearbot. eapply H0. (* r vclo issue *) admit.
     * pclearbot. eapply EqVisUnPrivTauRCo; eauto. intros.
       eapply MON.
       -- eapply CMP. econstructor; eauto. apply H1. apply H0.
       -- intros. apply gpaco2_clo. auto.
     * assert (TauF t3 = observe (Tau t3)); auto. rewrite H4.
       eapply EqVisUnPrivRLInd; eauto. intros. eapply H1; eauto.
   + pclearbot. remember (VisF e3 k3) as y.
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; ITrace.inj_existT; subst; eauto.
     * pclearbot. constructor; eauto. intros.
       eapply MON.
       -- eapply CMP. econstructor; eauto. apply H1. apply H0.
       -- intros. apply gpaco2_clo. auto.
     * pclearbot. eapply EqVisUnPrivTauLCo; eauto. intros.
       eapply MON.
       -- eapply CMP. econstructor; eauto. apply H1. apply H0.
       -- intros. apply gpaco2_clo. auto.
     * pclearbot. constructor; eauto. intros.
       eapply MON.
       -- eapply CMP. econstructor; eauto. apply H1. apply H0.
       -- intros. apply gpaco2_clo. auto.
     * assert (VisF e1 k0 = observe (Vis e1 k0)); auto. rewrite H4.
       eapply EqVisUnPrivRLInd; eauto. intros. eapply H1; eauto.
 - remember (VisF e k1) as x.
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; ITrace.inj_existT; subst; eauto.
   + pclearbot. constructor; eauto. intros. eapply H2; eauto. specialize (H0 a).
     punfold H0.
   + (* using nonempty condition here (note that the weaker (no high sec halts, would also work I think) ) *)
     assert (nonempty A0); eauto. inv H3.
     pclearbot. constructor; eauto. eapply H2; eauto. 
     pstep_reverse.
   + pclearbot. constructor; eauto. intros.
     assert (nonempty A0); eauto. inv H3.
     eapply H2; eauto. specialize H0 with (b := a0). pstep_reverse.  
 - remember (VisF e k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; ITrace.inj_existT; subst; eauto.
   + pclearbot. constructor; auto. intros.
     eapply H2; eauto. pstep_reverse.
   + assert (nonempty A0); auto. inv H3.
     constructor; auto. eapply H2; eauto. pstep_reverse.
     pclearbot.
     eapply H0; auto.
   + pclearbot. assert (nonempty A0); auto. inv H3.
     constructor; auto. intros. eapply H2; eauto.
     specialize H0 with (b := a).
     pstep_reverse.
     Unshelve .
     assert (nonempty A0); auto. 
Admitted.
*)

Ltac unpriv_co := try apply EqVisUnPrivVisCo; 
                  try apply EqVisUnPrivTauLCo; 
                  try apply EqVisUnPrivTauRCo; 
                  auto; intros.

Ltac unpriv_ind := try apply EqVisUnPrivLInd;
                   try apply EqVisUnPrivRInd;
                   auto; intros.

Ltac gfinal_with H := gfinal; left; apply H.

Ltac ne A := let Hne := fresh "H" in assert (Hne : nonempty A); eauto; inv Hne.

Lemma eqit_secureC_wcompat_id :  forall b1 b2 E R1 R2 (RR : R1 -> R2 -> Prop )
      Label priv l
, (forall A (e : E A), (~ leq (priv _ e) l) -> nonempty A) -> wcompatible2 (@secure_eqit_ E R1 R2 Label priv RR b1 b2 l id) 
                                         (eqit_secureC RR Label priv l b1 b2) .
Proof.
  (*Pay attention to where you use the nonempty condition, this might be false*)
  intros. constructor.
  { red. intros; eapply eqit_secureC_mon; eauto. }
  intros. dependent induction PR. 
  (* figure out the monotone thing*)
  punfold EQVl. punfold EQVr. red in EQVl. red in EQVr.
  red in REL. red. hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y. hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
    (* EqVisUnPrivRLInd slight problem with syntactic form of the constructor,
       nothing deep *)
    remember (RetF r1) as rr1. assert (rr1 = observe (Ret r1)); subst; auto.
    rewrite H4. constructor; eauto. intros. eapply H1; eauto.
  - remember (TauF t1) as x. hinduction EQVl before r; intros; subst; try inv Heqx;
    try inv CHECK; eauto.
    + remember (TauF t4) as y. pclearbot. 
      (* think I might have a lead on the problem, should H0 have vclo not id here?*)
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; eauto.
      * constructor. gclo. econstructor; eauto with paco.
      * unpriv_co.
        gclo. econstructor; eauto with paco. red. auto.
      * assert (TauF t1 = observe (Tau t1)); auto. rewrite H4. 
        unpriv_ind. eapply H1; eauto.
    + pclearbot. remember (TauF t3) as y.
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto.
      -- pclearbot. 
         unpriv_co. 
         gclo. econstructor; try apply H0; eauto with paco. apply H1.
      -- pclearbot. unpriv_co. gclo. 
         econstructor; try apply H1; try apply H0; eauto with paco.
      -- rewrite itree_eta' at 1. unpriv_ind. 
         eapply H1; eauto.
  - inv CHECK. remember (TauF t1) as x. 
    hinduction EQVl before r; intros; try inv Heqx; try inv CHECK; subst; eauto. 
    + constructor; eauto. eapply IHREL; eauto. pclearbot. punfold H0.
    + constructor; eauto; intros. eapply IHREL; eauto. specialize (H0 a).
      pclearbot. punfold H0.
  - inv CHECK. remember (TauF t2) as y.
    hinduction EQVr before r; intros; try inv Heqy; try inv CHECK; subst; eauto.
    + constructor; auto. eapply IHREL; eauto. pclearbot. punfold H0.
    + constructor; auto. intros. specialize (H0 a). pclearbot. punfold H0.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; try inv Heqx; try inv CHECK; subst; 
    ITrace.inj_existT; subst; eauto.
    + pclearbot. remember (VisF e0 k3) as y.
      hinduction EQVr before r; intros; try inv Heqy; try inv CHECK; subst;
      ITrace.inj_existT; subst; eauto.
      * constructor; auto. intros. red. gclo. pclearbot.
         econstructor; try apply H0; try apply H1; eauto with paco. gfinal_with H2.
      * rewrite itree_eta'. pclearbot.
        unpriv_co.
        gclo. econstructor; eauto with paco; try apply H1. apply H0. 
        gfinal_with H2.
      * pclearbot. unpriv_co.
        gclo. econstructor; eauto.
           apply H1. apply H0. gfinal_with H2.
      * (* inductive case *) rewrite itree_eta' at 1.
        unpriv_ind. eapply H1; eauto.
    + pclearbot. remember (VisF e0 k0) as x.
      hinduction EQVr before r; intros; subst; try inv Heqx; try inv CHECK;
      ITrace.inj_existT; subst; try contradiction; eauto.
    + pclearbot. remember (VisF e k3) as x.
      hinduction EQVr before r; intros; subst; try inv Heqx; try inv CHECK;
      ITrace.inj_existT; subst; try contradiction; eauto.
  - remember (VisF e k1) as x. 
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ITrace.inj_existT; subst; 
    try contradiction.
    + constructor; eauto.
    + pclearbot. remember (TauF t2) as y.
      hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK;
      ITrace.inj_existT; subst; eauto.
      * constructor. apply gpaco2_clo. pclearbot.
        assert (nonempty A0); eauto. inv H3.
        econstructor; eauto. apply H1. apply H2; auto.
        Unshelve. auto.
      * ne A0. unpriv_co. pclearbot.
         gclo. econstructor; eauto. apply H1.
         apply H0. gfinal_with H2. Unshelve. auto.
      * rewrite itree_eta' at 1. unpriv_ind.
        eapply H1; eauto.
   + pclearbot. remember (TauF t2) as y.
      hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK;
      ITrace.inj_existT; subst; eauto.
      * ne A0.
        pclearbot. unpriv_co. 
        intros. gclo. econstructor; eauto.
        apply H1. gfinal_with H2. 
      * ne A1.
        pclearbot. apply EqVisUnPrivVisCo; auto.
        intros. gclo. econstructor; eauto. apply H1. apply H0.
        gfinal. left. apply H2. Unshelve. auto. auto.
      * assert (VisF e1 k0 = observe (Vis e1 k0) ); auto. rewrite H4.
        remember (Vis e1 k0) as t. constructor; auto; subst. intros.
        eapply H1; eauto.
    + constructor; auto. intros. eapply H1; eauto.
  - remember (VisF e k2) as x.
    hinduction EQVr before r; intros; subst; try inv Heqx; try inv CHECK; ITrace.inj_existT; subst; 
    try contradiction; eauto.
    + pclearbot. remember (TauF t0) as y.
      hinduction EQVl before r; intros; subst; try inv Heqy; try inv CHECK; ITrace.inj_existT; subst; try contradiction; eauto.
      * assert (Hne : nonempty A0); eauto. inv Hne.
        constructor. apply gpaco2_clo. pclearbot. econstructor; eauto.
        apply H1. apply H2. Unshelve. auto. 
      * assert (Hne : nonempty A0); eauto. inv Hne.
        eapply EqVisUnPrivTauLCo; eauto. intros. pclearbot.
        gclo. econstructor; eauto. apply H0. apply H1. gfinal.
        left. apply H2. Unshelve. auto.
      * assert (TauF t1 = observe (Tau t1)); auto. rewrite H4.
        eapply EqVisUnPrivLInd; eauto. intros. eapply H1; eauto.
    + pclearbot. remember (TauF t1) as y.
      hinduction EQVl before r; intros; subst; try inv Heqy; try inv CHECK; ITrace.inj_existT; subst; try contradiction; eauto.
      * assert (Hne : nonempty A0); eauto. inv Hne.
        pclearbot. eapply EqVisUnPrivTauRCo; eauto. intros.
        gclo. econstructor; eauto. apply H1. gfinal. left. apply H2.
        Unshelve. auto.
      * assert (Hne : nonempty A1); eauto. inv Hne.
        constructor; auto. intros. gclo. pclearbot. 
        econstructor; eauto. apply H0. apply H1. gfinal. left. apply H2.
        Unshelve. auto.
      * assert (VisF e1 k0 = observe (Vis e1 k0) ); auto.  rewrite H4. eapply EqVisUnPrivLInd; eauto. intros. eapply H1; eauto.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; ITrace.inj_existT; subst; eauto.
    + pclearbot. remember (VisF e2 k3) as y. 
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; ITrace.inj_existT; subst; eauto.
      * assert (Hne : nonempty A0); eauto. inv Hne.
        assert (Hne : nonempty B); eauto. inv Hne.
        pclearbot. constructor; eauto. intros.
        gclo. econstructor; eauto. apply H1. apply H0.
        gfinal. left. apply H2.
      * assert (Hne : nonempty B); eauto. inv Hne.
        pclearbot. eapply EqVisUnPrivTauLCo; eauto.
        intros. gclo. econstructor; eauto. apply H1. apply H0. gfinal. left. apply H2. 
        Unshelve. auto.
      * assert (Hne : nonempty B0); eauto. inv Hne.
        pclearbot. constructor; eauto. intros. gclo. econstructor; eauto.
        apply H1. apply H0. gfinal. left. apply H2. Unshelve. auto.
      * assert (VisF e1 k0 = observe (Vis e1 k0)); auto. rewrite H4.
        unpriv_ind.
        eapply H1; eauto.
   + pclearbot. remember (VisF e2 k0) as y. 
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; ITrace.inj_existT; subst; eauto.
     * assert (Hne : nonempty A0); eauto. inv Hne.
       pclearbot.  eapply EqVisUnPrivTauRCo; eauto. intros.
       gclo. econstructor; eauto. apply H1. apply H0. gfinal. left. apply H2.
       Unshelve. auto.
     * assert (Hne : nonempty B); eauto. inv Hne.
       assert (Hne : nonempty A0); eauto. inv Hne.
       constructor. apply gpaco2_clo. econstructor; eauto.
       apply H1. pclearbot. eapply H0. apply H2. Unshelve. auto. auto. 
     * assert (Hne : nonempty B0); eauto. inv Hne.
       assert (Hne : nonempty A0); eauto. inv Hne.
       pclearbot. eapply EqVisUnPrivTauRCo; eauto. intros.
       gclo. econstructor; eauto. apply H1. apply H0.
       gfinal. left. apply H2. Unshelve. auto. auto.
     * assert (TauF t3 = observe (Tau t3)); auto. rewrite H4.
       unpriv_ind. eapply H1; eauto.
   + pclearbot. remember (VisF e3 k3) as y.
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; ITrace.inj_existT; subst; eauto.
     * assert (Hne : nonempty A1); eauto. inv Hne.
       pclearbot. constructor; eauto. intros.
       gclo. econstructor; eauto. apply H1. apply H0. gfinal. left. apply H2.
       Unshelve. auto.
     * assert (Hne : nonempty A1); eauto. inv Hne.
       assert (Hne : nonempty B0); eauto. inv Hne.
       pclearbot. eapply EqVisUnPrivTauLCo; eauto. intros.
       gclo. econstructor; eauto. apply H1. apply H0. gfinal. left. apply H2.
       Unshelve. auto. auto.
     * assert (Hne : nonempty A1); eauto. inv Hne.
       assert (Hne : nonempty B0); eauto. inv Hne.
       pclearbot. constructor; eauto. intros.
       gclo. econstructor; eauto. apply H1. apply H0. gfinal. left. apply H2.
       Unshelve. auto. auto.
     * assert (VisF e1 k0 = observe (Vis e1 k0)); auto. rewrite H4.
       unpriv_ind. intros. eapply H1; eauto.
 - remember (VisF e k1) as x.
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; ITrace.inj_existT; subst; eauto.
   + pclearbot. constructor; eauto. intros. eapply H2; eauto. specialize (H0 a).
     punfold H0.
   + (* using nonempty condition here (note that the weaker (no high sec halts, would also work I think) ) *)
     assert (nonempty A0); eauto. inv H3.
     pclearbot. constructor; eauto. eapply H2; eauto. 
     pstep_reverse. Unshelve. auto.
   + pclearbot. constructor; eauto. intros.
     assert (nonempty A0); eauto. inv H3.
     eapply H2; eauto. specialize H0 with (b := a0). pstep_reverse.  
 - remember (VisF e k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; ITrace.inj_existT; subst; eauto.
   + pclearbot. constructor; auto. intros.
     eapply H2; eauto. pstep_reverse.
   + assert (nonempty A0); eauto. inv H3.
     constructor; auto. eapply H2; eauto. pstep_reverse.
     pclearbot.
     eapply H0; auto. Unshelve. auto.
   + pclearbot. assert (nonempty A0); eauto. inv H3.
     constructor; auto. intros. eapply H2; eauto.
     specialize H0 with (b := a).
     pstep_reverse.
Qed.

Lemma eqit_secure_sym : forall b1 b2 E R1 R2 RR Label priv l (t1 : itree E R1) (t2 : itree E R2),
    eqit_secure Label priv RR b1 b2 l t1 t2 -> eqit_secure Label priv (flip RR) b2 b1 l t2 t1.
Proof.
  intros b1 b2 E R1 R2 RR Label priv l. pcofix CIH.
  intros t1 t2 Hsec. pfold. red. punfold Hsec. red in Hsec.
  hinduction Hsec before r; intros; eauto; pclearbot;
  try (unpriv_co; right; apply CIH; apply H).
  constructor; auto. intros. right. apply CIH; apply H.
Qed.


(*should try a version of this proof that just plays it straight, once we know it is a PER some extra avenues open up
  but uggh this proof is going to be a killer
  *)
Lemma strong_eqit_secure_trans : forall E (R : Type)
                  Label priv l (t1 t2 t3: itree E R),
     (forall (A : Type) (e : E A), ~ leq (priv A e) l -> nonempty A) ->
    eqit_secure Label priv eq false false l t1 t2 ->
    eqit_secure Label priv eq false false l t2 t3 ->
    eqit_secure Label priv eq false false l t1 t3.
Proof.
  intros E R Label priv l t1 t2 t3 HE Ht12 Ht23. 
  eapply gpaco2_init; try eapply eqit_secureC_wcompat_id; eauto with paco.
  generalize dependent t2. generalize dependent t1. generalize dependent t3.
  gcofix CIH0. intros. gclo. econstructor; eauto. apply eqit_secure_sym. eauto; intros.
  - (* back to this question, can I assume something is securely equiv to anything, it is securely equiv to self*) admit.
  - intros. subst. auto.
  - intros. red in H. subst. auto.
Abort.


(* maybe I should start by trying to make this above proof smaller *)
(* I think I need more assumptions from the context*)
(*not sure how confident I am in this lemma, soon I will try working through it to 
  see if it works/what goes wrong*)
Lemma eqit_secure_anything_to_self_aux:
forall (E : Type -> Type) (R1 : Type) (b1 b2 : bool) (R2 : Type) 
    (RR : R1 -> R2 -> Prop) (Label : Preorder) (priv : forall x : Type, E x -> L) 
    (l : L) (A : Type) (r : itree E R1 -> itree E R1 -> Prop),
  (forall (t1 : itree E R1) (t2 : itree E R2),
   eqit_secure Label priv RR b1 b2 l t1 t2 -> r t1 t1) ->
  (forall (t0 : itree E R2) (k1 : A -> itree E R1),
   (forall a : A, paco2 (secure_eqit_ Label priv RR b1 b2 l id) bot2 (k1 a) t0) ->
   forall a b : A, r (k1 a) (k1 b)) ->
  forall (k1 : A -> itree E R1) (a b : A),
  paco2 (secure_eqit_ Label priv eq b1 b2 l id) r (k1 a) (k1 b).
Proof.
  intros E R1 b1 b2 R2 RR Label priv l A r CIH CIH0 k1 a b.
Abort. 
(* this would come pretty directly out of a direct transitivity proof *)
Lemma eqit_secure_anything_to_self : forall b1 b2 E R1 R2 RR Label priv l (t1 : itree E R1) (t2 : itree E R2),
    (forall (A : Type) (e : E A), ~ leq (priv A e) l -> nonempty A) ->
    eqit_secure Label priv RR b1 b2 l t1 t2 -> eqit_secure Label priv eq b1 b2 l t1 t1.
Proof.
  intros b1 b2 E R1 R2 RR Label priv l t1 t2 Hhalt Ht12. generalize  dependent t2. generalize dependent t1.
  pcofix CIH. intros. pfold. red. punfold Ht12. red in Ht12. hinduction Ht12 before r; intros; try auto.
  - pclearbot. constructor. right. eauto.
  - constructor. left. pfold. apply IHHt12; auto.
  - pclearbot. constructor; auto. right. eapply CIH; apply H.
  - pclearbot. apply EqVisUnPrivVisCo; auto.
    left. revert a b. generalize dependent k1. generalize dependent t0. pcofix CIH0. intros.
    (* promising addition to coinductive hypothesis?

*)
    (* if t is no securely equiv to itself, it is securely equiv to nothing? *)
    admit.
  (* this case is problematic the coinductive case requires us to consider if the vis chooses diff paths*)
  - pclearbot. assert (Hne :nonempty A); eauto. inv Hne. constructor. right. eapply CIH.
    apply H with (a := a).
  - pclearbot. (* problematic for same reason *) admit.
  - rewrite itree_eta'. unpriv_ind. pstep_reverse. eapply paco2_mon with (r := bot2); intros; try contradiction. pfold. admit. (* problematic for different but related reason, probably could do a proof similar to the other cases though (assuming those cases are true) just advance coinductively and use H to show that no matter how to continue with k1, you have an equiv tree *)
  - assert (nonempty A); eauto. inv H1. apply H0; auto.
Abort.
 (* although, this might actually not exactly be transitivity when we don't have reflexivity*)
(* one thing that I think is true and would be helpful, if t is securely equivalent to anything else, it is securely equivalent to itself*)


Section Transitivity.


  Context (E : Type -> Type) (R : Type) (Label : Preorder) (priv : forall A, E A -> L).
  Context (l : L).
  Context (Hhalt_vis : forall A (e : E A), nonempty A -> leq (priv A e) l).

End Transitivity.

End SecureUntimedUnReflexive.

Section SecureTimed.

  Variant TimedEv (E : Type -> Type) : Type -> Type :=
    | TE {A : Type} (e : E A) (n : nat) : TimedEv E A.

  Fixpoint handle_timed_aux {E A} (e : E A) (n : nat) : itree E A :=
    match n with
    | 0 => Vis e (fun a => Ret a)
    | S m => Tau (handle_timed_aux e m) end.

  Definition handle_timed {E A} (e : TimedEv E A) : itree E A :=
    match e with TE _ e' a => handle_timed_aux e' a end.


End SecureTimed.
