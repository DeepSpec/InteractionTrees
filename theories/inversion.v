Require Import SquiggleEq.UsefulTypes.
Require Import ITree.ITree.
Require Import Coq.Logic.FunctionalExtensionality.
Import EqNotations.
Require Import Coq.Logic.Eqdep_dec.
Require Import EqdepFacts.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.

Section Observe.
  Context {e: Type->Type}.
  Fixpoint observeD (n : nat) {t} (p : itree e t) : itree e t :=
    match n with
    | 0 => p
    | S n => match p with
            | Ret x => Ret x
            | Vis e k => Vis e (fun x => observeD n (k x))
            | Tau x => Tau (observeD n x)
            end
    end.
  
  Lemma observeDEq n {t} (p : itree e t) :
    observeD n p = p.
  Proof using.
    revert dependent t.
    induction n; [ reflexivity | ].
    intros. simpl.
    destruct p; eauto;[ | ].
    - f_equal. apply functional_extensionality.
      eauto.
    -  f_equal. eauto.
  Qed.
  
  Lemma observeDEq1 {t} (p : itree e t) :
    observeD 1 p = p.
  Proof using.
    intros. simpl.
    destruct p; reflexivity.
  Defined.
End Observe.
Section InfDelay.
  Context {E: Type -> Type} {T:Type}.

CoFixpoint infDelay : itree E T :=
  Tau infDelay.

Lemma infDelayUnfold :
  infDelay = Tau infDelay.
Proof using.
  symmetry.
  rewrite <- (observeDEq 1).
  reflexivity.
Qed.

End InfDelay.

Definition extractDo {E} {T} (p:  itree E T) :
  {b:bool & if b then {A:Type & (E A) * (A -> itree E T)} else unit}%type.
  refine (
      match p with
      | Ret _ => existT _ false tt
      | Vis o k => existT _ true (existT _ _ (o, k))
      | Tau d => existT _ false tt
      end).
Defined.

Lemma invertDoEq {E} {T X1 X2 : Type} (e1 : E X1)
      (e2 : E X2)
      (k1 : X1 -> itree E T)  (k2 : X2 -> itree E T):
  (Vis e1 k1) = (Vis e2 k2) ->
  {p:X1=X2 | (rew p in e1)=e2 /\ (rew [fun U => U -> itree E T] p in k1)=k2}.
Proof.
  intros Hyp.
  apply (f_equal extractDo) in Hyp.
  simpl in Hyp.
  apply inj_pair2_eq_dec in Hyp;[ | apply Bool.bool_dec].
  apply eq_sigT_sig_eq in Hyp.
  exrepnd.
  exists H. subst. simpl in *. inverts Hyp0. auto.
Qed.


Class InvertTauEq (E:Type->Type):= invertTauEq:  forall {T X : Type} (e : E X)
                                                  (k1 k2 : X -> itree E T), 
      (Vis e k1) = (Vis e k2) -> k1=k2.

(* this is a sufficient condition for InvertTauEq *)
Class DecidableEffRet {E:Type->Type} {Code:Type}:=
  {
    encodeRetType : forall T, E T -> Code;
    decodeRetType :  Code -> Type;
    deqCode: UsefulTypes.DeqSumbool Code;
    encodeDecodeId : forall  T (e: E T), T = decodeRetType (encodeRetType _ e);
  }.


Definition transportToDecodeType {E} {Code} (encode: forall T, E T -> Code)
           (decode: Code -> Type)
           (deqCode: UsefulTypes.DeqSumbool Code)
           (encodeDecodeId : forall  T (e: E T), T = decode (encode _ e))
           (P:Type->Type) (def: forall A, P A)
           (c:Code)
           (U:Type)
           (e: E U)
           (p:  P U) : (P (decode c)).
    destruct (UsefulTypes.decSumbool (encode _ e = c)) as [peq |];
      [| exact (def _)].
    destruct peq.
    specialize (encodeDecodeId _ e).
    destruct encodeDecodeId.
    assumption.
 Defined.


Section Inversion.
  Context {E : Type -> Type}  {Code: Type} {invEC : @DecidableEffRet E Code}.

  Definition projectDoK {T}
             (c:Code) (p:  itree E T): ((decodeRetType c) -> itree E T).
    refine (
        match p  with
        | Vis e k => _
        | _ => fun _ => infDelay
        end
      ).
    rename T0 into U.
    pose proof (@transportToDecodeType E Code encodeRetType decodeRetType  deqCode encodeDecodeId (fun U => U ->  itree E T)) as X.
    simpl in X.
    specialize (X (fun _ _ => infDelay)).
    specialize (X c U e k). assumption.
  Defined.

Lemma    encodeDecodeIdRefl : forall E U Code (e:E U) (P: Type -> Type)
          encodeRetType
           (decodeRetType : Code -> Type)
           deqCode
           encodeDecodeId
                           (def: forall A, P A)
                           (p: P U),
        transportToDecodeType
          encodeRetType
           decodeRetType
           deqCode
           encodeDecodeId
           P
           def
           (encodeRetType _ e)
           U
           e
           p
        = (@UsefulTypes.transport _ _ _
                                  P (encodeDecodeId _ e) p).
Proof using.
  intros.
  unfold transportToDecodeType.
  rewrite DeqSumboolRefl.
  reflexivity.
Qed.

  Lemma  projectDoKCorrect : forall U T (e:E U) (k: U -> itree E T),
      (projectDoK
         (encodeRetType _ e)
         (Vis e k))
      = (@UsefulTypes.transport _ _ _
                                (fun T => T -> itree E _) (encodeDecodeId _ e) k).
  Proof using.
    intros. simpl.
    rewrite encodeDecodeIdRefl .
    reflexivity.
  Qed.
  
  Global Instance invertTauEqGen : InvertTauEq E.
  Proof using Code invEC.
    intros ? ? ? ? ? H.
    set (y := (@projectDoK T
                           (@encodeRetType E Code invEC X e))).
    apply (f_equal y) in H.
    subst y.
    pose proof (projectDoKCorrect _ _ e k1).
    pose proof (projectDoKCorrect _ _ e k2).
    rewrite H in H0. clear H.
    rewrite H0 in H1. clear H0.
    destruct  (encodeDecodeId X e) .
    simpl in *. assumption.
  Qed.

End Inversion.


Module BinaryInf.

  Require Import bbv.Word.
  Inductive E: Type -> Type :=
  | Ab : forall s:nat, Word.word s -> E (Word.word s)
  | An : bool -> E nat.

  Definition encodeType T (e: E T) : option nat :=
    match e with
    | Ab s _ => Some s
    | An _ => None
    end.
    
  Definition decodeType (on: option nat) : Type :=
    match on with
    | Some s => Word.word s
    | None => nat
    end.

    (* the stdlib should have this *)
  Lemma eqDecRefl s :
    PeanoNat.Nat.eq_dec s s = left eq_refl.
  Proof using.
    induction s; simpl; eauto.
    rewrite IHs. reflexivity.
  Qed.

    
  Eval compute in (optionDeqSumbool nat _ (Some 2) (Some 2)).

  Global Instance invReq : @DecidableEffRet E (option nat).
  Proof using.
    eapply Build_DecidableEffRet
      with
        (encodeRetType := encodeType)
        (decodeRetType := decodeType).
    apply (optionDeqSumbool _ PeanoNat.Nat.eq_dec).

    intros ? ?.
    destruct e; reflexivity.
    
  Qed.


  Lemma invertDoEqLemma  : InvertTauEq E.
  Proof using.
    eauto with typeclass_instances.
  Qed.

  (* Below, we do the same proof manually;
this manual proof was the inspiration of the generic
approach above *)
  Require Import Arith.
  Require Import SquiggleEq.UsefulTypes.
  Definition extractDoB (b:bool) (s: nat) {T} (p:  itree E T) : ((if b then (Word.word s)  else nat) -> itree E T).
    refine (
        match p  with
        | Vis x k => _
        | _ => fun _ => infDelay
        end
      ).
    destruct x.
  - destruct b; [ | exact (fun _ => infDelay)].
    destruct (PeanoNat.Nat.eq_dec s0 s)
      ; [ | exact (fun _ => infDelay)].
    destruct e. exact k.
   - destruct b;  try exact k; exact (fun _ => infDelay).
   Defined.

  Lemma invertDoEq2  : InvertTauEq E.
  Proof using.
    intros ? ? ? ? ? H.
    destruct e.
    - apply (f_equal (extractDoB true s)) in H. simpl in H.
      rewrite eqDecRefl in H.
      assumption.
    - apply (f_equal (extractDoB false 0)) in H. simpl in H. assumption.
  Qed.

End BinaryInf.
