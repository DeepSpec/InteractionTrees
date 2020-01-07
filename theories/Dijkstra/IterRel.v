From Paco Require Import paco.

Section IterRel.

  Context (A : Type).
  Context (r : A -> A -> Prop).

  Variant not_wf_F (F : A -> Prop) (a : A) : Prop :=
    | not_wf (a' : A) (Hrel : r a a') (Hcorec : F a') .
  Hint Constructors not_wf_F.

  Lemma not_wf_F_mono sim sim' a 
        (IN : not_wf_F sim a)
        (LE : sim <1= sim') : not_wf_F sim' a.
  Proof.
    destruct IN. eauto.
  Qed.
        
  Lemma not_wf_F_mono' : monotone1 not_wf_F.
  Proof.
    red. intros. eapply not_wf_F_mono; eauto.
  Qed.
  Hint Resolve not_wf_F_mono' : paco.

  Definition not_wf_from : A -> Prop :=
    paco1 not_wf_F bot1.

End IterRel.


