(* SAZ: I'm not sure where in the library this should live.
    The Monad instance for itree is in ITreeDefinition but we want
    to define Eq1 and MonadLawsE instances too.
*)

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition
     Eq.Eqit
     Eq.UpToTaus.

#[global]
Instance Eq1_ITree {E} : Eq1 (itree E) := fun a => eutt eq.

#[global]
Instance Eq1Equivalence_ITree {E} : Eq1Equivalence (itree E).
Proof.
  repeat red.
  intros a.
  typeclasses eauto.
Qed.

#[global]
Instance MonadLawsE_ITree {E} : MonadLawsE (itree E).
Proof.
  constructor.
  - intros a b f x.
    by setoid_rewrite bind_ret_l.
  - intros a x.
    by setoid_rewrite bind_ret_r.
  - intros a b c x f g.
    by setoid_rewrite bind_bind.
  - intros.
    repeat red.
    intros.
    apply eqit_bind; auto.
Qed.
