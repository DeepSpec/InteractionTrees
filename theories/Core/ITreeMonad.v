(* SAZ: I'm not sure where in the library this should live.
    The Monad instance for itree is in ITreeDefinition but we want
    to define Eq1 and MonadLawsE instances too.
*)

From ITree Require Import
     Basics.Basics
     Basics.Monad
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus.

Instance Eq1_ITree {E} : Eq1 (itree E) := fun a => eutt eq.

Instance Eq1Equivalence_ITree {E} : Eq1Equivalence (itree E).
Proof.
  repeat red.
  intros a.
  typeclasses eauto.
Qed.

Instance MonadLawsE_ITree {E} : MonadLawsE (itree E).
Proof.
  constructor.
  - intros a b f x.
    unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eq1, Eq1_ITree. rewrite bind_ret_l. reflexivity.
  - intros a x.    unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eq1, Eq1_ITree. rewrite bind_ret_r. reflexivity.
  - intros a b c x f g. unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eq1, Eq1_ITree. rewrite bind_bind. reflexivity.
  - unfold Monad.bind, Monad_itree.
    intros.
    repeat red.
    intros.
    apply eqit_bind; auto.
Qed.
