(* SAZ: I'm not sure where in the library this should live.
    The Monad instance for itree is in ITreeDefinition but we want
    to define EqM and MonadLaws instances too. 
*)

From ITree Require Import
     Basics.Basics
     Basics.MonadTheory
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus.

Instance EqM_ITree {E} : EqM (itree E) := fun a => eutt eq.

Instance EqMProps_ITree {E} : EqMProps (itree E).
repeat red.
intros a.
typeclasses eauto.
Qed.

Instance MonadLaws_ITree {E} : MonadLaws (itree E).
constructor.
- intros a b f x. 
  unfold Monad.bind, Monad.ret, Monad_itree.
  unfold eqm, EqM_ITree. rewrite bind_ret. reflexivity.
- intros a x.    unfold Monad.bind, Monad.ret, Monad_itree.
  unfold eqm, EqM_ITree. rewrite bind_ret2. reflexivity.
- intros a b c x f g. unfold Monad.bind, Monad.ret, Monad_itree.
  unfold eqm, EqM_ITree. rewrite bind_bind. reflexivity.
Qed.  

Instance MonadProperOps_ITree {E} : MonadProperOps (itree E).
unfold MonadProperOps.
unfold Monad.bind, Monad_itree.
intros.
repeat red.
intros.
apply eqit_bind; auto.
Qed.

