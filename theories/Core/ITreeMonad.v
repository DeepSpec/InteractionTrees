(* SAZ: I'm not sure where in the library this should live.
    The Monad instance for itree is in ITreeDefinition but we want
    to define EqM and MonadLaws instances too.
*)

From ITree Require Import
     Basics.Basics
     Basics.Monad
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus.

Instance EqMR_ITree {E} : EqMR (itree E) := fun a b => eutt.

Instance EqmR_OK_ITree {E} : EqmR_OK (itree E).
Proof.
  split; intros; try typeclasses eauto.
  unfold eqmR, EqMR_ITree.
  repeat red.
  intros.
  split; intros.
   - rewrite <- H0. rewrite <- H1. rewrite <- H. assumption.
   - rewrite H0. rewrite H1. rewrite H. assumption.
Qed.

Instance EqMRMonad_ITree {E} : EqmRMonad (itree E).
Proof.
  split.
  - intros. apply eqit_Ret.
  - intros. eapply eqit_bind'; eassumption.
  - intros.
    do 6 red; intros.
       eapply eutt_clo_bind; eassumption.
  - intros.
    unfold bind, Monad_itree, ret. rewrite bind_ret_l.
    apply f_OK. assumption.
  - intros.
    unfold bind, Monad_itree, ret. rewrite bind_ret_r.
    assumption.
  - intros.
    unfold bind, Monad_itree. rewrite bind_bind.
    eapply eutt_clo_bind.
    + apply ma_OK.
    + intros.
      eapply eutt_clo_bind.
      apply f_OK. assumption.
      intros.  apply g_OK. assumption.
Qed.
                  
(*
Instance MonadLaws_ITree {E} : MonadLaws (itree E).
Proof.
  constructor.
  - intros a b f x.
    unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eqm, EqM_ITree. rewrite bind_ret_l. reflexivity.
  - intros a x.    unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eqm, EqM_ITree. rewrite bind_ret_r. reflexivity.
  - intros a b c x f g. unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eqm, EqM_ITree. rewrite bind_bind. reflexivity.
  - unfold Monad.bind, Monad_itree.
    intros.
    repeat red.
    intros.
    apply eqit_bind; auto.
Qed.
*)
