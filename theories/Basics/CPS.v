Section CPS.
  Definition CPS (A:Type) := forall (X:Type), (A -> X) -> X.
  Definition ret_CPS {A:Type} (a:A) := fun X (k : A -> X) => k a.
  Definition bind_CPS {A B:Type} (ma : CPS A) (k: A -> CPS B) : CPS B :=
    fun X (kb : B -> X) => ma X (fun a => k a X kb).
End CPS.
