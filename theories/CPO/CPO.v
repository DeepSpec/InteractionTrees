
Definition sequence (T : Type) : Type := nat -> T.

Definition advance {T} (seq : sequence T) : sequence T :=
  fun n => seq (S n).


Class cpo := {
  T : Type;
  leq : T -> T -> Prop;
  sup : sequence T -> T;
  }.


Definition monotone_seq `{cpo} (seq : sequence T) : Prop :=
  forall (n m : nat), n <= m -> leq (seq n) (seq m).

Definition supremum `{cpo} (seq : sequence T) (s : T) :=
  forall (upper_bound : T), (forall n, leq (seq n) upper_bound) -> leq s upper_bound.
  

Class cpo_laws (C : cpo) := {
   (* partial order laws *)
  sup_correct : forall (seq : sequence T), supremum seq (sup seq);
  }.
