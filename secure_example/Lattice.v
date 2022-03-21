From Coq Require Import Morphisms.

From ITree Require Import Secure.SecureEqHalt.

Class Lattice := {
  T : Type;
  join : T -> T -> T;
  meet : T -> T -> T;
  eqlat : T -> T -> Prop;
  top : T;
  bot : T;

}.

Class LatticeLaws (Lat : Lattice) := {
  eq_equiv : Equivalence eqlat;
  join_proper : Proper (eqlat ==> eqlat ==> eqlat) join;
  meet_proper : Proper (eqlat ==> eqlat ==> eqlat) meet;
  eqlat_dec : forall l1 l2, {eqlat l1 l2} + {~ eqlat l1 l2};
  join_comm : forall l1 l2, eqlat (join l1 l2) (join l2 l1);
  join_assoc : forall l1 l2 l3, eqlat (join l1 (join l2 l3)) (join (join l1 l2) l3 );
  meet_comm : forall l1 l2, eqlat (meet l1 l2) (meet l2 l1);
  meet_assoc : forall l1 l2 l3, eqlat (meet l1 (meet l2 l3) ) (meet (meet l1 l2) l3 );
  join_unit : forall l, eqlat l (join l bot);
  meet_unit : forall l, eqlat l (meet l top);
  absorb1 : forall l1 l2, eqlat (join l1 (meet l1 l2) ) l1;
  absorb2 : forall l1 l2, eqlat (meet l1 (join l1 l2) ) l1;
}.


#[global] Instance PreOrderOfLattice (Lat : Lattice)  : Preorder :=
  {|
  L := T;
  leq := fun l1 l2 => eqlat (join l1 l2) l2;
  |}.

Lemma join_idempot (Lat : Lattice) {HLat : LatticeLaws Lat} (l : L) :
  eqlat (join l l) l.
Proof.
  destruct HLat. setoid_rewrite meet_unit0 at 3. apply absorb3.
Qed.

Lemma meet_idempot (Lat : Lattice) {HLat : LatticeLaws Lat} (l : L) :
  eqlat (meet l l) l.
Proof.
  destruct HLat. setoid_rewrite join_unit0 at 3. apply absorb4.
Qed.

Lemma leq_trans_lat (Lat : Lattice) {HLat : LatticeLaws Lat}  (l1 l2 l3 : L) :
  leq l1 l2 -> leq l2 l3 -> leq l1 l3.
Proof.
  cbn. intros H12 H23. destruct HLat. setoid_rewrite <- H23.
  rewrite join_assoc0. rewrite H12. reflexivity.
Qed.

Lemma leq_join_l (Lat : Lattice) {HLat : LatticeLaws Lat}  (l1 l2 : L) :
  leq l1 (join l1 l2).
Proof.
  cbn. assert (LatticeLaws Lat). auto. destruct HLat. rewrite join_assoc0. rewrite join_idempot; auto.
  reflexivity.
Qed.

Lemma leq_join_r (Lat : Lattice) {HLat : LatticeLaws Lat}  (l1 l2 : L) :
  leq l2 (join l1 l2).
Proof.
  cbn. assert (LatticeLaws Lat). auto. destruct HLat. rewrite join_comm0. rewrite <- join_assoc0.
  rewrite join_idempot; auto. reflexivity.
Qed.

Lemma leq_refl_lat (Lat : Lattice) {HLat : LatticeLaws Lat} l :
  leq l l.
Proof.
  cbn. apply join_idempot; auto.
Qed.

Lemma leq_join_and (Lat : Lattice) {HLat : LatticeLaws Lat} (l1 l2 l3 : L) :
  leq (join l1 l2) l3 -> leq l1 l3 /\ leq l2 l3.
Proof.
  intros. split.
  eapply leq_trans_lat; eauto. apply leq_join_l; auto.
  eapply leq_trans_lat; eauto. apply leq_join_r; auto.
Qed.

Lemma leqlat_join_or (Lat : Lattice) {HLat : LatticeLaws Lat} (l1 l2 l3 : L) :
  ~ (leq (join l1 l2) l3) -> ~ leq l1 l3 \/ ~ leq l2 l3.
Proof.
  intros. cbn. destruct HLat. destruct (eqlat_dec0 (join l1 l3) l3); eauto.
  right. intro. cbn in H. rewrite <- join_assoc0 in H.
  rewrite H0 in H. contradiction.
Qed.

Lemma leq_dec (Lat : Lattice) {HLat : LatticeLaws Lat} (l1 l2 : L) :
  {leq l1 l2} + {~ leq l1 l2}.
Proof.
  cbn. destruct HLat. auto.
Qed.

Lemma leq_bot (Lat : Lattice) {HLat : LatticeLaws Lat} l :
  leq bot l.
Proof.
  cbn. destruct HLat. rewrite join_comm0. rewrite <- join_unit0.
  reflexivity.
Qed.

Lemma leq_top  (Lat : Lattice) {HLat : LatticeLaws Lat} l :
  leq l top.
Proof.
  cbn. destruct HLat. rewrite join_comm0. rewrite (meet_unit0 l).
  rewrite meet_comm0. rewrite absorb3. reflexivity.
Qed.

Lemma leq_join_lub (Lat : Lattice) {HLat : LatticeLaws Lat} l1 l2 l3 :
  leq l1 l3 -> leq l2 l3 -> leq (join l1 l2) l3.
Proof.
  cbn. intros. destruct HLat. rewrite <- join_assoc0. rewrite H0. auto.
Qed.

#[global] Instance proper_leq1 (Lat : Lattice) {HLat : LatticeLaws Lat} : Proper (eqlat ==> eqlat ==> Basics.flip Basics.impl) leq.
Proof.
  cbn. repeat intro. destruct HLat. rewrite H, H0. auto.
Qed.

#[global] Instance proper_leq2 (Lat : Lattice) {HLat : LatticeLaws Lat} : Proper (eqlat ==> eqlat ==> Basics.impl) leq.
Proof.
  cbn. repeat intro. destruct HLat. rewrite <- H. rewrite <- H0. auto.
Qed.
