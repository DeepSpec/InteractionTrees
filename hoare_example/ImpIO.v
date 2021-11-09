From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Inductive aexp :=
  | AId : string -> aexp
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
.

Inductive bexp :=
  | BEq : aexp -> aexp -> bexp
  | BLeq : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp
  | BTrue : bexp
.

Inductive com :=
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CAss : string -> aexp -> com
  | CWhile : bexp -> com -> com
  | CPrint : aexp -> com
  | CRead : string -> com
.
