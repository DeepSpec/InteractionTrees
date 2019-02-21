Require Import Coq.Strings.String.
Require Import ZArith.
Typeclasses eauto := 5.

Section Syntax. 

  Definition var : Set := string.
  Definition value : Set := nat. (* this should change *)

  (* start with the syntax *)

  Variant operand : Set :=
  | Oimm (_ : value)
  | Ovar (_ : var).

  Variant instr : Set :=
  | Imov (dest : var) (src : operand)
  | Iadd (dest : var) (src : var) (o : operand)
  | Iload (dest : var) (addr : operand)
  | Istore (addr : var) (val : operand).

  Variant branch {label : Type} : Type :=
  | Bjmp (_ : label) (* jump to label *)
  | Bbrz (_ : var) (yes no : label) (* conditional jump *)
  | Bhalt
  .
  Global Arguments branch _ : clear implicits.

  Inductive block {label : Type} : Type :=
  | bbi (_ : instr) (_ : block)
  | bbb (_ : branch label).
  Global Arguments block _ : clear implicits.

  Definition fmap_branch {A B : Type} (f: A -> B): branch A -> branch B :=
    fun b =>
      match b with
      | Bjmp a => Bjmp (f a)
      | Bbrz c a a' => Bbrz c (f a) (f a')
      | Bhalt => Bhalt
      end.

  Definition fmap_block {A B: Type} (f: A -> B): block A -> block B :=
    fix fmap b :=
      match b with
      | bbb a => bbb (fmap_branch f a)
      | bbi i b => bbi i (fmap b)
      end.

  (* Collection of blocks labeled by [A], with jumps in [B]. *)
  Definition bks A B := A -> block B.

  (* ASM: linked blocks, can jump to themselves *)
  Record asm A B : Type := {
                            internal : Type;
                            code : bks (A + internal) ((A + internal) + B)
                          }.

End Syntax.

Arguments internal {A B}.
Arguments code {A B}.

From ITree Require Import
     ITree OpenSum Fix.
Require Import sum.

Section Semantics.
  (* now define a semantics *)

  (* Denotations as itrees *)
  Definition den {E: Type -> Type} A B : Type := A -> itree E B.
  (* den can represent both blocks (A -> block B) and asm (asm A B). *)

  Section den_combinators.

    Context {E: Type -> Type }.

    (* Sequential composition of den. *)
    Definition seq_den {A B C} (ab : den A B) (bc : den B C) : @den E A C :=
      fun a => ab a >>= bc.

    Infix ">=>" := seq_den (at level 40).

    Definition id_den {A} : @den E A A := fun a => Ret a.

    Definition lift_den {A B} (f : A -> B) : @den E A B := fun a => Ret (f a).

    Definition den_sum_map_r {A B C} (ab : den A B) : den (C + A) (C + B) :=
      sum_elim (lift_den inl) (ab >=> lift_den inr).

    Definition den_sum_bimap {A B C D} (ab : den A B) (cd : den C D) :
      den (A + C) (B + D) :=
      sum_elim (ab >=> lift_den inl) (cd >=> lift_den inr).

  End den_combinators.

  Require Import ExtLib.Structures.Monad.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Require Import Imp.

  Inductive Memory : Type -> Type :=
  | Load (addr : value) : Memory value
  | Store (addr val : value) : Memory unit.

  (* Denotation of blocks *)
  Section with_effect.
    Variable e : Type -> Type.
    Context {HasLocals : Locals -< e}.
    Context {HasMemory : Memory -< e}.

    Definition denote_operand (o : operand) : itree e value :=
      match o with
      | Oimm v => Ret v
      | Ovar v => lift (GetVar v)
      end.

    Definition denote_instr (i : instr) : itree e unit :=
      match i with
      | Imov d s =>
        v <- denote_operand s ;;
          lift (SetVar d v)
      | Iadd d l r =>
        lv <- lift (GetVar l) ;;
           rv <- denote_operand r ;;
           lift (SetVar d (lv + rv))
      | Iload d a =>
        addr <- denote_operand a ;;
             val <- lift (Load addr) ;;
             lift (SetVar d val)
      | Istore a v =>
        addr <- lift (GetVar a) ;;
             val <- denote_operand v ;;
             lift (Store addr val)
      end.

    Section with_labels.
      Context {A B : Type}.

      Inductive done : Set := Done : done.

      Definition denote_branch (b : @branch B)
        : itree e (B + done) :=
        match b with
        | Bjmp l => ret (inl l)
        | Bbrz v y n =>
          val <- lift (GetVar v) ;;
          if val : value then ret (inl y) else ret (inl n)
        | Bhalt => ret (inr Done) 
        end.

      Fixpoint denote_block (b : @block B)
        : itree e (B + done) :=
        match b with
        | bbi i b =>
          denote_instr i ;; denote_block b
        | bbb b =>
          denote_branch b
        end.

      Definition denote_b: bks A B -> @den e A (B + done) :=
        fun bs a => denote_block (bs a).

    End with_labels.
  End with_effect.

  (* Denotation of [asm] *)

  Definition denote_asm {e} `{Locals -< e} `{Memory -< e} {A B} : asm A B -> @den e A (B + done) :=
    fun s =>
      seq_den (lift_den inl)
              (aloop (fun a => ITree.map sum_assoc_r (denote_b e (code s) a))).

End Semantics.
(* SAZ: Everything from here down can probably be polished.

   In particular, I'm still not completely happy with how all the different parts
   fit together in run.  

 *)


(* Interpretation ----------------------------------------------------------- *)

From ITree Require Import
     Effect.Env.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

(* Both environments and memory effects can be interpreted as "map" effects. *)

Definition interpret_Locals {E : Type -> Type} `{envE var value -< E} :
  Locals ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => env_lookupDefault x 0
    | SetVar x v => env_add x v
    end.

Definition interpret_Memory {E : Type -> Type} `{envE value value -< E} :
  Memory ~> itree E :=
  fun _ e =>
    match e with
    | Load x => env_lookupDefault x 0
    | Store x v => env_add x v
    end.

(* Our Map implementation uses a simple association list *)
Definition env := alist var value.
Definition memory := alist value value.

(* Enable typeclass instances for Maps keyed by strings and values *)
Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if String.string_dec s1 s2 then true else false}.

Instance RelDec_value : RelDec (@eq value) := { rel_dec := Nat.eqb }.

(*
TODO: FIX

Definition run (p: asm unit done) : itree emptyE (env * (memory * unit)) :=
  let eval := Sum1.elim interpret_Locals interpret_Memory in
  run_env _ (run_env _ (interp eval _ (denote_asm p tt)) empty) empty.

*)

(* SAZ: Note: we should be able to prove that run produces trees that are equivalent
   to run' where run' interprets memory and locals in a different order *)



(*
Definition dummy_blk {label: Type}: block label := bbb Bhalt.
Definition arg: string := "arg".
Definition res: string := "res".

Definition local: string := "R0".

Section Odd_Even.


  (* Need to work over Z *)

  Definition even_entry {label: Type}: block label :=
    bbi (Iload local (Ovar arg))
        (bbb (Bbrz local Eend Ebody)).
  Definition even_body {label: Type}: block label :=
    bbi (Iload local (Ovar arg))
        (bbb (Bbrz local Eend Ebody)).




End Odd_Even.

Section Fact.
  Definition Fentry := 1.
  Definition Fbody := 2.
  Definition Fend := 3.

  (* Need to work over Z *)
  Definition fact_entry {label: Type} (Fend Fbody: label): block label :=
    bbi (Iload local (Ovar arg))
        (bbi (Iadd arg arg (Oimm -1)
                   (bbi (Istore res (Oimm 0))
                        (bbb (Bbrz local Fend Fbody))).

              Definition fact_body {label: Type} (Fbody: label): block label :=
                bbi (Iload local (Ovar arg))
                    (bbb (Bbrz local Fend Fbody)).



              Definition fact (n: nat): program :=
                {|
                  label:= nat;
                  blocks := fun n => match n with
                                  | 0 => bbi (Istore arg (Oimm n)) (bbb (Bjmp 1))
                                  | 1 => dummy_blk
                                  | _ => dummy_blk
                                  end;
                  main := 0
                |}.

End Fact.
*)
(*
Module AsmNotations.

  (* TODO *)
  Notation "▿ i0 ; .. ; i ; br △" :=
    (bbi i0 .. (bbi i (bbb br)) ..)
      (right associativity).

  Open Scope string_scope.
  Definition bar  := Imov "x" (Ovar "x").
  Definition foo {label: Type}: @block label :=
    ▿ bar ; bar ; bar ; Bhalt △.

End AsmNotations.

*)
