From Coq Require Import
     Strings.String
     Program.Basics
     ZArith.ZArith.
From ITree Require Import Basics_Functions.
From ExtLib Require Structures.Monad.
Require Import Imp.

Typeclasses eauto := 5.

Section Syntax.

  Definition var : Set := string.
  Definition value : Set := nat. (* this should change *)

  (** ** Syntax *)

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

  (** A block is a sequence of straightline instructions followed
      by a branch. *)
  Inductive block {label : Type} : Type :=
  | bbi (_ : instr) (_ : block)
  | bbb (_ : branch label).
  Global Arguments block _ : clear implicits.

  (** Collection of blocks labeled by [A], with branches in [B]. *)
  Definition bks A B := A -> block B.

  (** Blocks with visible unlinked labels [A] and [B] and internal
      linked labels, allowing blocks to explicitly jump to each other.
      - [A]: entry points
      - [B]: exit points
      - [internal]: linked and hidden labels
   *)
  Record asm A B : Type :=
    {
      internal : Type;
      code : bks (internal + A) (internal + B)
    }.

  Global Arguments internal {A B}.
  Global Arguments code {A B}.

End Syntax.

Arguments internal {A B}.
Arguments code {A B}.

From ITree Require Import
     ITree OpenSum KTree.

Section Semantics.

  (* Denotation in terms of itrees *)

  Import ExtLib.Structures.Monad.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Import Imp.

  Inductive Memory : Type -> Type :=
  | Load (addr : value) : Memory value
  | Store (addr val : value) : Memory unit.

  Inductive Exit : Type -> Type :=
  | Done : Exit Empty_set.

  Definition done {E A} `{Exit -< E} : itree E A :=
    Vis (subeffect _ Done) (fun v => match v : Empty_set with end).

  (* Denotation of blocks *)
  Section with_effect.
    Context {E : Type -> Type}.
    Context {HasLocals : Locals -< E}.
    Context {HasMemory : Memory -< E}.
    Context {HasExit : Exit -< E}.

    Definition denote_operand (o : operand) : itree E value :=
      match o with
      | Oimm v => Ret v
      | Ovar v => lift (GetVar v)
      end.

    Definition denote_instr (i : instr) : itree E unit :=
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

      Definition denote_branch (b : branch B) : itree E B :=
        match b with
        | Bjmp l => ret l
        | Bbrz v y n =>
          val <- lift (GetVar v) ;;
          if val : value then ret y else ret n
        | Bhalt => done
        end.

      Fixpoint denote_block (b : block B) : itree E B :=
        match b with
        | bbi i b =>
          denote_instr i ;; denote_block b
        | bbb b =>
          denote_branch b
        end.

      Definition denote_b : bks A B -> ktree E A B :=
        fun bs a => denote_block (bs a).

    End with_labels.

  (* A denotation of an asm program can be viewed as a circuit/diagram
   where wires correspond to jumps/program links.

   It is therefore denoted as a [den] term *)

    (* Denotation of [asm] *)
    Definition denote_asm {A B} : asm A B -> ktree E A B :=
      fun s => loop (denote_b (code s)).

  End with_effect.
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
