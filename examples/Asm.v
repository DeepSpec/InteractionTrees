Require Import Coq.Strings.String.


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
Arguments branch _ : clear implicits.

Inductive block {label : Type} : Type :=
| bbi (_ : instr) (_ : block)
| bbb (_ : branch label).
Arguments block _ : clear implicits.

Record program : Type :=
{ label : Type
; blocks : label -> block label
; main : label
}.


(* now define a semantics *)

From ITree Require Import
     ITree OpenSum
     MutFix.

Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

(* the "effect" to track local variables *)
Inductive Locals : Type -> Type :=
| GetVar (x : var) : Locals value
| SetVar (x : var) (v : value) : Locals unit.

Inductive Memory : Type -> Type :=
| Load (addr : value) : Memory value
| Store (addr val : value) : Memory unit.

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
    Context {label : Type}.

    Definition denote_branch (b : branch label)
    : itree e (option label) :=
      match b with
      | Bjmp l => ret (Some l)
      | Bbrz v y n =>
        val <- lift (GetVar v) ;;
        if val : value then ret (Some y) else ret (Some n)
      | Bhalt => ret None
      end.

    Fixpoint denote_block (b : block label)
    : itree e (option label) :=
      match b with
      | bbi i b =>
        denote_instr i ;;
        denote_block b
      | bbb b =>
        denote_branch b
      end.
  End with_labels.

  Definition denote_program (p : program) : itree e unit :=
    @mut_mfix e p.(label)
       (fun _ => {| dom := unit ; codom := fun _ => unit |})
       (fun _ embed rec lbl _ =>
          next <- embed _ (denote_block (p.(blocks) lbl)) ;;
          match next with
          | None => ret tt
          | Some next => rec next tt
          end)
       p.(main) tt.
End with_effect.


(* SAZ: Everything from here down can probably be polished.

   In particular, I'm still not completely happy with how all the different parts
   fit together.  

 *)


(* Interpretation ----------------------------------------------------------- *)

From ITree Require Import
     EnvEffect.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Definition interpret_Locals (E:Type->Type) `{envE var value -< E} : eff_hom Locals E :=
  fun _ e =>
    match e with
    | GetVar x => env_lookupDefault x 0
    | SetVar x v => env_add x v
    end.
Arguments interpret_Locals {E}.

Definition interpret_Memory (E:Type -> Type) `{envE value value -< E} : eff_hom Memory E :=
  fun _ e =>
    match e with
    | Load x => env_lookupDefault x 0
    | Store x v => env_add x v
    end.
Arguments interpret_Memory {E}.

Definition env := alist var value.
Definition memory := alist value value.

Instance RelDec_string : RelDec (@eq string) := { rel_dec := fun s1 s2 => if String.string_dec s1 s2 then true else false}.
Instance RelDec_value : RelDec (@eq value) := { rel_dec := Nat.eqb }.

(*
Definition run_with_env {E} :=
  interp_state (into_state (@eval_env var value env _ E )).

Definition run_with_memory {E : Type -> Type} :=
  interp_state (into_state (@eval_env value value memory _ E)).
*)


Definition run (p:program) : itree emptyE _ :=
  let p1 := interp1 (interpret_Memory _) (denote_program (Memory +' (Locals +' emptyE)) p) in
  let p2 := interp (interpret_Locals _) p1 in
  p2.



