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


(* SAZ: Everything from here down can probably be polished *)

(* Implementations of the local enviroment and memory effects *)

From ITree Require Import
     Morphisms.

From Coq Require Import
     List.

Import ListNotations.
Open Scope list_scope.

Section interp_locals.

  Definition env := list (var * value).
  Definition init_env : env := [].
  Fixpoint lookup (l:env) (x:var) : value :=
    match l with
    | [] => 0
    | (y,v)::rest => if string_dec x y then v else lookup rest x
    end.

  Definition insert (l:env) (x:var) (v:value) := (x,v)::l.

  Definition eval_locals {E} : eff_hom_s env Locals E :=
    fun _ e l =>
      match e with
      | GetVar x => Ret (l, lookup l x)
      | SetVar x v => Ret (insert l x v, tt)
      end.

  Definition run_locals {E R} (l : env) (t : itree (Locals +' E) R)
  : itree E (env * R) :=
    interp_state (into_state eval_locals) t l.

End interp_locals.

Section interp_memory.

  Definition mem := value -> value.
  Definition init_mem : mem := fun _ => 0.
  Definition load (m:mem) (a:value) : value := m a.
  Definition store (m:mem) (a:value) (v:value) : mem :=
    fun x => if  Nat.eqb a x then v else m x.

  Definition eval_mem {E} : eff_hom_s mem Memory E :=
    fun _ e m =>
      match e with
      | Load x => Ret (m, load m x)
      | Store x v => Ret (store m x v, tt)
      end.

  Definition run_mem {E R} (m : mem) (t : itree (Memory +' E) R)
  : itree E (mem * R) :=
    interp_state (into_state eval_mem) t m.

End interp_memory.

Section toplevel.

  Definition run (p:program) : itree emptyE (mem * (env * unit)) :=
    run_mem init_mem (run_locals init_env (denote_program _ p)).

End toplevel.
