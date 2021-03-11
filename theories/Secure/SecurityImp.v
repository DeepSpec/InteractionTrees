From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.


Definition var : Set := string.

Definition value : Type := nat.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr).

(** The statements are straightforward. The [While] statement is the only
 potentially diverging one. *)

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
.

Variant sensitivity : Set := Public | Private.

Definition privacy_map : Set := var -> sensitivity.


Variant SecurityImpState : Type -> Type :=
  | GetPrivVar (x : var) : SecurityImpState value
  | SetPrivVar (x : var) (v : value) : SecurityImpState unit
  | GetPubVar (x : var) : SecurityImpState value
  | SetPubVar (x : var) (v : value) : SecurityImpState unit
  | PubPrint  (v : value) : SecurityImpState unit 
  | PrivPrint (v : value) : SecurityImpState unit.



(* 
denote : stmt -> privacy_map -> itree Securityimpstate unit

interp ( ... ) :itree Securityimpstate unit ->
                S -> S -> itree (SecureIO) (S * S * unit)



itrees   ≈ eutt (eq up to tau)

monad  (StateT (itree E) ) equiv (m1 m2 : StateT (itree E) R)  forall s1 s2, state_equiv s1 s2 -> m1 s1 ≈ m2 s2




itrees   eqit_secure (with RR respecting privacy)


monad (...)    forall s1 s2, low_equiv s1 s2 -> eqit_secure ... low_equiv (m1 s1) (m2 s2)
*)
