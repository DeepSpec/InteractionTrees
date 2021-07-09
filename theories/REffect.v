Require Import ExtLib.Data.HList.


Set Implicit Arguments.
Set Strict Implicit.

(* recursive effects allow you to pass interaction trees to effects. *)

Section ritree.
  Context {e : list Type -> Type -> Type}.

  CoInductive ritree  {t : Type} : Type :=
  | Ret (_ : t)
  | Vis {u rs} (_ : e rs u) (_ : hlist (@ritree) rs) (_ : u -> @ritree t)
  | Tau (_ : @ritree t).
  Arguments ritree _ : clear implicits.

  Section bind.
    Context {t u : Type} (k : t -> ritree u).

    CoFixpoint bind (i : ritree t) : ritree u :=
      match i with
      | Ret x => k x
      | Vis e xs k => Vis e xs (fun x => bind (k x))
      | Tau t => Tau (bind i)
      end.
  End bind.
End ritree.
Arguments ritree _ _ : clear implicits.

Section hom.
  Variables e1 e2 : list Type -> Type -> Type.

  Definition eff_hom : Type :=
    forall rs u, e1 rs u -> hlist (ritree e2) rs -> ritree e2 u.
  (* i need this definition to ensure guardedness. *)

  Variable (hom : eff_hom).

  CoFixpoint interp u (i : ritree e1 u) : ritree e2 u :=
    match i with
    | Ret v => Ret v
    | Vis e xs k =>
      (* note(gmm): this isn't productive. i could make `eff_hom` use the
       * same structure as `mfix`, but that prevents `eff_hom`s from
       * inspecting their arguments, which they probably want to do.
       * > as usual, this is a real problem due to an `ritree` such as:
       *
       *    cofix rec := Vis (Exact (Hcons rec Hnil)) k
       *)
      bind (fun x => interp (k x)) (hom e (hlist_map interp xs))
    | Tau k => Tau (interp k)
    end.