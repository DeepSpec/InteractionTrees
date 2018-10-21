Require Import ITree.ITree.
Require Import ITree.Fix.

(* Mutual fixpoints *)
Section mutual_fixpoints.
  Record ftype : Type :=
  { dom : Type
  ; codom : dom -> Type }.
  Definition ftypeD (eff : Effect) (ft : ftype) : Type :=
    forall x : ft.(dom), itree eff (ft.(codom) x).

  Context {eff : Effect}.

  Context {name : Type}.
  Variable type_of : name -> ftype.

  Definition mfix_defns : Type :=
    forall eff',
      (forall t, itree eff t -> itree eff' t) ->
      (forall n, ftypeD eff' (type_of n)) ->
      forall n, ftypeD eff' (type_of n).

  Variable defns : mfix_defns.

  Local Definition mdom := {x0 : name & dom (type_of x0) }.
  Local Definition mcodom (r : mdom) :=
    let '(existT _ tag arg) := r in
    codom (type_of tag) arg.

  Definition mut_mfix n : ftypeD eff (type_of n) :=
    fun x =>
      @mfix eff mdom mcodom
            (fun _ inj rec '(existT _ tag arg) =>
               defns _ inj
                     (fun (n0 : name) (x0 : dom (type_of n0)) =>
                        rec (existT (fun x1 : name => dom (type_of x1)) n0 x0)) tag arg)
            (existT _ n x).

End mutual_fixpoints.

Arguments mut_mfix {_ _} _ _ _.
