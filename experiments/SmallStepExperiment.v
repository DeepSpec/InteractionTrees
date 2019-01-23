From ITree Require Import ITree Trace.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Parameter state : Set.
Parameter done : state -> bool.
Parameter E : Type -> Type.

Parameter ss : state -> state +  {i:Type & ((E i) * (i -> state))%type}.

CoFixpoint big (s:state) : itree E state :=
  if done s then Ret s else
    match ss s with
    | inl s' => Tau (big s')
    | inr (existT _ i (e, k)) =>
      Vis e (fun x => big (k x))
    end.

(* This doesn't work if the semantics loops because there can a nontrivial trace but these derivations can't find them *)
Inductive big_trace : state -> (trace E) -> option state -> Prop :=
| bt_done : forall s, done s = true -> big_trace s [] (Some s)
| bt_tau  : forall s s' t r, ss s = inl s' -> big_trace s' t r -> big_trace s t r
| bt_vis  : forall s i e k t r,
    ss s = inr (existT _ i (e, k)) -> forall (x:i), big_trace (k x) t r -> big_trace s ((Event e x)::t) r.

Fixpoint big_trace_approx (n:nat) (s:state) (t:trace E) (os:option state) : Prop :=
  match n with
  | 0 => os = None
  | S m =>
    (done s = true /\ os = Some s /\ t = []) \/
    (exists s', ss s = inl s' /\ big_trace_approx m s' t os) \/
    (exists t' i e k, ss s = inr (existT _ i (e, k))
                 /\ forall (x:i), t = ((Event e x)::t') /\ (big_trace_approx m (k x) t' os))
end.

(* Should this be <-> ? *)
Lemma semantics_coincide : forall s n t os, big_trace_approx n s t os -> is_trace (big s) t os.
Proof.

Admitted.  
 
