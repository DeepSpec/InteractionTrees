(* Effect types *)

(* A record [E : Effect] is an effect type. *)
(* An effect is an [action] expecting some type of [reaction]. *)
Record Effect := {
    action :> Type;
    reaction : action -> Type;
  }.

Arguments reaction {_}.

(* Some external occurences of this definition:
   - coq-io (https://github.com/coq-io/io/blob/7a6e32042b704c9da367c3cf34831b022ef32761/src/Effect.v)
   - "Turing-Completeness Totally Free", Conor McBride
*)
