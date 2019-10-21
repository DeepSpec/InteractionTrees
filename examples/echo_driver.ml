(*  To Build:

    - First extract the echo.ml file from ICFPPaper.v by running the
      Extraction commands found there

    - ocamlbuild example_loop.native
*)

open Echo
let observe t = let Go ot = Lazy.force t in ot

(* OCaml handler -----(not extracted) ------------------------------------------ *)
let handle_io e k = match e with
  | Input -> k (Obj.magic (read_int ()))
  | Output x -> print_int x ; print_newline () ; k (Obj.magic ())

let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (e, k) -> handle_io e (fun x -> run (k x))

;; run echo
