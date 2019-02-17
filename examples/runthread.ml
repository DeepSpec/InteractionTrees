;; open MultiThreadedPrinting


(* Taken from Xavier Leroy's Camlcoq library, which is part of CompCert under
   Gnu Public License version 2 or later.  *)
let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)





(* The driver loop ---------------------------------------------------------- *)

let rec step fuel m : unit =
  if fuel <= 0 then
    Printf.printf "Out of fuel!\n%!"
  else
    let step = step (fuel - 1) in
    match Core0.observe m with
    (* Internal steps compute as nothing *)
    | Core0.TauF x -> step x

    (* We finished the computation *)
    | Core0.RetF _ -> ()

    (* The only residual effect is Print, which carries just a string *)
    | Core0.VisF (s, k) ->
      Printf.printf "%s\n%!" (camlstring_of_coqstring s);
      step (k (Obj.magic ()))


;; step 30 scheduled_thread
