From ITree Require Import ITree.
From ITreeTutorial Require Import Imp.
From Coq Require Import NArith String.

Local Open Scope string_scope.

Import ImpNotations.

Definition loopy : stmt :=
  WHILE 1 DO Skip.

Fixpoint run {A} (n : nat) (t : itree void1 A) : option A :=
  match n, observe t with
  | O, _ => None
  | S _, RetF a => Some a
  | S n, TauF t => run n t
  | S _, VisF e _ => match e with end
  end.

Definition run_ (n : N) (s : stmt) : option env :=
  option_map fst (run (N.to_nat n) (eval_imp s)).

Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlNatInt.

Parameter io : Type.
Extract Inlined Constant io => "(unit -> unit)".

Parameter seq : io -> io -> io.
Extract Constant seq => "fun a b () -> a (); b ()".

Parameter print_binding : var -> nat -> io.
Extract Constant print_binding =>
  "fun v n () ->
     let to_string l =
       let l_ = ref l in
       String.init (List.length l) (fun _ ->
         match !l_ with
         | h :: t -> l_ := t; h
         | [] -> assert false) in
     let v = to_string v in
     print_string v;
     print_string "":="";
     print_int n;
     print_string "";""".

Parameter print_newline : io.
Extract Inlined Constant print_newline => "print_newline".

Parameter nit : Type.
Extract Inlined Constant nit => "unit".

Parameter run_io : io -> nit.
Extract Constant run_io => "fun w -> w ()".

Fixpoint print_env (e : env) : io :=
  match e with
  | nil => print_newline
  | cons (v, n) e => seq (print_binding v n) (print_env e)
  end.

Definition run' (n : N) (s : stmt) : io :=
  match run_ n s with
  | None => print_newline
  | Some e => print_env e
  end.

Definition test : nit :=
  run_io (
    seq (run' 100 loopy)
        (run' 1000 (fact "X" "Y" 10)%string)
  ).

Set Warnings "-extraction-default-directory".
Extraction "imp_test.ml" test.
