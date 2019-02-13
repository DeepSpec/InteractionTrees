Require Import Imp Asm.

Require Import Coq.Strings.String.
Local Open Scope string_scope.
Import ListNotations.

Section compile_assign.

  Fixpoint compile_expr (e: expr): list instr :=
    match e with
    | Var x => [Imov "fixme" (Ovar x)]
    | Lit n => [Imov "fixme" (Oimm n)] 
    | Plus e1 e2 =>
      compile_expr e1 ++
      compile_expr e2 ++
      [Iadd "fixme" "fixme" (Ovar "fixme")]
    end.

  Definition compile_assign (x: Imp.var) (e: expr): list instr :=
    let instrs := compile_expr e in
    instrs ++ [Imov x (Ovar "fixme")].

End compile_assign.
  
Section after.
  Context {a : Type}.
  Fixpoint after (is : list instr) (blk : block a) : block a :=
    match is with
    | nil => blk
    | i :: is => bbi i (after is blk)
    end.
End after.

Section fmap_block.
  Context {a b : Type} (f : a -> b).

  Definition fmap_branch (blk : branch a) : branch b :=
    match blk with
    | Bjmp x => Bjmp (f x)
    | Bbrz v a b => Bbrz v (f a) (f b)
    | Bhalt => Bhalt
    end.

  Fixpoint fmap_block (blk : block a) : block b :=
    match blk with
    | bbb x => bbb (fmap_branch x)
    | bbi i blk => bbi i (fmap_block blk)
    end.
End fmap_block.

(* CR essentially corresponds to an open (asm) program.
 /imports/ encodes the set of external labels to which the program can jump.
 c_main is the current entry point.
 *)
Record CR {imports : Type} : Type :=
  { c_label  : Type                                    (* Internal labels *) 
    ; c_main   : block (c_label + imports)             (* Entry point     *)
    ; c_blocks : c_label -> block (c_label + imports)   (* Other blocks    *)
  }.
Arguments CR _ : clear implicits.

Variant WhileBlocks : Set :=
| WhileTop
| WhileBottom.

(*
  Compiles a statement given a partially built continuation 'k' expressed as a block.
 *)
Fixpoint compileCR (s : stmt) {L} (k : block L) {struct s} : CR L.
refine
  match s with

  | Skip =>
    {| c_label  := Empty_set
     ; c_blocks := fun x => match x with end
     ; c_main   := fmap_block inr k |}

  | Assign x e =>
    {| c_label  := Empty_set
     ; c_blocks := fun x => match x with end
     ; c_main   := after (compile_assign x e)
                         (fmap_block inr k) |}

  | Seq l r =>
    let rc := @compileCR r L k in
    let lc := @compileCR l (sum rc.(c_label) L) rc.(c_main) in
    {| c_label  := lc.(c_label) + rc.(c_label)
     ; c_blocks := fun x =>
       match x with
       | inl x => fmap_block _ (lc.(c_blocks) x)
       | inr x => fmap_block _ (rc.(c_blocks) x)
       end
     ; c_main   :=
         fmap_block _ lc.(c_main) |}

  | If e l r =>
    let lc := @compileCR l L k in
    let rc := @compileCR r L k in
    let to_right := (fun x =>
                       match x with
                       | inl y => inl (inr (Some y))
                       | inr y => inr y
                       end)
    in
    let to_left := (fun x =>
                       match x with
                       | inl y => inl (inl (Some y))
                       | inr y => inr y
                       end) in
    {| c_label  := option lc.(c_label) + option rc.(c_label)
     ; c_blocks := fun x =>
       match x with
       | inl None =>
         fmap_block to_left lc.(c_main)
       | inl (Some x) =>
         fmap_block to_left (lc.(c_blocks) x)
       | inr None =>
         fmap_block to_right rc.(c_main)
       | inr (Some x) =>
         fmap_block to_right (rc.(c_blocks) x)
       end
     ; c_main   :=
         after (compile_assign "_jump_var" e)
               (bbb (Bbrz "_jump_var"
                          (inl (inl None))
                          (inl (inr None))))
    |}
  | While e b =>
    let bc := compileCR b unit (bbb (Bjmp tt)) in
    {| c_label := WhileBlocks
                + option bc.(c_label)
     ; c_blocks :=
       let convert x :=
           match x with
           | inl x => inl (inr (Some x))
           | inr x => inl (inl WhileTop)
           end
       in fun x =>
       match x with
       | inl WhileTop => (* before evaluating e *)
         after (compile_assign "_jump_var" e)
               (bbb (Bbrz "_jump_var"
                          (inl (inr None))
                          (inl (inl WhileBottom))))
       | inl WhileBottom => (* after the loop exits *)
         fmap_block inr k
       | inr None =>
         fmap_block convert bc.(c_main)
       | inr (Some x) =>
         fmap_block convert (bc.(c_blocks) x)
       end
     ; c_main := bbb (Bjmp (inl (inl WhileTop)))
     |}
  end.
all: clear; tauto.
Defined.

Definition compile (s : stmt) : program :=
  let cr := @compileCR s Empty_set (bbb Bhalt) in
  {| label := option cr.(c_label)
   ; main := None
   ; blocks :=
       let convert (x : _ + Empty_set) :=
           match x with
           | inl x => Some x
           | inr x => match x with end
           end in
       fun x =>
       match x with
       | None => fmap_block convert cr.(c_main)
       | Some l => fmap_block convert (cr.(c_blocks) l)
       end |}.

Section tests.

  Import ImpNotations.

  Definition ex1: stmt :=
    "x" ← 1.

Compute (compile ex1).

End tests.


(* something like this...
Lemma compileCR_correct : forall s,
    @denote_program ImpEff _ _ (@compile s) = denoteStmt s.
Proof.
*)


(*
l: x = phi(l1: a, l2: b) ; ...
l1: ... ; jmp l
l2: ... ; jmp l

l: [x]
   ....
l1: ...; jmp[a]
l2: ...; jmp[b]
*)