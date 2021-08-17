From ITree Require Import
     Secure.SecurityImpExc.SecurityImp.


Definition secure (pc l : sensitivity) (c : stmt) : Prop := True.

Definition join (s1 s2 : sensitivity) :=
  match s1 with
  | Public => Public
  | Private => s2 end.

Variant leq_sense : sensitivity -> sensitivity -> Prop :=
  | ls_pub s : leq_sense Public s
  | ls_priv : leq_sense Private Private.

Inductive well_typed_expr (Γ : privacy_map) : sensitivity -> expr -> Prop := 
  | wte_lit n s : well_typed_expr Γ s (Lit n)
  | wte_var x : well_typed_expr Γ (Γ x) (Var x)
  | wte_plus e1 s1 e2 s2 : well_typed_expr Γ s1 e1 -> well_typed_expr Γ s2 e2 ->
                          well_typed_expr Γ (join s1 s2) (Plus e1 e2)
  | wte_min e1 s1 e2 s2 : well_typed_expr Γ s1 e1 -> well_typed_expr Γ s2 e2 ->
                          well_typed_expr Γ (join s1 s2) (Minus e1 e2)
  | wte_mult e1 s1 e2 s2 : well_typed_expr Γ s1 e1 -> well_typed_expr Γ s2 e2 ->
                          well_typed_expr Γ (join s1 s2) (Mult e1 e2)
.

Inductive well_typed_stmt (Γ : privacy_map) : sensitivity -> sensitivity -> stmt -> Prop :=
  | wts_manual pc l c : secure pc l c -> well_typed_stmt Γ pc l c
  | wts_skip pc l : well_typed_stmt Γ pc l Skip
  | wts_seq c1 c2 pc l1 l2 : well_typed_stmt Γ pc l1 c1 -> well_typed_stmt Γ pc l2 c2 ->
                             well_typed_stmt Γ pc (join l1 l2) (Seq c1 c2)
  | wts_assign x e pc l l' : well_typed_expr Γ l e -> leq_sense (join l pc) (Γ x) ->
                          well_typed_stmt Γ pc l' (Assign x e)
  | wts_if e c1 c2 pc l l1 l2 : well_typed_expr Γ l e ->
      well_typed_stmt Γ (join pc l) l1 c1 -> well_typed_stmt Γ (join pc l) l2 c2 ->
                              well_typed_stmt Γ pc (join l1 l2) (If e c1 c2)
  | wts_while e c l : well_typed_expr Γ Public e -> well_typed_stmt Γ Public l c ->
                      well_typed_stmt Γ Public l (While e c) 
  | wts_print e l l' pc : well_typed_expr Γ l' e -> leq_sense (join pc l') l ->
                       well_typed_stmt Γ pc l' (Output l e)
  | wts_raise l pc : leq_sense pc l -> well_typed_stmt Γ pc l (Raise l) 
  | wts_try c1 c2 l l' pc : well_typed_stmt Γ pc l' c1 -> well_typed_stmt Γ (join pc l') l c2 ->
                            well_typed_stmt Γ pc l (TryCatch c1 c2)
.


Lemma well_typed_stmt_correct : forall Γ pc l c, well_typed_stmt Γ pc l c -> secure pc l c.
Abort.
