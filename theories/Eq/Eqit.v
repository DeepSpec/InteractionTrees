(* 
RTODOS:
- rename and redo sections
- keep building tests until rewriting robustness is clear 
   - organize file 
   - remove add parametric morphism 
*)

(** * Strong bisimulation *)

(** Because [itree] is a coinductive type, the naive [eq] relation
    is too strong: most pairs of "morally equivalent" programs
    cannot be proved equal in the [eq] sense.
[[
    (* Not provable *)
    Goal (cofix spin := Tau spin) = Tau (cofix spin := Tau spin).
    Goal (cofix spin := Tau spin) = (cofix spin2 := Tau (Tau spin2)).
]]
    As an alternative, we define a weaker, coinductive notion of equivalence,
    [eqit], which can be intuitively thought of as a form of extensional
    equality. We shall rely extensively on setoid rewriting.
 *)

(* begin hide *)
From Stdlib Require Import
     Structures.Orders (* Hint Unfold is_true *)
     Program
     Setoid
     Morphisms
     Relations.

From Coinduction Require Export all.

(* important: Basics.Utils must come after Coinduction, as it 
re-implements several tactics. *)
From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq.Shallow.


Local Open Scope itree_scope.
(* end hide *)

(** ** Coinductive reasoning with Pous' Enhanced Coinduction library *)

(** Similarly to the way we deal with cofixpoints explained in
      [Core.ITreeDefinition], coinductive properties are defined in two steps,
      as greatest fixed points of monotone relations.

    - _monotonicity_ is with respect to relations ordered by set inclusion
      (a.k.a. implication, when viewed as predicates) 
      [(r1 <= r2) ≡ (r1 -> r2)];

    - the [coinduction] library provides a combinator [gfp] defining the
          greatest fixed point [gfp f] when [f] is indeed monotone.

    The [coinduction] library provides us with elegant machinery for
    defining a monotone function: we simply need to prove it respects 
    the [leq] relation on the implicit underlying lattice, though we never
    need to mention the actual lattice itself. 

    By thus avoiding [CoInductive] to define coinductive properties,
    [coinduction] both spares us from thinking about guardedness of proof terms,
    instead encoding a form of productivity visible in types, and also provides
    us with a powerful set of tactics for reasoning about observable behaviors.

    We have gone a step further to enrich this set of tactics with our own 
    definitions specific to ITrees. These can be found in [Basics/Utils.v] 
    and in this file in the [Tactics] section.
 *)

(** We coerce [b1] and [b2] in [eqitF] (below) from [bool] to [Prop]. This makes
it slightly easier to write and automate mechanized proofs about [eqit]: we have
hypotheses of simply [b1] rather than [b1 = true]. *)

Local Coercion is_true : bool >-> Sortclass.

Section eqit.

  (** Although the original motivation is to define an equivalence
      relation on [itree E R], we will generalize it into a
      heterogeneous relation [eqit_] between [itree E R1] and
      [itree E R2], parameterized by a relation [RR] between [R1]
      and [R2].

      Then the desired equivalence relation is obtained by setting
      [RR := eq] (with [R1 = R2]).

      The lattice on which the greatest fixed point is taken quantifies
      over types: [forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop].
      This allows chains to work uniformly across all type instantiations,
      which is essential for the bind closure principle.
   *)
  Context {E : Type -> Type}.

  (** We also need to do some gymnastics to work around the
      two-layered definition of [itree]. We first define a
      relation transformer [eqitF] as an indexed inductive type
      on [itreeF], which is then composed with [observe] to obtain
      a relation transformer on [itree] ([eqit_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [itree].
   *)

  Inductive eqitF {R1 R2 : Type} (RR : R1 -> R2 -> Prop) (b1 b2: bool) (sim : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqitF RR b1 b2 sim (RetF r1) (RetF r2)
  | EqTau m1 m2
        (REL: sim m1 m2):
      eqitF RR b1 b2 sim (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2
        (REL: forall v, sim (k1 v) (k2 v) : Prop):
      eqitF RR b1 b2 sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2
        (CHECK: b1)
        (REL: eqitF RR b1 b2 sim (observe t1) ot2):
      eqitF RR b1 b2 sim (TauF t1) ot2
  | EqTauR ot1 t2
        (CHECK: b2)
        (REL: eqitF RR b1 b2 sim ot1 (observe t2)):
      eqitF RR b1 b2 sim ot1 (TauF t2)
  .
  Hint Constructors eqitF : itree.

  Definition eqit_ b1 b2
    (sim : forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop) :
    forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop :=
    fun R1 R2 RR t1 t2 => eqitF RR b1 b2 (sim R1 R2 RR) (observe t1) (observe t2).
  Hint Unfold eqit_ : itree.
  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono b1 b2 : Proper (leq ==> leq) (eqit_ b1 b2).
  Proof.
    intros sim sim' Hsim R1 R2 RR x0 x1.
    unfold eqit_. intros IN.
    induction IN; constructor; auto.
    - apply Hsim; auto.
    - intros ?; apply Hsim; auto.
  Qed.

  (** Rocq is smart enough to figure out that [eqitF_mono] proves [eqit_] is
     monotone. *)

  Definition eqit_mon b1 b2 : mon (forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop) :=
    {| body := eqit_ b1 b2 ; Hbody := eqitF_mono b1 b2 |}.

  Definition eqit b1 b2 : forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop :=
    gfp (eqit_mon b1 b2).

  (** Strong bisimulation on itrees. If [eqit RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)

  Definition eq_itree {R1 R2} (RR : R1 -> R2 -> Prop) := eqit false false R1 R2 RR.

  Definition eutt {R1 R2} (RR : R1 -> R2 -> Prop) := eqit true true R1 R2 RR.

  Definition euttge {R1 R2} (RR : R1 -> R2 -> Prop) := eqit true false R1 R2 RR.

End eqit.
Arguments eqit_ {E} b1 b2 sim R1 R2 RR t1 t2/.
Arguments eqit {E} b1 b2 {R1 R2} RR _ _.
Arguments eqit_mon {E} b1 b2.


(** Notation of [eqit] and [eqitF]. You can write
    [≅] using [[\cong]]
    [≈] using [[\approx]]
    [≳] using [[\gtrsim]]
    in tex-mode.
    
    *)
    (* eq_itree and relative functions *)
    (* gfp *)
    Infix "≅⟨ R ⟩"   := (eq_itree R) (at level 70) : type_scope.
    Infix "≅"   := (eq_itree eq) (at level 70) : type_scope.
    (* b (gfp) *)
    Infix "{≅⟨ R ⟩}" := (eqitF R false false (eq_itree _)) (at level 70) : type_scope.
    Infix "{≅}" := (eqitF eq false false (eq_itree _)) (at level 70, only parsing) : type_scope.
    (* b (elem) *)
    Infix "{[≅⟨ R ⟩]}" := (eqitF R false false (elem _ _ _ _)) (at level 70) : type_scope.
    Infix "{[≅]}" := (eqitF eq false false (elem _ _ _ _)) (at level 70, only parsing) : type_scope.
    (* elem *)
    Infix "[≅⟨ R ⟩]" := (@elem _ _ (eqit_mon false false) _ _ _ R) (at level 70) : type_scope.
    Infix "[≅]" := (@elem _ _ (eqit_mon false false) _ _ _ eq) (at level 70) : type_scope.

    Infix "≈⟨ R ⟩" := (eutt R) (at level 70) : type_scope.
    Infix "≈" := (eutt eq) (at level 70) : type_scope.
    (* b (gfp) *)
    Infix "{≈⟨ R ⟩}" := (eqitF R true true (eutt _)) (at level 70) : type_scope.
    Infix "{≈}" := (eqitF eq true true (eutt _)) (at level 70, only parsing) : type_scope.
    (* b (elem) *)
    Infix "{[≈⟨ R ⟩]}" := (eqitF R true true (elem _ _ _ _)) (at level 70) : type_scope.
    Infix "{[≈]}" := (eqitF eq true true (elem _ _ _ _)) (at level 70, only parsing) : type_scope.
    (* elem *)
    Infix "[≈⟨ R ⟩]" := (@elem _ _ (eqit_mon true true) _ _ _ R) (at level 70) : type_scope.
    Infix "[≈]" := (@elem _ _ (eqit_mon true true) _ _ _ eq) (at level 70) : type_scope.

    Infix "≳⟨ R ⟩" := (euttge R) (at level 70) : type_scope.
    Infix "≳"   := (euttge eq) (at level 70) : type_scope.
    (* b (gfp) *)
    Infix "{≳⟨ R ⟩}" := (eqitF R true false (euttge _)) (at level 70) : type_scope.
    Infix "{≳}" := (eqitF eq true false (euttge _)) (at level 70, only parsing) : type_scope.
    (* b (elem) *)
    Infix "{[≳⟨ R ⟩]}" := (eqitF R true false (elem _ _ _ _)) (at level 70) : type_scope.
    Infix "{[≳]}" := (eqitF eq true false (elem _ _ _ _)) (at level 70, only parsing) : type_scope.
    (* elem *)
    Infix "[≳⟨ R ⟩]" := (@elem _ _ (eqit_mon true false) _ _ _ R) (at level 70) : type_scope.
    Infix "[≳]" := (@elem _ _ (eqit_mon true false) _ _ _ eq) (at level 70) : type_scope.

    (* chains *)
    Notation euttC := (Chain (eqit_mon true true)).
    Notation euttgeC := (Chain (eqit_mon true false)).
    Notation eq_itreeC := (Chain (eqit_mon false false)).
    
    (* makes [observe] a bit nicer to look at *)
    Notation "⊙ x" := (observe x) (only printing, at level 10).
    

    (* begin hide *)
    #[global] Hint Constructors eqitF : itree.
    #[global] Hint Unfold eqit_ : itree.
    #[global] Hint Unfold eqit_mon : itree.
    #[global] Hint Unfold eqit : itree.
    #[global] Hint Unfold eq_itree : itree.
    #[global] Hint Unfold eutt : itree.
    #[global] Hint Unfold euttge : itree.
    (* Alternative notation to the ` with a \dot. Would be good to pick an ascii
    one instead maybe? *)
    #[local] Notation "̇ R" := (elem R) (at level 2, R at level 1, format "̇ R").
    (* end hide *)
    
(** Tactics *)

(* Ongoing hesitation: should the [icoinduction] tactic expose a [eqit_mon R b b']
goal, or directly a [eqitF R b b'] one?
Experimenting with the latter at the moment. *)

(* We first enhance the coinduction tactic to recognize goals that 
   do not have a syntactic match with [gfp _] *)

#[local] Ltac iunfold_all :=
  unfold euttge, eq_itree, eutt, eqit in *.

#[local] Ltac iunfold_in h :=
  unfold euttge, eq_itree, eutt, eqit in h.

#[local] Ltac iunfold :=
  unfold euttge, eq_itree, eutt, eqit.


(* Trick for unfolding only the relevant instances *)
#[local] Ltac iunfold_coind :=
    first
      [intros ?; iunfold_coind; revert_last |
       unfold euttge,eutt,eq_itree,eqit].
  
Ltac refold :=
  repeat match goal with
  | |- context[gfp (@eqit_mon ?E ?b1 ?b2)] =>
      fold (@eqit E b1 b2);
      try fold (@eq_itree E _ _);
      try fold (@euttge E _ _);
      try fold (@eutt E _ _)
  end.


Ltac refold_in h :=
  match type of h with
  | context[gfp (@eqit_mon ?E ?b1 ?b2)] =>
      fold (@eqit E b1 b2) in h;
      try fold (@eq_itree E _ _) in h;
      try fold (@euttge E _ _) in h;
      try fold (@eutt E _ _) in h
  end.

Ltac to_mon_core :=
match goal with
| |- context[@eqitF ?E ?R1 ?R2 ?RR ?b1 ?b2 (?f ?R1 ?R2 ?RR) (observe ?t1) (observe ?t2)] =>
      change (eqitF RR b1 b2 (f R1 R2 RR) (observe t1) (observe t2))
      with (eqit_mon b1 b2 f R1 R2 RR t1 t2)
| |- context[@eqitF ?E ?R1 ?R2 ?RR ?b1 ?b2 (?f ?R1 ?R2 ?RR) (?con1 ?a1) (?con2 ?a2)] =>
      change (eqitF RR b1 b2 (f R1 R2 RR) (con1 a1) (con2 a2))
      with (eqit_mon b1 b2 f R1 R2 RR (go (con1 a1)) (go (con2 a2)))
end.

Ltac under_forall' tac := 
let dummy := fresh "dummy" in   
assert (dummy : True) by constructor; 
          intros; 
          tac; 
          revert_until dummy; 
          clear dummy. 

Ltac to_mon := 
let dummy := fresh "dummy" in   
assert (dummy : True) by constructor; 
          intros; 
          to_mon_core; 
          revert_until dummy; 
          clear dummy. 

Ltac to_mon_in h :=
match type of h with
| context[@eqitF ?E ?R1 ?R2 ?RR ?b1 ?b2 (?f ?R1 ?R2 ?RR) (observe ?t1) (observe ?t2)] =>
      change (eqitF RR b1 b2 (f R1 R2 RR) (observe t1) (observe t2))
      with (eqit_mon b1 b2 f R1 R2 RR t1 t2) in h
| context[@eqitF ?E ?R1 ?R2 ?RR ?b1 ?b2 (?f ?R1 ?R2 ?RR) (?con1 ?a1) (?con2 ?a2)] =>
      change (eqitF RR b1 b2 (f R1 R2 RR) (con1 a1) (con2 a2))
      with (eqit_mon b1 b2 f R1 R2 RR (go (con1 a1)) (go (con2 a2))) in h
end.

#[local] Ltac icbn := cbn[eqit_mon body eqit_].
#[local] Ltac icbn_in H := cbn[eqit_mon body eqit_] in H.

#[local] Tactic Notation "icbn" "in" ident(h) := icbn_in h. 
#[local] Tactic Notation "icbn" "in" "*" := cbn[eqit_mon body eqit_] in *. 


Tactic Notation "refold" "in" ident(h) := refold_in h.
Tactic Notation "to_mon" "in" ident(h) := to_mon_in h.
Tactic Notation "iunfold" "in" ident(h) := iunfold_in h.
Tactic Notation "iunfold" "in" "*" := iunfold_all.
Tactic Notation "step" := iunfold; step; icbn; try refold.
Tactic Notation "unstep" := iunfold; try to_mon; unstep; try refold. 
Tactic Notation "step" "in" ident(h) :=
  iunfold in h;
  step in h;
  cbn[eqit_mon body] in h;
  unfold eqit_ in h;
  try refold_in h.
Tactic Notation "unstep" "in" ident(h) := 
iunfold_in h; try to_mon_in h; unstep_in h; try refold_in h. 

Tactic Notation "icoinduction" simple_intropattern(R) simple_intropattern(H) :=
iunfold_coind; coinduction R H; icbn.  

Tactic Notation "bcoinduction" simple_intropattern(R) simple_intropattern(H) :=
icoinduction R H; to_mon.

Tactic Notation "bcoinduction" :=
let c := fresh "c" in 
let cih := fresh "cih" in 
bcoinduction c cih. 

Ltac bcbn := cbn; to_mon. 

(* The [icbn] tactic: unfolding the ITree definition *)

(* Since [itrees] are defined with nesting, un-nesting is often needed 
  during a proof to get Rocq to recognize certain terms as valid under
  certain tactics. Example: [dependent induction] does not work for 
  [eqit_mon], but it does for [eqitF]. Unfolding icbn to [eqitF]
  [eqit_mon], but it does for [eqitF]. Unfolding icbn to [eqitF]
  in both hypotheses and the goal is so common that the library uses
  an internal tactic for doing so all at once. *)


(* [solve_eqitF] tries to solve a goal with a variant of [eqitF] by
   simplifiying, rewriting, and trying to apply assumptions. *)

Ltac solve_eqitF := 
  (* reduce to 'observe' form by stripping constructors and unfolding *)
  iunfold; icbn in *; try econstructor; 
  (* replace 'observe' with actual constructor values *)
  simpobs; 
  (* finish off *)
  try econstructor; intros; eauto with itree. 

(* [taul] and [taur] peel off a tau from either side when the CHECK flag for
   that side is set. Their primary purpose is to make proofs more readable. 
   [taus] is simply the [EqTau] constructor, and serves the same purpose. 
   *)

Ltac taul := apply EqTauL; [auto|].
Ltac taur := apply EqTauR; [auto|]. 
Ltac taus := apply EqTau. 


Module step_notation_tests. 
  #[local] Parameter E : Type -> Type.
  #[local] Parameter R1 R2 : Type.
  #[local] Parameter RR : R1 -> R2 -> Prop.
  #[local] Parameter t u : itree E R1.
  #[local] Parameter v w : itree E R2.
  #[local] Parameter eqc : (Chain (@eqit_mon E false false)).
  #[local] Parameter (EQ1 : t ≅ u).
  #[local] Parameter (EQUIV1 : t ≈ u).
  #[local] Parameter (EQ2 : v ≅ w).
  #[local] Parameter (EQUIV2 : v ≈ w).
  #[local] Parameter (GT : v ≳ w).
  #[local] Parameter (GT2 : w ≳ v).

  (* RTODO: step better error message *)
Goal eutt RR u v.
    (* already in the gfp <-> b gfp loop *)
    step. unstep.
    step.
    Fail step. 
    unstep. 
    Fail unstep.  
    assert (eqitF eq false false (elem eqc _ _ eq) (observe v) (observe w)).
    step.
    (* now in the loop *)
    step. unstep. Fail unstep. step. Fail step. now (unstep; apply EQ2). 
    assert ((elem eqc _ _ eq) v w).
    step. step. 
    (* now in the loop *)
    step. unstep. Fail unstep. step. Fail step. now (unstep; apply EQ2). 
Abort. 

End step_notation_tests. 

Lemma eqitF_inv_VisF_r {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 sim}
  t1 X2 (e2 : E X2) (k2 : X2 -> _) :
  eqitF RR b1 b2 sim t1 (VisF e2 k2) ->
  (exists k1, t1 = VisF e2 k1 /\ forall v, sim (k1 v) (k2 v)) \/
    (b1 /\ exists t1', t1 = TauF t1' /\ eqitF RR b1 b2 sim (observe t1') (VisF e2 k2)).
Proof.
  refine (fun H =>
            match H in eqitF _ _ _ _ _ t2 return
                  match t2 return Prop with
                  | VisF e2 k2 => _
                  | _ => True
                  end
            with
            | EqVis _ _ _ _ _ _ _ _ => _
            | _ => _
            end); try exact I.
  - left; eauto.
  - destruct i0; eauto.
Qed.

Lemma eqitF_inv_VisF_l {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 sim}
    t2 X2 (e1 : E X2) (k1 : X2 -> _)
  : eqitF RR b1 b2 sim (VisF e1 k1) t2 ->
    (exists k2, t2 = VisF e1 k2 /\ forall v, sim (k1 v) (k2 v)) \/
    (b2 /\ exists t2', t2 = TauF t2' /\ eqitF RR b1 b2 sim (VisF e1 k1)(observe t2')).
Proof.
  refine (fun H =>
    match H in eqitF _ _ _ _ t1 _ return
      match t1 return Prop with
      | VisF e1 k1 => _
      | _ => True
      end
    with
    | EqVis _ _ _ _ _ _ _ _ => _
    | _ => _
    end); try exact I.
  - left; eauto.
  - destruct i; eauto.
Qed.

Lemma eqitF_inv_VisF_weak {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 sim}
    X1 (e1 : E X1) (k1 : X1 -> _) X2 (e2 : E X2) (k2 : X2 -> _)
  : eqitF RR b1 b2 sim (VisF e1 k1) (VisF e2 k2) ->
    exists p : X1 = X2, eqeq E p e1 e2 /\ pweqeq sim p k1 k2.
Proof.
  refine (fun H =>
    match H in eqitF _ _ _ _ t1 t2 return
      match t1, t2 return Prop with
      | VisF e1 k1, VisF e2 k2 => _
      | _, _ => True
      end with
    | EqVis _ _ _ _ _ _ _ _ => _
    | _ => _
    end); try exact I.
  - exists eq_refl; cbn; eauto.
  - destruct i; exact I.
Qed.

Lemma eqitF_inv_VisF {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 sim}
    X (e : E X) (k1 : X -> _) (k2 : X -> _)
  : eqitF RR b1 b2 sim (VisF e k1) (VisF e k2) ->
    forall x, sim (k1 x) (k2 x).
Proof.
  intros H. dependent destruction H. assumption.
Qed.

Lemma eqitF_VisF_gen {E R1 R2} {RR : R1 -> R2 -> Prop} {b1 b2 sim}
    {X1 X2} (p : X1 = X2) (e1 : E X1) (k1 : X1 -> _) (e2 : E X2) (k2 : X2 -> _)
  : eqeq E p e1 e2 -> pweqeq sim p k1 k2 ->
    eqitF RR b1 b2 sim (VisF e1 k1) (VisF e2 k2).
Proof.
  destruct p; intros <-; cbn; constructor; auto.
Qed.

Lemma eqitF_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2 r:
  flip (eqitF (flip RR) b2 b1 (flip r)) <= @eqitF E R1 R2 RR b1 b2 r.
Proof.
  repeat intro; induction H; eauto with itree.
Qed.

#[global] Instance eqitF_Proper_R {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq_rel ==> eq_rel)
    (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; unfold subrelationH; intros. 
  all: 
  induction H0; auto with itree; econstructor; intros; 
  try (now apply H); now apply H2. 
Qed.

#[global] Instance eqitF_Proper_R2 {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
         (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; intros.
  all: induction H0; auto with itree;
       econstructor; now apply H.
Qed.

#[global] Instance eqit_Proper_R {E : Type -> Type} {R1 R2:Type} b1 b2
  : Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eqit E b1 b2 R1 R2).
Proof with auto with itree.
  repeat red.
  repeat intro. subst. 
  split.
  - revert_until H. icoinduction R CIH. intros.
    step in H0.
    hinduction H0 before CIH...
    econstructor; now apply H. 
  - revert_until H. icoinduction R CIH. intros.  
    step in H0.
    hinduction H0 before CIH... 
    econstructor; now apply H. 
Qed. 

#[global] Instance eq_itree_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eq_itree E R1 R2).
Proof.
  now repeat intro; apply eqit_Proper_R.
Qed.

#[global] Instance euttge_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@euttge E R1 R2).
Proof.
  now repeat intro; apply eqit_Proper_R.
Qed.

#[global] Instance eutt_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eutt E R1 R2).
Proof.
  now repeat intro; apply eqit_Proper_R.
Qed.


(* Note and TODO: if we push [forall R1 R2 RR] below the [gfp],
   this and monotonicity will hold on chains.
   Meaning, assuming it can typecheck after the generalization,
   the following are conjectures:
   [forall (c : Chain (@eqit_mon E)),
   `c (flip RR) b2 b1 <= `c RR b1 b2]
   Though this would require to push b1 and b2 below the gfp
   as well, which sounds highly silly.
   Alternatively, it would be restricted to b1 = b2.
 *)

Lemma eqit_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2:
  forall (u : itree E R1) (v : itree E R2),
    eqit b2 b1 (flip RR) v u -> eqit b1 b2 RR u v.
Proof.
  (* do coinduction. *)
  icoinduction c CIH. intros u v euv. 
  (* reduce the hypothesis and conclusion to the right form. *)
  step in euv.
  (* do induction and conclude trivially with constructors. *)
  induction euv; eauto with itree.
Qed.

Lemma eutt_flip : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop)
                         (ta : itree E A) (tb : itree E B),
    eutt R ta tb -> eutt (flip R) tb ta.
Proof.
  intros. now apply eqit_flip.  
Qed.

#[global] Hint Unfold flip : itree.

(** [eqit] itself is monotone *)

Lemma eqit_mono {E R1 R2} RR RR' (b1 b2 b1' b2': bool)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2')
      (LERR: RR <= RR'):
  @eqit E b1 b2 R1 R2 RR <= eqit b1' b2' RR'.
Proof.
  repeat intro. 
  revert a a0 H. 
  icoinduction c CIH; intros.  
  step in H. induction H; eauto with itree.
  econstructor. now apply LERR.  
Qed.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eqit_gen.

(** *** Properties of relation transformers. *)

  Context {E : Type -> Type} {R: Type} (RR : R -> R -> Prop).

  (** *** Order properties of the respective chains *)

  (** Universal properties of the chains of the respective relations:
    - all three are reflexive
    - the chains for [eq_itree] and [eutt] are symmetric
    - the chain for [eq_itree] is additionally transitive
Properties of the chains specialize to the relations: the gfp is an element of the chain.
   *)
  
  #[global] Instance Reflexive_eqitF b1 b2 (sim : itree E R -> itree E R -> Prop)
    : Reflexive RR -> Reflexive sim -> Reflexive (eqitF RR b1 b2 sim).
  Proof.
    red. destruct x; constructor; eauto with itree.
  Qed.

  (* We of course exclude the asymmetric case *)
  #[global] Instance Symmetric_eqitF b (sim : itree E R -> itree E R -> Prop)
    : Symmetric RR -> Symmetric sim -> Symmetric (eqitF RR b b sim).
  Proof.
    red. induction 3; constructor; subst; eauto.
  Qed.

  (* Note the strong bisimulation assumption *)
  #[global] Instance Transitive_eqitF (sim : itree E R -> itree E R -> Prop)
    : Transitive RR -> Transitive sim -> Transitive (eqitF RR false false sim).
  Proof.
    intros ?? t u v EQ1 EQ2.
    inv EQ1; try now (inv EQ2; try easy; eauto with itree).
    apply eqitF_inv_VisF_l in EQ2 as [(? & -> & ?) | [abs _]]; [| easy].
    constructor; eauto.
  Qed. 

  #[global] Instance Reflexive_eqit_ b1 b2
    (sim : forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop)
    : Reflexive RR -> Reflexive (sim R R RR) -> Reflexive (eqit_ b1 b2 sim R R RR).
  Proof. repeat red. intros. reflexivity. Qed.

  #[global] Instance Symmetric_eqit_ b
    (sim : forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop)
    : Symmetric RR -> Symmetric (sim R R RR) -> Symmetric (eqit_ b b sim R R RR).
  Proof. repeat red; symmetry; auto. Qed.

  #[global] Instance Transitive_eqit_
    (sim : forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop)
    : Transitive RR -> Transitive (sim R R RR) -> Transitive (eqit_ false false sim R R RR).
  Proof. repeat red; etransitivity; eauto. Qed.

  (* Prove Reflexive/Symmetric for eqit first (by coinduction),
     then derive for elem via gfp_chain. *)

  #[global] Instance Reflexive_eqit b1 b2 : Reflexive RR -> Reflexive (@eqit E b1 b2 _ _ RR).
  Proof.
    red; intros.
    revert x. icoinduction c CIH. intro. 
    now repeat apply Reflexive_eqit_.
  Qed.

  #[global] Instance Symmetric_eqit b : Symmetric RR -> Symmetric (@eqit E b b _ _ RR).
  Proof.
    intros Hsym x y Hxy.
    apply eqit_flip.
    eapply eqit_mono; [auto | auto | | exact Hxy]; auto. 
  Qed.

  #[global] Instance Reflexive_elem (b1 b2: bool) (HR : Reflexive RR)
    {c: Chain (@eqit_mon E b1 b2)}: Reflexive (elem c R R RR).
  Proof.
    red; intro x.
    apply (gfp_chain c).
    reflexivity.
  Qed.

  Lemma inf_closed_Symmetric_at :
    inf_closed (X := forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop)
      (fun x => Symmetric (x R R RR)).
  Proof.
    intros T HT x y Hxy.
    intros z Hz. apply HT; auto.
  Qed.

  #[global] Instance Symmetric_elem (b: bool) (HS : Symmetric RR)
    {c: Chain (@eqit_mon E b b)}: Symmetric (elem c R R RR).
  Proof.
    revert c. apply (tower inf_closed_Symmetric_at).
    intros c Hsym. apply Symmetric_eqit_; auto.
  Qed.

End eqit_gen.


Section eqit_inv.

  Context {E : Type -> Type} {R1 R2} {RR : R1 -> R2 -> Prop} {b1 b2 : bool}.
  Context {sim : itree E R1 -> itree E R2 -> Prop}.

  Notation eqit__ t1_ t2_ :=
    match _observe t1_, _observe t2_ with
    | RetF r1, RetF r2 => RR r1 r2
    | VisF e1 k1, VisF e2 k2 =>
        exists p, eqeq E p e1 e2 /\ pweqeq (eqit b1 b2 RR) p k1 k2
    | RetF _, VisF _ _ | VisF _ _, RetF _ => False
    | TauF t1, TauF t2 => eqit b1 b2 RR t1 t2
    | TauF t1, _ =>
        if b1 then eqit b1 b2 RR t1 t2_
        else False
    | _, TauF t2 =>
        if b2 then eqit b1 b2 RR t1_ t2
        else False
    end.

  Lemma eqit_inv_Tau_l t1 t2 :
    @eqit E b1 true R1 R2 RR (Tau t1) t2 -> eqit b1 true RR t1 t2.
  Proof.
    intros * H.
    step in H.
    step.   
    remember (observe (Tau t1)).
    induction H; inv Heqi.  
    - step in REL. now taur. 
    - assumption. 
    - taur. now apply IHeqitF. 
  Qed. 

  Lemma eqit_inv_Tau_r t1 t2 :
    @eqit E true b2 R1 R2 RR t1 (Tau t2) -> eqit true b2 RR t1 t2.
  Proof.
    intros * H.
    step in H.
    step.   
    remember (observe (Tau t2)).
    induction H; inv Heqi.  
    - step in REL. now taul. 
    - taul. now apply IHeqitF. 
    - assumption. 
  Qed. 

  Lemma eqitF_inv_Tau t1 t2 :
    @eqitF E R1 R2 RR b1 b2 (gfp (eqit_mon b1 b2) R1 R2 RR) (TauF t1) (TauF t2)
    -> eqitF RR b1 b2 (gfp (eqit_mon b1 b2) R1 R2 RR) (observe t1) (observe t2).
  Proof.
    intros.
    remember (TauF t1) as ot1. 
    remember (TauF t2) as ot2. 
    revert t1 t2 Heqot1 Heqot2.
    induction H; intros t1' t2' Heqot1 Heqot2; try easy; subst.
    - inv Heqot1; inv Heqot2. now unstep.  
    - inv H; inv Heqot1; simpobs. 
      + taul. now step in REL.  
      + taul. now apply IHeqitF.  
      + assumption. 
    - inv H; inv Heqot2; simpobs. 
      + taur. now step in REL. 
      + assumption. 
      + taur. now apply IHeqitF. 
  Qed. 

  Lemma eqit_inv_Tau t1 t2 :
    @eqit E b1 b2 R1 R2 RR (Tau t1) (Tau t2) -> eqit b1 b2 RR t1 t2.
  Proof.
    intros.
    step in H; step.
    now apply eqitF_inv_Tau. 
  Qed. 

  Lemma eqit_inv t1 t2 : eqit b1 b2 RR t1 t2 -> eqit__ t1 t2.
  Proof.
    intros H; step in H.
    genobs t1 ot1; genobs t2 ot2; revert t1 t2 Heqot1 Heqot2; unfold observe, _observe.
    destruct H; intros * E1 E2; rewrite <- E1, <- E2; cbn; auto.
    - exists eq_refl; cbn; eauto.
    - rewrite CHECK in *. destruct ot2.
      1,3: step; unfold observe, _observe; rewrite <- E2; assumption.
      1: apply eqit_inv_Tau_r; step; unfold observe, _observe; assumption.
    - rewrite CHECK in *. destruct ot1.
      1,3: step; unfold observe, _observe; rewrite <- E1; assumption.
      1: apply eqit_inv_Tau_l; step; unfold observe, _observe; assumption.
  Qed.

Lemma eqit_inv_Tau_var (m1 : itree E R1) z :
  forall (om1 : itree' E R1),
    observe m1 = om1 ->
    eqitF RR true false sim om1 z ->
    @eqitF _ R1 R2 RR true false sim (TauF m1) z.
Proof.
  intros om1 Heq H2.
  (* Now om2 is a variable — we can use plain induction *)
  induction H2; taul; simpobs; eauto with itree. 
Qed. 

End eqit_inv.

Ltac genret r or := remember (RetF r) as or.
Ltac gentau t ot := remember (TauF t) as ot.
Ltac genvis e k ot := remember (VisF e k) as ot.

Lemma euttge_tau_r_inv [E R1 R2 RR] (t : itree E R1) (u : itree E R2) :
  euttge RR t (Tau u) -> exists t', observe t = TauF t'.
Proof.
  intros EQ; step in EQ.
  desobs t ot; eauto; inv EQ; easy.
Qed.

Lemma euttge_tau_inv {E R1 R2 RR} (t : itree E R1) (u : itree E R2):
  euttge RR t u  ->
  forall t' u',
  observe t = TauF t' ->
  observe u = TauF u' ->
  euttge RR t' u'.
Proof.
  intros EQ.
  step in EQ; cbn in EQ.
  genobs t ot; genobs u ou.
  revert t u Heqot Heqou.
  induction EQ; intros; try easy.
  - inv H; inv H0; try easy.
  - inv H; simpobs.
    edestruct euttge_tau_r_inv; [step; eauto |].
    step.
    simpobs.
    taul.
    unstep.
    eapply IHEQ; eauto.
Qed.


Ltac inf_closed_forall_auto := 
repeat match goal with 

| [|- inf_closed (fun _ => forall _, _)] => 
  apply inf_closed_all; intro
  end. 

Ltac inf_closed_impl_auto := 
repeat match goal with 
| [|- inf_closed (fun _ => _ -> _)] => 
  apply inf_closed_impl; repeat intro; 
  match goal with [H : _ <= _ |- _] => apply H; auto end
  end. 



Ltac inf_closed_auto := 
repeat match goal with 
| [|- inf_closed _] => (inf_closed_forall_auto || inf_closed_impl_auto)
end. 

Ltac tower_induction := apply tower; [inf_closed_auto|].
Tactic Notation "tower" "induction" := tower_induction. 

(* for meeting *)
 (* learned a lot from this. 
    1 interesting difference is your induction on eqit_mon ... ̇c,
     rather than on {≳}.
    another is the strong IH. 
    a third is use of certain interesting automation, which I'd like to learn
    finally, edestructing a lemma. seems quite cool. 
    
    we will talk next steps at our meeting: 
    1. where to go in this file: notation, tactic naming, etc. 
      imo we should name things exactly as they will be in your 
      coinduction library PR, so that they are easy to fix.
    2. onwards: we want this proof but with euttgeC, no? 
       finally, will we use uptotaus, or just move on to the next
       part in ktrees? 
    3. finally, thanks! 
     *)
#[global] Instance euttge_proper_euttC {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : euttC):
  Proper (euttge (E := E) eq ==> euttge eq ==> flip impl) (elem c _ _ RR).
Proof with eauto with itree.
  unfold Proper, respectful, flip, impl.
  tower induction.
  clear c; intros c IH x x' EQx y y' EQy; step in EQx; step in EQy.
    icbn; intros EQ.
    genobs x' ox'; genobs y' oy'.
    (* [hinduction] is not sufficient here, because [move] is unable to pass
         through [ox] to reach [x] *)
    revert x x' y y' Heqox' Heqoy' EQx EQy.
    induction EQ; intros.
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genret r1 or1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros; subst; inv Heqor1. clear x Heqox.
        genobs y oy; genret r2 or2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        subst; intros [=<-] ??...
        now intros; taur; eapply IHEQy.
      * intros; subst; taul; eapply IHEQx...
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      gentau m1 om1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros [=<-] ? ??.
        clear x Heqox.
        genobs y oy; gentau m2 om2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        intros [=<-] ??...
        intros.
        taur.
        now eapply IHEQy.
      * intros; subst; taul; eapply IHEQx...
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genvis e k1 ot1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros.
        apply eq_inv_VisF_weak in Heqot1 as (-> & ? & ?); cbn in *; subst.
        clear x Heqox.
        genobs y oy; genvis e k2 ot2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        intros; apply eq_inv_VisF_weak in Heqot2 as (-> & ? & ?); cbn in *; subst; eauto with itree.
        intros.
        taur.
        now eapply IHEQy.
      * intros; subst; taul; eapply IHEQx...
    + edestruct euttge_tau_r_inv; [step; eauto |].
      simpobs.
      taul.
      eapply IHEQ; eauto.
      assert (euttge eq (Tau x0) (Tau t1)) by (now step).
      unstep; eapply euttge_tau_inv; eauto.
    + edestruct euttge_tau_r_inv; [step; eauto |].
      simpobs.
      taur.
      eapply IHEQ; eauto.
      assert (euttge eq (Tau x0) (Tau t2)) by (now step).
      unstep; eapply euttge_tau_inv; eauto.
Qed. 



(* here chain_b lifts b to elements of the chain... *)
#[global] Instance euttge_proper_euttC_mon {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : euttC):
  Proper ((euttge (E := E) eq) ==> (euttge eq) ==> flip impl)  (eqit_mon true true (elem c) R1 R2 RR).
Proof.
  eapply euttge_proper_euttC with (c := chain_b c); eauto.  
Qed. 

(* ... and chain_gfp lifts the gfp. *)
#[global] Instance euttge_proper_eutt  {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : Chain (@eqit_mon E true true)):
  Proper ((euttge (E := E) eq) ==> (euttge eq) ==> flip impl)  (eutt RR). 
Proof.
  eapply euttge_proper_euttC with (c := (chain_gfp (eqit_mon true true))); eauto.  
Qed. 

Lemma eq_subH_euttge {E R1 R2} (RR : R1 -> R2 -> Prop):
  subrelationH (@eq_itree E _ _ RR) (euttge RR).
Proof. now apply eqit_mono. Qed.

#[global] Instance eq_sub_euttge {E R} (RR : R -> R -> Prop):
  subrelation (@eq_itree E _ _ RR) (euttge RR).
Proof. now apply eqit_mono. Qed.

Lemma euttge_subH_eutt {E R1 R2} (RR : R1 -> R2 -> Prop):
  subrelationH (@euttge E _ _ RR) (eutt RR).
Proof. now eapply eqit_mono. Qed.

#[global] Instance euttge_sub_eutt {E R} (RR : R -> R -> Prop):
  subrelation (@euttge E _ _ RR) (eutt RR).
Proof. now apply eqit_mono. Qed.

Lemma eq_subH_eutt {E R1 R2} (RR : R1 -> R2 -> Prop):
  subrelationH (@eq_itree E _ _ RR) (eutt RR).
Proof. now apply eqit_mono. Qed.

#[global] Instance eq_sub_eutt {E R} (RR : R -> R -> Prop):
  subrelation (@eq_itree E _ _ RR) (eutt RR).
Proof. now apply eqit_mono. Qed.

#[global] Instance eq_proper_euttC {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : euttC):
  Proper (eq_itree (E := E) eq ==> eq_itree eq ==> iff) (elem c _ _ RR).
Proof. 
  split; intro. 
  1: symmetry in H; symmetry in H0. 
  all: 
  apply eq_sub_euttge with (RR := eq) in H;
  apply eq_sub_euttge with (RR := eq) in H0;
  eapply euttge_proper_euttC; eauto.
Qed.

#[global] Instance eq_proper_eqit {E R1 R2 b1 b2}
  (RR : R1 -> R2 -> Prop):
  Proper (eq_itree (E := E) eq ==> eq_itree eq ==> iff) (eqit b1 b2 RR). 
Proof with eauto with itree. 
  split; intros; 
  revert_until RR; 
  icoinduction c cih; intros; 
  step in H0; step in H1; step in H; icbn in *.
  all:
  hinduction H1 before RR; intros.
   (* ret and taus cases *)
  1-2, 6-7: inv H; inv H0; simpobs; try easy; eauto with itree. 
  (* vis *)
  1,4:
  genvis e k1 ok1; inv H; simpobs; try easy; 
  genvis e k2 ok2; inv H0; simpobs; try easy;
  do 2 inv_Vis; constructor; intros;
  specialize (REL1 v);
  specialize (REL0 v);
  eapply cih; eauto. 
  (* inductive steps *)
  1,3: 
  inv H; simpobs; try easy; taul; eapply IHeqitF; eauto; now step in REL.
  1-2: 
  inv H0; simpobs; try easy; taur; eapply IHeqitF; eauto; now step in REL.
Qed.

(* [euttge_proper_euttgeC] with [euttge eq] on BOTH arguments is FALSE.
   Counterexample: c = chain_gfp (eqit_mon eq true false) so ̇c = euttge eq.
   Take x = x' = Ret tt, y = Tau (Ret tt), y' = Ret tt.
   Then euttge eq (Ret tt) (Ret tt) ✓, euttge eq (Tau (Ret tt)) (Ret tt) ✓ (EqTauL),
   and ̇c (Ret tt) (Ret tt) = euttge eq (Ret tt) (Ret tt) ✓,
   but ̇c (Ret tt) (Tau (Ret tt)) = euttge eq (Ret tt) (Tau (Ret tt)) is FALSE
   because b2=false means the right side cannot skip taus. *)
Lemma not_euttge_proper_euttgeC :
~ (forall E R1 R2 (RR : R1 -> R2 -> Prop) (c : euttgeC),
  Proper (euttge (E := E) eq ==> euttge eq ==> flip impl) (elem c _ _ RR)).
  unfold Proper, respectful, flip, impl. 
  intro. 
assert (Hfalse : euttge (E := fun _ => Empty_set) (R1 := unit) (R2 := unit) eq
                    (Ret tt) (Tau (Ret tt))).
  { eapply H with (x := Ret tt) (y := Ret tt).
  (* ^ this works because the canonical chain structure uses chain_gfp
     to coerce things into the right shape. *)
    - reflexivity.
    - step. taul. reflexivity.
    - reflexivity. }
  step in Hfalse. inv Hfalse. easy. 
Qed.  

(* RTODO: see if this is true *)
Lemma euttge_proper_flip_euttgeC {E R1 R2} 
  (RR : R1 -> R2 -> Prop) (c : euttgeC) :
  Proper (euttge (E := E) eq ==> flip (euttge eq) ==> flip impl) (elem c _ _ RR).
Proof with eauto with itree.
  unfold Proper, respectful, flip, impl.
  tower induction.
  clear c; intros c IH x x' EQx y y' EQy; step in EQx; step in EQy.
    icbn; intros EQ.
    genobs x' ox'; genobs y' oy'.
    (* [hinduction] is not sufficient here, because [move] is unable to pass
         through [ox] to reach [x] *)
    revert x x' y y' Heqox' Heqoy' EQx EQy.
    induction EQ; intros.
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genret r1 or1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros; subst; inv Heqor1. clear x Heqox.
        genobs y oy; genret r2 or2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        subst; intros [=<-] ??...
      * intros; subst; taul; eapply IHEQx...
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      gentau m1 om1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros [=<-] ? ??.
        clear x Heqox.
        genobs y oy; gentau m2 om2.
        revert y Heqoy.
        hinduction EQy before om2; try easy.
        intros [=<-] ??...
        intros [=<-] ??.
        taul. subst. step. 
        (* unusable IHEQy: 
        IHEQy : ⊙ t1 = TauF t1 -> forall y : itree E R, 
                ot2 = ⊙ y -> TauF m0 {[≳⟨eq⟩]} ot2 *)
        admit. 
      * intros; subst; taul; eapply IHEQx...
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genvis e k1 ot1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      intros. inv_Vis. 
      apply eqitF_inv_VisF_l in EQy. break EQy; try easy; break H. 
      simpobs...
      intros. taul. eapply IHEQx; eauto.  
    + edestruct euttge_tau_r_inv; [step; eauto |].
      simpobs.
      taul.
      eapply IHEQ; eauto.
      assert (euttge eq (Tau x0) (Tau t1)) by (now step).
      unstep; eapply euttge_tau_inv; eauto.
    + easy. 
Abort. 

(* The correct instance: first arg uses [euttge eq], second uses [eq_itree eq].
   Since euttgeC has b2=false, the right argument cannot skip taus, so we need
   strong bisimulation (eq_itree eq) there, not euttge eq. *)
#[global] Instance euttge_eq_proper_euttgeC {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : euttgeC):
  Proper (euttge (E := E) eq ==> eq_itree eq ==> flip impl) (elem c _ _ RR).
Proof with eauto with itree.
  unfold Proper, respectful, flip, impl.
  tower induction.
  clear c; intros c IH x x' EQx y y' EQy; step in EQx; step in EQy.
    icbn; intros EQ.
    genobs x' ox'; genobs y' oy'.
    revert x x' y y' Heqox' Heqoy' EQx EQy.
    induction EQ; intros.
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genret r1 or1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros; subst; inv Heqor1. clear x Heqox.
        genobs y oy; genret r2 or2.
        revert y Heqoy.
        (* EQy is eq_itree eq (b1=b2=false): EqTauL/EqTauR cases dismissed by [try easy] *)
        hinduction EQy before oy; try easy.
        subst; intros [=<-] ??...
      * intros; subst; taul; eapply IHEQx...
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      gentau m1 om1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros [=<-] ? ??.
        clear x Heqox.
        genobs y oy; gentau m2 om2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        intros [=<-] ??...
      * intros; subst; taul; eapply IHEQx...
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genvis e k1 ot1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros.
        apply eq_inv_VisF_weak in Heqot1 as (-> & ? & ?); cbn in *; subst.
        clear x Heqox.
        genobs y oy; genvis e k2 ot2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        intros; apply eq_inv_VisF_weak in Heqot2 as (-> & ? & ?); cbn in *; subst; eauto with itree.
      * intros; subst; taul; eapply IHEQx...
    + edestruct euttge_tau_r_inv; [step; eauto |].
      simpobs.
      taul.
      eapply IHEQ; eauto.
      assert (euttge eq (Tau x0) (Tau t1)) by (now step).
      unstep; eapply euttge_tau_inv; eauto.
    + easy. 
    (* no EqTauR block: euttgeC has b2=false *)
Qed.

#[global] Instance eq_proper_euttgeC {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : euttgeC):
  Proper (eq_itree (E := E) eq ==> eq_itree eq ==> iff) (elem c _ _ RR).
Proof.
  split; intro.
  - (* forward: t1 ≅ t2, s1 ≅ s2, ̇c t1 s1 → ̇c t2 s2:
       need t2 ≳ t1 (reverse) and s2 ≅ s1 (reverse) *)
    symmetry in H; apply eq_sub_euttge with (RR := eq) in H.
    symmetry in H0.
    eapply euttge_eq_proper_euttgeC; eauto.
  - (* backward: t1 ≅ t2, s1 ≅ s2, ̇c t2 s2 → ̇c t1 s1:
       need t1 ≳ t2 and s1 ≅ s2 (direct) *)
    apply eq_sub_euttge with (RR := eq) in H.
    eapply euttge_eq_proper_euttgeC; eauto.
Qed.


#[global] Instance eq_proper_eq_itreeC {E R1 R2}
  (RR : R1 -> R2 -> Prop) (c : eq_itreeC):
  Proper (eq_itree (E := E) eq ==> eq_itree eq ==> iff) (elem c _ _ RR).
Proof. 
  split; revert_until c; tower induction; intros!;
  step in H0; step in H1; icbn in *.
  (* this proof is largely uninteresting and is just diagram chase. *)
  all: 
  inv H2; simpobs; try easy.
  all: 
  try genvis e k1 ok1; inv H0; simpobs; try easy; 
  try genvis e k2 ok2; inv H1; simpobs; try easy. 
  all: try do 2 inv_Vis; constructor; intros; try eapply H; eauto.
  all: inv H1; inv H0.  
  all: 
  eapply H; try eapply REL0; try eapply REL1; eauto.   
Qed.


(** *** Transitivity properties *)

Inductive rcompose {R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) (r1: R1) (r3: R3) : Prop :=
| rcompose_intro r2 (REL1: RR1 r1 r2) (REL2: RR2 r2 r3)
.
#[global] Hint Constructors rcompose : itree.

Lemma trans_rcompose {R} RR (TRANS: Transitive RR):
  forall x y : R, rcompose RR RR x y -> RR x y.
Proof.
  intros. destruct H; eauto.
Qed.

(* Transitivity of eqit *)
Lemma eqit_trans {E R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) b1 b2 t1 t2 t3
      (INL: eqit b1 b2 RR1 t1 t2)
      (INR: eqit b1 b2 RR2 t2 t3):
  @eqit E b1 b2 _ _ (rcompose RR1 RR2) t1 t3.
Proof.
  unfold eqit. revert_until b2.  
  (* we'll need the coinductive reasoning later: elements of the chain 
  are transitive w.r.t. eqit. *)
  icoinduction c CIH. intros. 
  step in INL. step in INR.
  (* we begin with induction on t1 ~ t2. 
  in each case, we perform induction on t2 ~ t3.  *)
  hinduction INL before CIH; intros; subst. clear t1 t2.
  (* Ret, straightforward *)
  - genret r2 ot.
    hinduction INR before CIH; intros; inv Heqot; eauto with itree.
  - genobs t3 ot3. 
    (* need something more: t3 is either a τ node, or it isn't. *)
    assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; easy. }
    destruct DEC as [[m3 ?] | EQ].
    (* τ - τ case: strip both. *)
    + subst; simpobs. 
      econstructor.
      eapply CIH; eauto.
      apply eqit_inv_Tau.
      now step.    
    (* τ - ̸τ : we do further case analysis. *)
    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      taul. 
      step in REL.
      hinduction REL0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      (* now we can handle each subcase with another layer of induction *)
      * remember (RetF r1) as ot.
        hinduction REL0 before CIH; intros; inv Heqot; eauto with itree.
      * remember (VisF e k1) as ot.
        hinduction REL0 before CIH; intros; try discriminate; [ inv_Vis | eauto with itree ].
        econstructor. intros.
        apply (CIH _ _ _ (REL v) (REL0 v)). 
      * eapply IHREL0; eauto.
        destruct b1; inv CHECK0.
        unstep. apply eqit_inv_Tau_r. now step. 
  - remember (VisF e k2) as ot.
    hinduction INR before CIH; intros; try discriminate; [ inv_Vis | eauto with itree ].
    econstructor. intros.
    apply (CIH _ _ _ (REL0 v) (REL v)). 
  - eauto with itree.
  - gentau t0 ot.
    genobs t3 ot3. 
    hinduction INR before CIH; intros; try inversion Heqot; subst.
    + eapply (IHINL (Tau m2)).
      step in REL. eauto with itree.
    + now eapply IHINL.
    + taur. eapply IHINR; eauto. 
Qed.
Arguments eqit_trans {E R1 R2 R3} [RR1 RR2 b1 b2 t1 t2 t3].
(* We can now package the instances for the top level relations:
   two equivalences and a preorder as expected.
 *)
#[global] Instance Transitive_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b1 b2: bool):
  Transitive RR -> Transitive (@eqit E b1 b2 _ _ RR).
Proof.
  red; intros. assert (TRANS := trans_rcompose RR). 
  eapply eqit_mono, eqit_trans; eauto.
  repeat intro. now apply TRANS.
Qed.

#[global] Instance Transitive_eqit_eq {E : Type -> Type} {R: Type} (b1 b2: bool):
  Transitive (@eqit E b1 b2 R R eq).
Proof.
  apply Transitive_eqit. repeat intro; subst; eauto.
Qed.

#[global] Instance Equivalence_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b: bool):
  Equivalence RR -> Equivalence (@eqit E b b R R RR).
Proof.
  constructor; try typeclasses eauto.
Qed.

#[global] Instance Equivalence_eqit_eq {E : Type -> Type} {R: Type} (b: bool):
  Equivalence (@eqit E false false R R eq).
Proof.
  constructor; try typeclasses eauto.
Qed.

#[global] Instance Transitive_eutt {E R RR} : Transitive RR -> Transitive (@eutt E R R RR).
Proof.
  red; intros. assert (TRANS := trans_rcompose RR). eapply eqit_mono, eqit_trans; eauto.
  repeat intro. now apply TRANS. 
Qed.


#[global] Instance Transitive_elem {E R RR} (HT : Transitive RR)
  {c: Chain (@eqit_mon E false false)}: Transitive (elem c R R RR).
Proof.
  assert (Hinf : inf_closed (X := forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop)
    (fun x => Transitive (x R R RR))).
  { intros T HTr x y z Hxy Hyz i Hi. apply (HTr _ Hi) with y; [exact (Hxy i Hi) | exact (Hyz i Hi)]. }
  revert c. apply (tower Hinf). intros c Htrans.
  apply Transitive_eqit_; auto.
Qed.

#[global] Instance Equivalence_elem {E R RR} (HT : Equivalence RR)
  {c: Chain (@eqit_mon E false false)}: Equivalence (elem c R R RR).
Proof.
  constructor; typeclasses eauto.
Qed.  

Lemma rcompose_eql {R1 R2} (RR : R1 -> R2 -> Prop) : eq_rel (rcompose eq RR) RR.
Proof.
  split; [intros ?? []; now subst | intros ???; now econstructor].
Qed.
Lemma rcompose_eqr {R1 R2} (RR : R1 -> R2 -> Prop) : eq_rel (rcompose RR eq) RR.
Proof.
  split; [intros ?? []; now subst | intros ???; econstructor; eauto].
Qed.

#[global] Instance eutt_cong_eutt_eq {E R1 R2 RS}:
  Proper (eutt eq ==> eutt eq ==> iff)
         (@eutt E R1 R2 RS).
Proof.
  repeat red. 
  intros t t' EQ1 u u' EQ2.
  split; intros EQUIV. 
  - symmetry in EQ1. 
    pose proof eqit_trans EQ1 EQUIV as EQUIV'.
    rewrite rcompose_eql in EQUIV'.
    pose proof eqit_trans EQUIV' EQ2 as EQUIV''.
    now rewrite rcompose_eqr in EQUIV''.
  - pose proof eqit_trans EQ1 EQUIV as EQUIV'.
    rewrite rcompose_eql in EQUIV'.
    symmetry in EQ2.
    pose proof eqit_trans EQUIV' EQ2 as EQUIV''.
    now rewrite rcompose_eqr in EQUIV''.
Qed.

#[global] Instance Equivalence_eutt {E R RR} : Equivalence RR -> Equivalence (@eutt E R R RR).
Proof.
  typeclasses eauto.
Qed.

#[global] Instance Transitive_euttge {E R RR} : Transitive RR -> Transitive (@euttge E R R RR).
Proof.
  red; intros. assert (TRANS := trans_rcompose RR). eapply eqit_mono, eqit_trans; eauto.
  repeat intro. now apply TRANS. 
Qed.

#[global] Instance PreOrder_euttge {E R RR} : PreOrder RR -> PreOrder (@euttge E R R RR).
Proof.
  constructor; typeclasses eauto. 
Qed.

#[global] Instance eq_proper_eq {E R1 R2}
  (RR : R1 -> R2 -> Prop):
  Proper (eq_itree (E := E) eq ==> (eq_itree (R2 := R2) eq) ==> iff) (eq_itree eq). 
Proof. 
  split; 
  repeat intro.
  do 2 (etransitivity; symmetry; eauto).
  do 2 (etransitivity; eauto); now symmetry. 
Qed.



(* Ongoing sanity tests *)
Module Tests.
  #[local] Parameter E : Type -> Type.
  #[local] Parameter R1 R2 : Type.
  #[local] Parameter RR : R1 -> R2 -> Prop.
  #[local] Parameter t u : itree E R1.
  #[local] Parameter v w : itree E R2.
  #[local] Parameter (EQ1 : t ≅ u).
  #[local] Parameter (EQUIV1 : t ≈ u).
  #[local] Parameter (EQ2 : v ≅ w).
  #[local] Parameter (EQUIV2 : v ≈ w).
  #[local] Parameter (GT : v ≳ w).
  #[local] Parameter (GT2 : w ≳ v).

Goal eutt RR u v.
    rewrite EQUIV2.
    rewrite <- EQ2.
    eapply eq_proper_euttC.
    rewrite <- EQ1.
    exact EQ1. 
    rewrite EQ2, <- EQ2. 
    exact EQ2.
    step.
    step. 
    rewrite <- EQ1. 
    rewrite <- GT. 
    rewrite EQ1.
    rewrite <- EQUIV1.  
Abort. 

  #[local] Parameter (EQUIV : u ≈⟨RR⟩ v).

  (* TODO: have tests work with a relation on leaves.
     Currently fails, need better instance
   *) 
  (* Test for rewrites in [eutt]: [eq_itree eq], [] *)
  Goal t ≈⟨RR⟩ w -> t ≈⟨RR⟩ w.
    intros H.
    rewrite EQ1.
    rewrite EQ1 in H.
    rewrite <- EQUIV1.
    (* ↕ these are eutt up to eutt *)
    rewrite <- EQUIV1 in H.
    rewrite <- EQUIV2 in H. 
    rewrite GT2.
    rewrite <- GT2 in H.
    rewrite GT.
    rewrite <- GT in H.
    (* no way to use symmetry: RR cannot be symmetric *)
    Fail symmetry.
    Fail symmetry in H.
    rewrite <- GT. 
    assumption. 
  Qed.

  (* RTODO: next *)
  Definition VE := fun _ : Type => Empty_set. 
  #[local] Parameter (EQUIV_tt : eutt (E:= VE) eq (Ret tt) (Ret tt)).
  Goal eutt (E:= VE) eq (Ret tt) (Ret tt). 
    step.  
    (* THIS SHOULD WORK *)
    unstep. 
    assert (eutt (E:= VE) eq (Ret tt) (Ret tt)). 
    step.
    (* we should be able to fold into observe form *)
    rewrite observing_observe.  
Abort. 
   (* RTODO: These *)
  Goal t ≅ u -> t ≅ u.
    intros H.
    rewrite EQ1.
    rewrite EQ1 in H.
    symmetry.
    symmetry in H.
    reflexivity.
  Qed.
   (* 2. next: this: euttge RR is proper wrt eq_itree RR - make sure this works *)
  Goal t ≅ u -> v ≅⟨flip RR⟩ u -> t ≳⟨RR⟩ v -> t ≳⟨RR⟩ v.
    intros EQ1 EQ2' H.
    rewrite EQ1.
    rewrite EQ2.
    apply eqit_flip in EQ2'.
    rewrite EQ2 in EQ2'. 
    (* eapply (eqit_mono RR RR false false); eauto.  *)
    (* next todo: get this to work *)
    Fail rewrite EQ2'.  
    Fail rewrite <- EQ2'.  
     (* TO FIX: only going through subrelation is insuficient *)
  Admitted.

  (* Test [coinduction] tactic, notations  *)
  Goal u ≈ t -> t ≈ u.
    icoinduction r cih.
    intros.
    step. 
    rewrite H. 
    reflexivity. 
Qed. 
End Tests.

#[global] Hint Resolve Reflexive_eqit : reflexivity.




Section eqit_eq.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R : Type}.

Local Notation eqit := (fun b1 b2 => @eqit E b1 b2 R R eq).

#[global] Instance Reflexive_eqitF_eq b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqitF eq b1 b2 sim).
Proof.
  apply Reflexive_eqitF; eauto.
Qed.

#[global] Instance Symmetric_eqitF_eq b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqitF eq b b sim).
Proof.
  apply Symmetric_eqitF; eauto. 
Qed.

#[global] Instance Reflexive_eqit__eq b1 b2
  (sim : forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop)
: Reflexive (sim R R eq) -> Reflexive (eqit_ b1 b2 sim R R eq).
Proof. apply Reflexive_eqit_; eauto. Qed.

#[global] Instance Symmetric_eqit__eq b
  (sim : forall R1 R2, (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop)
: Symmetric (sim R R eq) -> Symmetric (eqit_ b b sim R R eq).
Proof. apply Symmetric_eqit_; eauto. Qed.

(** *** [eqit] is an equivalence relation *)

#[global] Instance Reflexive_eqit_eq b1 b2 : Reflexive (eqit b1 b2).
Proof.
  apply Reflexive_eqit; eauto.
Qed.

#[global] Instance Symmetric_eqit_eq b : Symmetric (eqit b b).
Proof.
  apply Symmetric_eqit; eauto.
Qed.

(** *** Congruence properties *)
#[global] Instance eqit_observe b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@observe E R).
Proof.
  constructor; step in H; step; auto with itree.  
Qed. 

#[global] Instance eqit_tauF b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@TauF E R _).
Proof.
  constructor; step. econstructor. eauto.
Qed.

#[global] Instance eqit_VisF b1 b2 {u} (e: E u) :
  Proper (pointwise_relation _ (eqit b1 b2) ==> going (eqit b1 b2)) (VisF e).
Proof.
  constructor; red in H. step; econstructor; auto with itree.
Qed.

#[global] Instance observing_sub_eqit l r :
  subrelation (observing eq) (eqit l r).
Proof.
  repeat red; intros.
  step. rewrite (observing_observe H). apply Reflexive_eqitF; eauto.
Qed.

#[global] Instance observing_sub_elem b1 b2 (c : Chain (eqit_mon b1 b2)) (l r : itree E R) :
  subrelation (@observing E R R eq) (elem c R R eq).
Proof.
  repeat intro.
  inv H.
  step.
  rewrite observing_observe.
  step. reflexivity.
Qed.

(** ** Eta-expansion *)

Lemma itree_eta_ (t : itree E R) : t ≅ go (_observe t).
Proof. apply observing_sub_eqit. econstructor. reflexivity. Qed.

Lemma itree_eta (t : itree E R) : t ≅ go (observe t).
Proof. apply itree_eta_. Qed.

Lemma itree_eta' (ot : itree' E R) : ot = observe (go ot).
Proof. reflexivity. Qed.

End eqit_eq.

(** *** One-sided inversion *)

Lemma eqitree_inv_Ret_r {E R} (t : itree E R) r :
  t ≅ (Ret r) -> observe t = RetF r.
Proof.
  intros; step in H; inv H; try inv CHECK; eauto.
Qed.

Lemma eqitree_inv_Vis_r {E R U} (t : itree E R) (e : E U) (k : U -> _) :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ forall u, k' u ≅ k u.
Proof.
  intros; step in H; apply eqitF_inv_VisF_r in H.
  destruct H as [ [? [-> ?]] | [] ]; [ | discriminate ].
  eexists; split; eauto.
Qed.

Lemma eqitree_inv_Tau_r {E R} (t t' : itree E R) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; step in H; inv H; try inv CHECK; eauto.
Qed.

Lemma eqit_inv_Ret {E R1 R2 RR} b1 b2 r1 r2 :
  @eqit E b1 b2 R1 R2 RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. step in H. inv H. eauto.
Qed.

(* Axiom-free, weaker version of [eqit_inv_vis] *)
Lemma eqit_inv_Vis_weak {E R1 R2 RR} b1 b2
  {u1 u2} (e1 : E u1) (e2 : E u2) (k1: u1 -> itree E R1) (k2: u2 -> itree E R2) :
  eqit b1 b2 RR (Vis e1 k1) (Vis e2 k2) ->
  exists p, eqeq E p e1 e2 /\ pweqeq (eqit b1 b2 RR) p k1 k2.
Proof.
  intros. step in H; apply eqitF_inv_VisF_weak in H.
  destruct H as [ p []]. exists p; split; auto.
Qed.

(* This assumes UIP. *)
Lemma eqit_inv_Vis {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2 U (e : E U)
    (k1 : U -> itree E R1) (k2 : U -> itree E R2)
  : eqit b1 b2 RR (Vis e k1) (Vis e k2) ->
    forall u, eqit b1 b2 RR (k1 u) (k2 u).
Proof.
  intros H x; step in H; apply eqitF_inv_VisF with (x := x) in H; auto.
Qed.

(* Other properties: RTODO sort these *)
Lemma eutt_inv_Ret {E R} r1 r2 :
  (Ret r1: itree E R) ≈ (Ret r2) -> r1 = r2.
Proof.
  intros; eapply eqit_inv_Ret; eauto.
Qed.

Lemma eqitree_inv_Ret {E R} r1 r2 :
  (Ret r1: itree E R) ≅ (Ret r2) -> r1 = r2.
Proof.
  intros; eapply eqit_inv_Ret; eauto.
Qed.

Lemma eqit_Tau_l {E R1 R2 RR} b2 (t1 : itree E R1) (t2 : itree E R2) :
  eqit true b2 RR t1 t2 -> eqit true b2 RR (Tau t1) t2.
Proof.
  intros. step. econstructor; eauto. now step in H. 
Qed.

Lemma eqit_Tau_r {E R1 R2 RR} b1 (t1 : itree E R1) (t2 : itree E R2) :
  eqit b1 true RR t1 t2 -> eqit b1 true RR t1 (Tau t2).
Proof.
  intros. step. econstructor; eauto. now step in H. 
Qed.

Lemma tau_euttge {E R} (t: itree E R) :
  Tau t ≳ t.
Proof.
  apply eqit_Tau_l. reflexivity.
Qed.

Lemma tau_eutt {E R} (t: itree E R) :
  Tau t ≈ t.
Proof.
  apply euttge_sub_eutt, tau_euttge.
Qed.


Lemma simpobs {E R} {ot} {t: itree E R} (EQ: ot = observe t): t ≅ go ot.
Proof.
  step. repeat red. simpobs. simpl. subst. unstep. apply Reflexive_eqit; eauto.
Qed.

(** *** Transitivity properties *)

Add Parametric Morphism {E R1 R2 RR1 RR2 RS} b1 b2
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) : 
         (@eqit E b1 b2 R1 R2 RS)
         with signature (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         as eqitgen_cong_eqit. 
Proof. 
repeat intro; unfold flip, eq_itree in *. 

  (* Given *)
  (* LERR1: ∀ x x' y. RR1 x x' -> RS x' y -> RS x y *)
  (* LERR2: ∀ x y y'. RR2 y y' -> RS x y' -> RS x y, *)
  (* Prove the diagram commutes *)
  
  (* 
   y -(eqit b1 b2 RS) → y0 
   ↑                    ↑
   ≅RR1                ≅RR2
   |                    | 
   x -(?eqit b1 b2 RS)→ x0
  *)

  (* Problem: this diagram does not have a path from x to x0. *)
  (* Solution: flip ≅RR2, as both boolean flags are false to 
    begin with this is a "symmetry" on trees only. *)

(* 
   y -(eqit b1 b2 RS) → y0 
   ↑                    |
   ≅RR1                ≅(flip RR2)
   |                    ↓ 
   x -(?eqit b1 b2 RS)→ x0

(* This diagram has a clear path (lifting with eqit_mono), 
  and LERR1 and LERR2 get us the correlaries we need to arrive there: namely: *)
*)
(*  by LERR1, Ret nodes of x and Ret nodes of y0 are related by RS. 
    by LERR2, Ret nodes of x0 and Ret nodes of y are related by RS. 
    RR1 ∘ RS <= RS 
    (flip RR2) ∘ RS <= RS 
    so RS is closed under left composition by RR1
    and right composition by flip RR2.
  *)
  (* We use a mix of foreward and backward reasoning. *)
  
  idtac. 
  (* build arrows and strengthen *)
  assert (rcompose RR1 RS <= RS) by (intros ? ? [? ?]; eauto). 
  assert (rcompose RS (flip RR2) <= RS) by (intros ? ? [? ?]; eauto).
  assert (eqit b1 b2 RR1 x y) by 
  (eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR1); easy).
  assert (eqit b1 b2 RR2 x0 y0) by 
  (eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR2); try easy).  

  (* first diagonal *)
  specialize (eqit_trans H4 H1) as Hdiag_weak. 
  assert (eqit b1 b2 RS x y0) as Hdiag by 
  (eapply eqit_mono with (RR:=(rcompose RR1 RS)); eauto).
  
  (* reverse the final arrow *)
  apply eqit_flip in H0.
  
  (* backward reasoning, straightforward *)
  eapply eqit_mono with (RR:=(rcompose RS (flip RR2))); eauto. 
  eapply eqit_trans; eauto. 
  eapply eqit_mono with (b1:=false) (b2:=false) (RR:=(flip RR2)); easy. 
Qed. 



(* Auxiliary results on [itree]s. *)

Lemma tau_eutt_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eutt RR (Tau t) s <-> eutt RR t s.
Proof.
  intros.
  split; intros H.
  - eapply transitivity. 2 : { apply H. }
    red. apply eqit_Tau_r. reflexivity.
  - red. red. step. econstructor. auto. now step in H. 
Qed.

Lemma tau_eqit_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eqit true false RR t s -> eqit true false RR (Tau t) s.
Proof.
  intros.
  red. step. econstructor. auto. now step in H. 
Qed.

Lemma tau_eutt_RR_r : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eutt RR t (Tau s) <-> eutt RR t s.
Proof.
  intros.
  split; intros H.
  - eapply transitivity. apply H.
    red. apply eqit_Tau_l. reflexivity.
  - red. red. step. econstructor. auto. now step in H.
Qed.

Lemma eutt_inv_Ret_l {E R} (r1: R) (t2: itree E R):
  (Ret r1) ≈ t2 -> t2 ≳ (Ret r1).
Proof.
  intros Heutt. step in Heutt. 
  rewrite itree_eta. 
  remember (observe (Ret r1)).
  genobs t2 ot2.
  remember {| _observe := ot2 |}.
  hinduction Heutt before r1; intros; inv Heqi. 
  - reflexivity.
  - rewrite tau_euttge. rewrite itree_eta. now eapply IHHeutt.
Qed.

(* The trick with these observe induction proofs 
  is often to go 'as high as possible...' *)
Lemma eutt_inv_Ret_r {E R} (t1: itree E R) (r2: R):
  t1 ≈ (Ret r2) -> t1 ≳ (Ret r2).
Proof.
  intros Heutt. step in Heutt.  
  rewrite itree_eta. 
  remember (observe (Ret r2)); genobs t1 ot1; remember {| _observe := ot1 |}.
  hinduction Heutt before R; intros; inv Heqi. 
  - reflexivity.
  - rewrite tau_euttge. rewrite itree_eta. now eapply IHHeutt.
Qed.

(** ** Equations for core combinators *)

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => ITree.bind (ke x) k)
  | TauF t => Tau (ITree.bind t k)
  end.

Lemma unfold_bind {E R S} (t : itree E R) (k : R -> itree E S)
  : ITree.bind t k ≅ bind_ t k.
Proof.
  apply observing_sub_eqit; constructor; reflexivity.
Qed.

Lemma bind_ret_l {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k ≅ (k r).
Proof. apply observing_sub_eqit, bind_ret_. Qed.

Lemma bind_tau {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof. apply (unfold_bind (Tau t) k). Qed.

Lemma bind_vis {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof. apply (unfold_bind (Vis e ek) k). Qed.

Lemma bind_trigger {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k ≅ Vis e (fun x => k x).
Proof.
  rewrite unfold_bind; cbn.
  step.
  constructor.
  intros. apply bind_ret_l.
Qed.

Lemma unfold_iter {E A B} (f : A -> itree E (A + B)) (x : A) :
  (ITree.iter f x) ≅ ITree.bind (f x) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l))).
Proof.
  rewrite unfold_aloop_. reflexivity.
Qed.

Lemma unfold_forever {E R S} (t : itree E R)
  : @ITree.forever E R S t ≅ ITree.bind t (fun _ => Tau (ITree.forever t)).
Proof.
  rewrite itree_eta, (itree_eta (ITree.bind _ _)).
  reflexivity.
Qed.

Ltac auto_ctrans :=
  intros; repeat (match goal with [H: rcompose _ _ _ _ |- _] => destruct H end); subst; eauto.
Ltac auto_ctrans_eq := try instantiate (1:=eq); auto_ctrans.

Section eqit_h.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(** [eqit] is a congruence for [itree] constructors. *)

Lemma eqit_Tau b1 b2 (t1 : itree E R1) (t2 : itree E R2) :
  eqit b1 b2 RR (Tau t1) (Tau t2) <-> eqit b1 b2 RR t1 t2.
Proof.
  split; intros H.
  - step in H. step.  
    move H before RR. revert_until H.
    remember (observe (Tau t1)). 
    remember (observe (Tau t2)). 
    genobs t1 ot1. 
    genobs t2 ot2. 
    hinduction H before RR; intros; inv Heqi; try inv Heqi0. 
    + now unstep. 
    + inv H. 
      * taul. eapply IHeqitF; eauto. 
      * taul. eapply IHeqitF; eauto. 
      * assumption. 
    + inv H. 
      * taur. eapply IHeqitF; eauto. 
      * assumption. 
      * taur. eapply IHeqitF; eauto. 
  - step. now constructor.   
Qed. 

Lemma eqit_Vis_gen b1 b2 {U1 U2} (p : U1 = U2) (e1 : E U1) (e2 : E U2)
      (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2)
  : eqeq E p e1 e2 -> pweqeq (eqit b1 b2 RR) p k1 k2 ->
    eqit b1 b2 RR (Vis e1 k1) (Vis e2 k2).
Proof.
  destruct p; cbn. intros <- H. step. econstructor. apply H.
Qed.

Lemma eqit_Vis b1 b2 {U} (e : E U)
    (k1 : U -> itree E R1) (k2 : U -> itree E R2)
  : (forall u, eqit b1 b2 RR (k1 u) (k2 u)) ->
    eqit b1 b2 RR (Vis e k1) (Vis e k2).
Proof.
  apply eqit_Vis_gen with (p := eq_refl); constructor.
Qed.

Lemma eqit_Ret b1 b2 (r1 : R1) (r2 : R2) :
  RR r1 r2 <-> @eqit E b1 b2 _ _ RR (Ret r1) (Ret r2).
Proof.
  split; intros H.
  - step. constructor; auto.
  - step in H. inversion H; subst; auto.
Qed.

(** *** "Up-to" principles for coinduction. *)

(* One could consider making this a respectful instance. *)
(* This might be good when doing other proofs, as it shows up 
often. *)

Lemma eqit_clo_bind_chain
 b1 b2 (c : Chain (eqit_mon b1 b2)) {U1 U2}
 (t1 : itree E U1) (t2 : itree E U2) 
 (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2) (UU : U1 -> U2 -> Prop) : 
elem c _ _ UU t1 t2 -> 
(forall u1 u2, UU u1 u2 -> elem c _ _ RR (k1 u1) (k2 u2)) -> 
elem c _ _ RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof. 
  revert_until U2. 
  tower induction. 
  - intros. 
  eapply H0; eauto.   
 - intros. 
  icbn in *. 
  genobs t1 ot1.  
  genobs t2 ot2.
  hinduction H0 before RR; intros; try easy. 
(* be careful not to rewrite all here; this will mess up taul and taur cases. *)
  1-3: rewrite 2observe_bind; simpobs.
  (* ret *)
  + eapply H1; eauto. 
  (* taus *)
  + constructor.
    eapply H; eauto. 
    intros; step; now eapply H1.
  (* vis *)
  + constructor. 
    intro. 
    eapply H; eauto.
    intros; step; now eapply H1.
  (* taul *)
  + rewrite observe_bind. 
    simpobs. 
    taul. 
    eapply IHeqitF; eauto.  
  (* taur *)
  + setoid_rewrite observe_bind at 2. 
    simpobs. 
    taur. 
    eapply IHeqitF; eauto. 
Qed. 



Lemma eutt_clo_bind {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eutt E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eutt RR (k1 u1) (k2 u2)):
  eutt RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
    unfold eutt. eapply eqit_clo_bind_chain; eauto.  
Qed. 

Lemma eutt_clo_bind_chain {U1 U2 UU} t1 t2 k1 k2
      (c : euttC)
      (EQT: @eutt E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eutt RR (k1 u1) (k2 u2)):
  eqit_mon true true (elem c) _ _ RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
    eapply eqit_clo_bind_chain; intros. 
    all: now do 2 step; [apply EQT || apply EQK].
Qed. 


End eqit_h.

Ltac ebind := eapply eqit_clo_bind_chain; eauto with itree.  


Lemma eutt_Tau {E R} (t1 t2 : itree E R):
  Tau t1 ≈ Tau t2 <-> t1 ≈ t2.
Proof.
  apply eqit_Tau.
Qed.

Lemma eqitree_Tau {E R} (t1 t2 : itree E R):
  Tau t1 ≅ Tau t2 <-> t1 ≅ t2.
Proof.
  apply eqit_Tau.
Qed.

Lemma eqit_bind' {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) b1 b2
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eqit b1 b2 RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eqit b1 b2 RS (k1 r1) (k2 r2)) ->
  @eqit E b1 b2 _ _ RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros.
  eapply eqit_clo_bind_chain; eauto. 
Qed.

Lemma eq_itree_clo_bind {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eq_itree E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eq_itree RR (k1 u1) (k2 u2)):
  eq_itree RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  eapply eqit_bind'; eauto.
Qed.

(* RTODO: want

Proper (eutt ==> pointwise_chain ==> chain) bind 

want something finer-grained- eutt lifts a relation 

Choose any postcondition SS. eutt over SS, pointwise_chain over SS. 

we want to pull this out. 

(* 
[shelved]. trans true false elem c
[done]1. remove dep. induction 
2. consider coinduction library fix- mwe at least 
[with yannick] 3. think about removing bind_clo and replacing with proper instance
3.a very strong bespoke proper instance- pull out R1 R2 RR etc. 

*)

forall t u SS, (elem c SS t u ==> forall x y, SS x y -> elem c (k x) (g y) -> elem c (bind t k) bind u g)
*)

#[global] Instance eqit_subst {E R S} b1 b2 :
  Proper (pointwise_relation _ (eqit b1 b2 eq) ==> eqit b1 b2 eq ==>
          eqit b1 b2 eq) (@ITree.subst E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

#[global] Instance eqit_bind {E R S} b1 b2 :
  Proper (eqit b1 b2 eq ==> pointwise_relation _ (eqit b1 b2 eq) ==>
          eqit b1 b2 eq) (@ITree.bind E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

(* #[global] Instance eqit_bind {E R S} b1 b2 :
  Proper (eqitF eq b1 b2 ==> pointwise_relation _ (eqitF eq b1 b2) ==>
          eqitF eq b1 b2) (@ITree.bind E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed. *)


Lemma eqit_map {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) b1 b2
      (RS : S1 -> S2 -> Prop)
      f1 f2 t1 t2 :
  (forall r1 r2, RR r1 r2 -> RS (f1 r1) (f2 r2)) ->
  @eqit E b1 b2 _ _ RR t1 t2 ->
  eqit b1 b2 RS (ITree.map f1 t1) (ITree.map f2 t2).
Proof.
  unfold ITree.map; intros.
  eapply eqit_bind'; eauto.
  intros; step; constructor; auto.
Qed.

#[global] Instance eqit_eq_map {E R S} b1 b2 :
  Proper (pointwise_relation _ eq ==>
          eqit b1 b2 eq ==>
          eqit b1 b2 eq) (@ITree.map E R S).
Proof.
  repeat intro; eapply eqit_map; eauto.
  intros; subst; auto.
Qed.

Add Parametric Morphism {E R1}:
        (eqit_ false false (gfp (eqit_mon false false)) _ _ eq)
         with signature (@eq_itree E R1 _ eq ==> eq_itree eq ==> flip impl)
         as eqitF_cong_eqit. 
Proof. 
  red; intros. 
  unstep. rewrite H. rewrite H0. now step. 
Qed. 


#[global] Instance trans_elem_eq_itree_mon {E R} (c : Chain (@eqit_mon E false false)) :
  Transitive (elem c R R eq).
Proof.
  apply Transitive_elem. typeclasses eauto. 
Qed.

Add Parametric Morphism {E R} (c : Chain (@eqit_mon E false false)) :
  (elem c R R eq)
  with signature (observing eq ==> observing eq ==> flip impl)
  as elem_observing_proper. 
Proof. 
  intros x y Hxy x' y' Hx'y' Helem.
  symmetry in Hx'y'.  
  eapply observing_sub_elem in Hxy; eauto.
  eapply observing_sub_elem in Hx'y'; eauto.
  do 2 (etransitivity; eauto).  
Qed.   

(* This lemma requires a bit of cleverness: [elem c], where [c] is [Chain
(eqit_mon eq false false)], is respected by [observing eq]. Such respectfulness
in turn reqires transitivity of [elem c] and the fact that [observing eq] is a
subrelation of [elem c]. Some work in the reasoning, but with short proofs- and
worth it! 
*)
Lemma bind_ret_r {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  unfold eq_itree. intros.
   (* we need to eta-expland first, but we have to be able 
   to reduce later. *)
  rewrite (itree_eta_ (ITree.bind _ _)), (itree_eta s).
  (* need strong CIH *)
  revert s. 
  icoinduction c CIH. 
  intros.
  (* with eta-reduction in place, we can reduce to base comparisons. *)
  desobs s H; cbn; simpobs; constructor; intros.
  (* Ret case is easy *)
  reflexivity. 
  (* the others are more tricky but mostly identical: *)
  (* 1. we need only show the two sides are related by elem under [observe]. *)
  all: eapply elem_observing_proper.
  (* 2. we know they are by the CIH... *)
  all: try eapply CIH.
  (* 3. so the rest is just 'fancy reflexivity. *)
  all: constructor; reflexivity. 
Qed. 

Lemma bind_ret_r' {E R} (u : itree E R) (f : R -> R) :
  (forall x, f x = x) ->
  ITree.bind u (fun r => Ret (f r)) ≅ u.
Proof.
  intro H. rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - reflexivity.
  - hnf. intros. apply eqit_Ret. auto.
Qed.

Ltac fold_subst := 
  repeat match goal with 
  |- context[ITree.subst ?k ?s] => 
    replace (ITree.subst k s)
    with (ITree.bind s k)
    by reflexivity
  end. 

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  unfold eq_itree. intros. 
  lazymatch goal with
  | [ |- _ (ITree.bind ?t1 _) ?t2 ] => rewrite (itree_eta_ t1), (itree_eta_ t2); cbn
  end.
  lazymatch goal with
  | [ |- _ ?t0 _ ] => rewrite (itree_eta_ t0); cbn
  end.
  revert s k h. 
  icoinduction c CIH.
  intros.
  desobs s H; cbn; simpobs. 
  1: step. reflexivity. 
  all: constructor; intros; eapply elem_observing_proper.
  all: try eapply CIH.
  all: constructor. 
  all: fold_subst. 
  all: repeat rewrite observe_bind.
  all: reflexivity.
Qed.


Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_map {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma map_bind {E X Y Z} (t: itree E X) (k: X -> itree E Y) (f: Y -> Z) :
  (ITree.map f (ITree.bind t k)) ≅ ITree.bind t (fun x => ITree.map f (k x)).
Proof.
  intros. unfold ITree.map. apply bind_bind.
Qed.

Lemma map_ret {E A B} (f : A -> B) (a : A) :
    @ITree.map E _ _ f (Ret a) ≅ Ret (f a).
Proof.
  intros. unfold ITree.map.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma map_tau {E A B} (f : A -> B) (t : itree E A) :
    @ITree.map E _ _ f (Tau t) ≅ Tau (ITree.map f t).
Proof.
  intros.
  unfold ITree.map.
  rewrite bind_tau; reflexivity.
Qed.

#[global] Hint Rewrite @bind_ret_l : itree.
#[global] Hint Rewrite @bind_ret_r : itree.
#[global] Hint Rewrite @bind_tau : itree.
#[global] Hint Rewrite @bind_vis : itree.
#[global] Hint Rewrite @bind_map : itree.
#[global] Hint Rewrite @map_ret : itree.
#[global] Hint Rewrite @map_tau : itree.
#[global] Hint Rewrite @bind_bind : itree.

(** ** Tactics *)

Ltac force_left :=
  match goal with
  | [ |- _ ?x _ ] => rewrite (itree_eta x); cbn
  end.

Ltac force_right :=
  match goal with
  | [ |- _ _ ?x ] => rewrite (itree_eta x); cbn
  end.

(** Remove all taus from the left hand side of the goal equation
    (assumed to be of the form [lhs ≈ rhs]). *)
Ltac tau_steps_left :=
  repeat (force_left; rewrite tau_eutt); force_left.

(** Remove all taus from the right hand side of the goal equation. *)
Ltac tau_steps_right :=
  repeat (force_right; rewrite tau_eutt); force_right.

(** Remove all taus from both sides of the goal equation. *)
Ltac tau_steps :=
  tau_steps_left;
  tau_steps_right.

Ltac force_left_in H :=
  match type of H with _ ?x _ => rewrite (itree_eta x) in H; cbn in H end.

Ltac force_right_in H :=
  match type of H with _ _ ?x => rewrite (itree_eta x) in H; cbn in H end.

Ltac tau_steps_left_in H :=
  repeat (force_left_in H; rewrite tau_eutt in H); force_left_in H.

Ltac tau_steps_right_in H :=
  repeat (force_right_in H; rewrite tau_eutt in H); force_right_in H.

Ltac tau_steps_in H :=
  tau_steps_left_in H;
  tau_steps_right_in H.

Lemma eqit_inv_bind_ret:
  forall {E X R1 R2 RR} b1 b2
    (ma : itree E X) (kb : X -> itree E R1) (b: R2),
    @eqit E b1 b2 R1 R2 RR (ITree.bind ma kb) (Ret b) ->
    exists a, @eqit E b1 b2 X X eq ma (Ret a) /\
         @eqit E b1 b2 R1 R2 RR (kb a) (Ret b).
Proof.
  intros.
  step in H.
  remember (observe (ITree.bind ma kb)) as otl.
  remember (Ret b) as retb. 
  remember (observe retb) as tr.
  revert ma kb Heqotl b retb Heqretb Heqtr.
  hinduction H before RR; intros; subst; try discriminate.
  - intros; subst.
    unfold observe, _observe in Heqotl; cbn in Heqotl.
    destruct (observe ma) eqn:Ema; try discriminate.
    exists r. split.
    * rewrite itree_eta, Ema. reflexivity.
    * rewrite itree_eta_. unfold _observe. rewrite <- Heqotl. inv Heqtr. 
    step; constructor; auto.
  - intros. subst.
    unfold observe, _observe in Heqotl; cbn in Heqotl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + exists r. split.
      * rewrite itree_eta, Ema. reflexivity.
      * step. unfold observe at 1; unfold _observe. rewrite <- Heqotl. constructor; auto.
    + inv Heqotl. 
      edestruct IHeqitF; eauto. exists x. 
      destruct H0. 
      split; eauto.
      step; rewrite Ema. taul. 
      now step in H0. 
Qed.

Lemma eutt_inv_bind_ret:
  forall {E A B} (ma : itree E A) (kb : A -> itree E B) b,
    ITree.bind ma kb ≈ Ret b ->
    exists a, ma ≈ Ret a /\ kb a ≈ Ret b.
Proof.
  intros; apply eqit_inv_bind_ret; auto.
Qed.

Lemma eqitree_inv_bind_ret:
  forall {E A B} (ma : itree E A) (kb : A -> itree E B) b,
    ITree.bind ma kb ≅ Ret b ->
    exists a, ma ≅ Ret a /\ kb a ≅ Ret b.
Proof.
  intros; apply eqit_inv_bind_ret; auto.
Qed.

Ltac inv_eq_VisF H :=
  lazymatch type of H with
  | (VisF _ _ = @VisF _ _ _ ?X ?e ?k) =>
    refine
      match H in _ = w return
        match w with
        | VisF e k => _
        | _ => False
        end
      with eq_refl => _
      end; try clear H X e k
  end.

Lemma eqit_inv_bind_vis :
  forall {A B C E X RR} b1 b2
    (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxc : X -> itree E C),
    eqit b1 b2 RR (ITree.bind ma kab) (Vis e kxc) ->
    (exists (kxa : X -> itree E A), (eqit b1 b2 eq ma (Vis e kxa)) /\
                              forall (x:X), eqit b1 b2 RR (ITree.bind (kxa x) kab) (kxc x)) \/
    (exists (a : A), eqit b1 b2 eq ma (Ret a) /\ eqit b1 b2 RR (kab a) (Vis e kxc)).
Proof.
  intros. step in H. 
  remember (observe (ITree.bind ma kab)) as tl.
  remember (Vis e kxc) as vis.
  remember (observe vis) as tr. 
  revert ma kab Heqtl kxc e vis Heqvis Heqtr.
  induction H; try solve [intros; subst; discriminate].
  - intros. unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right. exists r. split.
      * step;  rewrite Ema. constructor. auto.
      * step;  unfold observe at 1; unfold _observe. rewrite <- Heqtl.
        simpobs. constructor; auto.
    + left.
      symmetry in Heqtl.

      revert e0 Heqvis. revert k2 REL Heqtr. inv_eq_VisF Heqtl. intros.
      inv Heqvis. 
      cbn in Heqtr. 
      inv_eq_VisF Heqtr.
      exists k. split.
      * step;  rewrite Ema. constructor.  reflexivity.
      * auto.
  - intros. subst.
    unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn: Ema; try discriminate.
    + right; exists r; split.
      * rewrite itree_eta, Ema; reflexivity.
      * step.  unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor; auto.
    + inv Heqtl. specialize (IHeqitF _ _ eq_refl _ _ _ eq_refl eq_refl).
      destruct IHeqitF as [(k0 & ? & ?) | (a & ? & ?)]; [left | right].
      * exists k0. split; auto.
        step; icbn; rewrite Ema; constructor; now step in H0. 
      * exists a. split; auto.
        step; icbn; rewrite Ema; constructor; now step in H0.
Qed.

Lemma eutt_inv_bind_vis:
  forall {A B E X} (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxb : X -> itree E B),
    ITree.bind ma kab ≈ Vis e kxb ->
    (exists (kca : X -> itree E A), (ma ≈ Vis e kca) /\ forall (x:X), (ITree.bind (kca x) kab) ≈ (kxb x)) \/
    (exists (a : A), (ma ≈ Ret a) /\ (kab a ≈ Vis e kxb)).
Proof.
  intros. apply eqit_inv_bind_vis. auto.
Qed.

Lemma eqitree_inv_bind_vis:
  forall {A B E X} (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxb : X -> itree E B),
    ITree.bind ma kab ≅ Vis e kxb ->
    (exists (kca : X -> itree E A), (ma ≅ Vis e kca) /\ forall (x:X), (ITree.bind (kca x) kab) ≅ (kxb x)) \/
    (exists (a : A), (ma ≅ Ret a) /\ (kab a ≅ Vis e kxb)).
Proof.
  intros. apply eqit_inv_bind_vis. auto.
Qed.

Lemma eqit_inv_bind_tau:
  forall {E A B C RR} b1 b2
    (ma : itree E A) (kab : A -> itree E B) (tc: itree E C),
    eqit b1 b2 RR (ITree.bind ma kab) (Tau tc) ->
    (exists (ma' : itree E A), eqit b1 b2 eq ma (Tau ma') /\ eqit b1 b2 RR (ITree.bind ma' kab) tc) \/
    (exists (a : A), eqit b1 b2 eq ma (Ret a) /\ eqit b1 b2 RR (kab a) (Tau tc)).
Proof.
  intros. step in H. 
  remember (observe (ITree.bind ma kab)) as tl.
  remember (Tau tc) as tau.
  remember (observe tau) as tr.
  revert ma kab Heqtl tc tau Heqtau Heqtr.
  induction H; intros; try solve [subst; discriminate].
  - inv Heqtr. unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right; exists r; split.
      * step; icbn; rewrite Ema; constructor; auto.
      * step; icbn; inv H0; unfold observe, _observe; rewrite <- Heqtl; now constructor.
    + left; exists t; split.
      * step; icbn; rewrite Ema; constructor; apply reflexivity.
      * inv Heqtl. inv H0. assumption.
  - subst.
    unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right; exists r; split.
      * step; icbn; rewrite Ema; constructor; auto.
      * step; icbn; unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor 4; auto.
    + inv Heqtl. specialize (IHeqitF _ _ eq_refl _ _ eq_refl eq_refl).
      destruct IHeqitF as [(t0 & ? & ?) | (a & ? & ?)]; [left | right].
      * exists t0. split; auto.
        step; icbn; rewrite Ema; constructor 4; now step in H0.
      * exists a. split; auto.
        step; icbn; rewrite Ema; constructor; now step in H0.
  - inv Heqtr.
    left; exists ma; split.
    + step; constructor; auto. 
    + inv H1; step; assumption.
Qed.

Lemma eutt_inv_bind_tau:
  forall {E A B} (ma : itree E A) (kab : A -> itree E B) (t: itree E B),
    ITree.bind ma kab ≈ Tau t ->
    (exists (ma' : itree E A), ma ≈ Tau ma' /\ ITree.bind ma' kab ≈ t) \/
    (exists (a : A), ma ≈ Ret a /\ kab a ≈ Tau t).
Proof.
  intros. apply eqit_inv_bind_tau. auto.
Qed.

Lemma eqitree_inv_bind_tau:
  forall {E A B} (ma : itree E A) (kab : A -> itree E B) (t: itree E B),
    ITree.bind ma kab ≅ Tau t ->
    (exists (ma' : itree E A), ma ≅ Tau ma' /\ ITree.bind ma' kab ≅ t) \/
    (exists (a : A), ma ≅ Ret a /\ kab a ≅ Tau t).
Proof.
  intros. apply eqit_inv_bind_tau. auto.
Qed.

Lemma eutt_Ret_spin_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} (v: R1),
    eutt RR (Ret v) (@ITree.spin E R2) -> False.
Proof.
  intros.
  step in H.
  remember (observe (Ret v)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.

Lemma eutt_spin_Ret_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} (v: R2),
    eutt RR (@ITree.spin E R1) (Ret v) -> False.
Proof.
  intros.
  step in H.
  remember (observe (Ret v)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.

Lemma eutt_Vis_spin_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} {X} (e: E X) (k: X -> itree E R1),
    eutt RR (Vis e k) (@ITree.spin E R2) -> False.
Proof.
  intros.
  step in H.
  remember (observe (Vis e k)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.

Lemma eutt_spin_Vis_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} {X} (e: E X) (k: X -> itree E R2),
    eutt RR (@ITree.spin E R1) (Vis e k) -> False.
Proof.
  intros.
  step in H.
  remember (observe (Vis e k)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.
Section eqit_elem. 
(*** *** Properties of the chain. *)


(* 
important: proving rewriting of elem under euttge 
--------
goal: establish lemmas of toplevel relations that happen to be instantiations 
of general properties of the corresponding chain. 

1. 
forall (c : Chain (eqit_mon (RR : R1 -> R2 -> Prop) true false )) 
Proper (euttge (@eq R1) ==> euttge (@eq R2) ==> [flip] impl) (elem c)
by subrelation : 
Proper (eq_itree ==> eq_itree ==> [flip] impl) (elem c)

DONE
forall (c : Chain (eqit_mon RR false false)), Equivalence RR -> Equivalence c
(this implies eq_itree is an equivalence relation)

3. 
we want euttge to be a preorder - is this true? 
forall (c : Chain (eqit_mon RR true false)), Preorder RR -> Preorder c

can we generalize to be heterogeneous for an RR that relates R1, R2? 

next q: 
weak bisim: 

4. DONE 
forall (c : Chain (eqit_mon RR true true)), Refl RR -> Refl c 
5. DONE 
forall (c : Chain (eqit_mon RR true true)), Sym RR -> Sym c 
(* do not attempt: *)
forall (c : Chain (eqit_mon RR true true)), Trans RR -> Trans c 

but at the gfp, it is true. 
(* this is true: *)
(* Equiv RR -> Equiv eutt RR *)

next big piece is how it all interacts w bind. 

we should be able to prove this: 

forall X1 X2 Y1 Y2, 
eutt (RR : X1 -> X2 -> Prop) u v -> (forall x1 x2, RR x1 x2 -> eutt SS (k x1) (g x2)
-> eutt SS (bind u k) (bind v g)

but this should be a particular case of a more gen lemma: under context reasoning
(here bind is the context)

back to bind: 
[DONE, SORT OF]6. 
forall (c : Chain (eqit_mon SS b1 b2)) RR, 
Proper (eutt RR ==> (fun k g => (forall x y, RR x y -> c (k x) (g y))) ==> c) 
bind 

could be interesting: 
chain_mono: 

RR1 <= RR2, b1 <= b1', ... 
(Chain eqit_mon RR b1 b2) <=
(Chain eqit_mon RR' b1' b2') 
)

*)

(* Conjecture chain_mono RR1 RR2 b1 b2 b1' b2' : 
(* we know from JOACHIM PARROW AND TJARK WEBER 2016 that the 
companion is monotone.  *)
... 
(Chain eqit_mon RR b1 b2) <=
(Chain eqit_mon RR' b1' b2') .  *)

Context {E : Type -> Type} {R1 R2} {RR : R1 -> R2 -> Prop} {b1 b2 : bool}.

Ltac euttsimpl := unfold eutt, euttge, eq_itree, eqit in *. 

(* we really need euttge trans *)

Lemma Equivalence_elem_ff R RS (c : Chain (@eqit_mon E false false)) :
Equivalence RS -> Equivalence (elem c R R RS).
Proof.
  constructor; typeclasses eauto.
Qed.

Lemma Reflexive_elem_eutt R RS (c : Chain (@eqit_mon E true true)) :
      Reflexive RS -> Reflexive (elem c R R RS).
Proof. typeclasses eauto. Qed.

Lemma Symmetric_elem_eutt R RS (c : Chain (@eqit_mon E true true)) :
      Symmetric RS -> Symmetric (elem c R R RS).
Proof. typeclasses eauto. Qed.

(* modified: eutt RX u v -> eqit RX b1 b2 u v. otherwise you get stuck
when you need to know something about b1/b2. *)
Lemma Proper_elem_bind X1 X2 Y1 Y2 RX SS u v k g 
  (c : Chain (eqit_mon b1 b2)) : 
  eqit b1 b2 RX u v -> (forall x1 x2, RX x1 x2 -> elem c _ _ SS (k x1) (g x2)) -> 
  elem c _ _ SS (@ITree.bind E X1 Y1 u k) (@ITree.bind E X2 Y2 v g).
Proof.
  revert u v. 
  tower induction. intros. icbn.  
  rewrite 2observe_bind.  
  step in H0. induction H0; simpobs.
  - now apply H1. 
  - constructor. eapply H; eauto. intros.
   (* `step` tactic fails here as there are 2 chains *)
    now apply (b_chain x), H1. 
  - constructor. intro. eapply H; eauto. intros.
    now apply (b_chain x), H1. 
   (* note: we cannot prove these cases for a generic b1 b2 in the chain *)
  - taul. rewrite observe_bind. eapply IHeqitF; eauto. 
  - taur. rewrite observe_bind. eapply IHeqitF; eauto. 
Qed. 


(* We can't state this nicely as a Proper relation, since proper instances
need to have subcomponents that share types. eutt RX violates this, as 
u and v are of different types. *)

End eqit_elem. 

Section eutt_facts. 

(** * Equivalence up to taus *)

(** Abbreviated as [eutt]. *)

(** We consider [Tau] as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many [Tau]s between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. This ensures that equivalence
   up to taus is transitive (and in fact an equivalence relation).
 *)

(** A rewrite hint database named [itree] is available via the tactic
    [autorewrite with itree] as a custom simplifier of expressions using
    mainly [Ret], [Tau], [Vis], [ITree.bind] and [ITree.Interp.Interp.interp].
 *)

(** This file contains only the definition of the [eutt] relation.
    Theorems about [eutt] are split in two more modules:

    - [ITree.Eq.UpToTausCore] proves that [eutt] is reflexive, symmetric,
      and that [ITree.Eq.Eqit.eq_itree] is a subrelation of [eutt].
      Equations for [ITree.Core.ITreeDefinition] combinators which only rely on
      those properties can also be found here.

    - [ITree.Eq.UpToTausEquivalence] proves that [eutt] is transitive,
      and, more generally, contains theorems for up-to reasoning in
      coinductive proofs.
 *)


#[global]
Instance eutt_cong_eutt {E R1 R2 RR}:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (@eqit E true true R1 R2 RR).
Proof.
  intros!. now rewrite H, H0.
Qed.

#[global]
Instance eutt_cong_euttge {E R1 R2 RR}:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (@eqit E true true R1 R2 RR).
Proof.
  intros!. now rewrite H, H0.
Qed.

#[global]
Instance eutt_cong_eq {E R1 R2 RR}:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E true true R1 R2 RR).
Proof.
  intros!. now rewrite H, H0.
Qed.

#[global]
Instance eutt_cong_eutt' {E R1 R2 RR} :
  Proper (eutt eq ==> eutt eq ==> flip impl) (@eutt E R1 R2 RR).
Proof.
  apply eutt_cong_eutt.
Qed.

(* Specialization of [eutt_clo_bind] to the recurrent case where [UU := eq]
   in order to avoid having to provide the relation manually everytime *)
Lemma eutt_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, eutt RR (k1 u) (k2 u)) -> eutt RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

(* Further specialization for [RR := eq] *)
Lemma eutt_eq_bind' {E U R} (t1 t2: itree E U) (k1 k2: U -> itree E R):
  t1 ≈ t2 ->
  (forall u, (k1 u) ≈ (k2 u)) ->
  (ITree.bind t1 k1) ≈ (ITree.bind t2 k2).
Proof.
  intros -> Hk. now apply eutt_eq_bind.
Qed.

(* Exposing a version specialized to [eutt] so that users don't have to know about [eqit] *)
Lemma eutt_Ret :
  forall E (R1 R2 : Type) (RR : R1 -> R2 -> Prop) r1 r2, RR r1 r2 <-> eutt (E := E) RR (Ret r1) (Ret r2).
Proof.
  intros; apply eqit_Ret.
Qed.

(* [eutt] can be thought as the elementary block of a relational program logic.
   The following few lemmas give elementary logical rules to compose proofs.
 *)
Lemma eutt_conj {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS  t s ->
    eutt RS' t s ->
    eutt (cup RS RS') t s. 
Proof.
  repeat red.
  icoinduction c cih. intros * EQ EQ'.
  step in EQ; step in EQ'. 
  genobs t ot; genobs s os.
  hinduction EQ before cih; subst; intros; simpl.
  - now inv EQ'; constructor; constructor.
  - taus. eapply cih; eauto. apply eqit_inv_Tau. now step.  
  - constructor. intro v. specialize (REL v).
    eapply cih; eauto. 
    now eapply eqitF_inv_VisF in EQ'; eauto.
  - taul. eapply IHEQ; eauto. subst. unstep. eapply eqit_inv_Tau_l. 
    now step.  
  - taur. eapply IHEQ; eauto. subst. unstep. eapply eqit_inv_Tau_r. 
    now step.  
Qed.

Lemma eutt_disj_l {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS t s ->
    eutt (cup RS RS') t s. 
Proof.
  intros.
  eapply (eqit_mono RS _); eauto.
Qed.

Lemma eutt_disj_r {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS' t s ->
    eutt (cup RS RS') t s. 
Proof.
  intros.
  eapply (eqit_mono RS' _); eauto.
Qed.

Lemma eutt_equiv {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    (HeterogeneousRelations.eq_rel RS RS') ->
    eutt RS t s <-> eutt RS' t s. 
Proof.
  intros * EQ; split; intros EUTT; eapply eqit_mono; try apply EUTT; eauto.
  all:apply EQ.
Qed.

(* Rewriting equivalent simulation relations under [eq_itree] and [eutt] *)
#[global]
Instance eq_itree_Proper_R_Het {E : Type -> Type} {R1 R2:Type}
  : Proper ((@HeterogeneousRelations.eq_rel R1 R2) ==> Logic.eq ==> Logic.eq ==> iff) (@eq_itree E R1 R2).
Proof.
  repeat intro; subst.
  unfold eq_itree; rewrite H; reflexivity.
Qed.

#[global]
Instance eutt_Proper_R_Het {E : Type -> Type} {R1 R2:Type}
  : Proper  ((@HeterogeneousRelations.eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eutt E R1 R2).
Proof.
  repeat intro; subst.
  unfold eutt; rewrite H; reflexivity.
Qed.

(* Stronger subrelation result which applies for [eutt RR t t]. This is
   relevant for post-conditions *)
Lemma eutt_sub_self {E R} (R1 R2: R -> R -> Prop) (t: itree E R):
  (forall r, R1 r r -> R2 r r) ->
  eutt R1 t t ->
  eutt R2 t t.
Proof.
  intros Hrel; revert t. icoinduction c cih; intros t Heutt.
  step in Heutt.
  remember t as t' in Heutt at 2. assert (Ht': t' ≈ t) by now subst. clear Heqt'.
  rewrite (itree_eta t), (itree_eta t') in Ht'.
  revert Ht'. induction Heutt; clear t; intros Heq.
  - apply eutt_inv_Ret in Heq; subst.
    constructor; auto.
  - apply eqit_inv_Tau in Heq.
    constructor. eapply cih. 
    now rewrite <- Heq at 2.
  - constructor. intros v. eapply eqit_inv_Vis in Heq.
    specialize (REL v). eapply cih. now rewrite <- Heq at 2.
  - taul. taur. apply IHHeutt. rewrite <- (itree_eta t1).   
    now rewrite tau_euttge in Heq. 
  - apply IHHeutt. rewrite <- (itree_eta).   
    now rewrite tau_euttge in Heq. 
Qed.

End eutt_facts. 
