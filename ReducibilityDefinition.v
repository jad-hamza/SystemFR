Require Import Relations.
Require Import Psatz.
Require Import Coq.Strings.String.

Require Export SystemFR.ReducibilityMeasure.
Require Export SystemFR.ReducibilityCandidate.
Require Export SystemFR.Equivalence.

Require Import Equations.Equations.
Require Import Coq.Classes.RelationClasses.
Require Import Equations.Prop.Subterm.
Require Import Coq.Arith.PeanoNat.

Definition reduces_to (R: tree -> tree -> Prop) (t1 t2: tree) :=
  closed_term t1 /\
  closed_term t2 /\
  exists v1 v2, R v1 v2 /\ star scbv_step t1 v1 /\ star scbv_step t2 v2.

Lemma reduces_to_equiv:
  forall (R R': tree -> tree -> Prop) t1 t2,
    reduces_to R t1 t2 ->
    (forall v1 v2, R v1 v2 -> R' v1 v2) ->
    reduces_to R' t1 t2.
Proof.
  unfold reduces_to; repeat step; eauto 6.
Qed.

Reserved Notation "'[' ρ ⊨ t ':' T ']'"  (ρ at level 60, t at level 60).

Reserved Notation "'[' ρ ⊨ t1 '≡' t2 ':' T ']'" (ρ at level 60, t1 at level 60, t2 at level 60).

Reserved Notation "'[' ρ '⊨' v ':' T ']v'" (ρ at level 60, v at level 60).

Reserved Notation "'[' ρ '⊨' v1 '≡' v2 ':' T ']v'"
  (ρ at level 60, v1 at level 60, v2 at level 60).

Equations reducible_values (ρ: interpretation) (v1 v2: tree) (T: tree): Prop
    by wf (get_measure T) lt_measure := {
  reducible_values ρ v1 v2 (fvar X type_var) :=
    match lookup Nat.eq_dec ρ X with
    | None => False
    | Some R => R v1 v2
    end;

  reducible_values ρ v1 v2 T_unit := v1 = uu /\ v2 = uu;

  reducible_values ρ v1 v2 T_bool :=
    (v1 = ttrue /\ v2 = ttrue) \/
    (v1 = tfalse /\ v2 = tfalse);

  reducible_values ρ v1 v2 T_nat :=
    is_nat_value v1 /\ v1 = v2;

  reducible_values ρ v1 v2 (T_abs T) :=
    closed_value v1 /\
    closed_value v2 /\
    exists X,
      ~(X ∈ support ρ) /\
      ~(X ∈ pfv T type_var) /\
      forall RC,
        reducibility_candidate RC ->
        [ (X,RC) :: ρ ⊨ v1 ≡ v2 : topen 0 T (fvar X type_var) ]v;

  reducible_values ρ v1 v2 (T_arrow A B) :=
    exists (_: is_erased_type B),
    exists t1 t2,
      v1 = notype_lambda t1 /\
      v2 = notype_lambda t2 /\
      closed_value v1 /\
      closed_value v2 /\
      forall a1 a2 (p1: closed_term a1),
        [ ρ ⊨ a1 ≡ a2 : A ]v ->
        [ ρ ⊨ open 0 t1 a1 ≡ open 0 t2 a2 : open 0 B a1 ]
  ;

  reducible_values ρ v1 v2 (T_prod A B) :=
    exists (_: is_erased_type B),
    closed_value v1 /\
    closed_value v2 /\
    exists a1 a2 b1 b2 (_: closed_term a1),
      v1 = pp a1 b1 /\
      v2 = pp a2 b2 /\
      [ ρ ⊨ a1 ≡ a2 : A ]v /\
      [ ρ ⊨ b1 ≡ b2 : open 0 B a1 ]v;

  reducible_values ρ v1 v2 (T_sum A B) :=
    closed_value v1 /\
    closed_value v2 /\
    (
      (exists v1' v2', v1 = tleft v1'  /\ v2 = tleft v2'  /\ [ ρ ⊨ v1' ≡ v2' : A ]v) \/
      (exists v1' v2', v1 = tright v1' /\ v2 = tright v2' /\ [ ρ ⊨ v1' ≡ v2' : B ]v)
    );

  reducible_values ρ v1 v2 (T_refine T p) :=
    closed_value v1 /\
    closed_value v2 /\
    [ ρ ⊨ v1 ≡ v2 : T ]v /\
    is_erased_term p /\
    wf p 1 /\
    pfv p term_var = nil /\
    star scbv_step (open 0 p v1) ttrue /\
    star scbv_step (open 0 p v2) ttrue;

  reducible_values ρ v1 v2 (T_type_refine A B) :=
    exists (_: is_erased_type B),
    exists (_: closed_value v1),
    exists (_: closed_value v2),
      [ ρ ⊨ v1 ≡ v2 : A ]v /\
      exists p1 p2,
        [ ρ ⊨ p1 ≡ p2 : open 0 B v1 ]v;

  reducible_values ρ v1 v2 (T_intersection A B) :=
    closed_value v1 /\
    closed_value v2 /\
      [ ρ ⊨ v1 ≡ v2 : A ]v /\
      [ ρ ⊨ v1 ≡ v2 : B ]v;

  reducible_values ρ v1 v2 (T_union A B) :=
    closed_value v1 /\
    closed_value v2 /\
    clos_trans_1n _ (fun v1' v2' =>
      [ ρ ⊨ v1' ≡ v2' : A ]v \/
      [ ρ ⊨ v1' ≡ v2' : B ]v
    ) v1 v2;

  reducible_values ρ v1 v2 T_top := closed_value v1 /\ closed_value v2;

  reducible_values ρ v1 v2 T_bot := False;

  reducible_values ρ v1 v2 (T_equiv t1 t2) :=
    v1 = uu /\ v2 = uu /\
    [ t1 ≡ t2 ];

  reducible_values ρ v1 v2 (T_forall A B) :=
    exists (_: is_erased_type B),
    closed_value v1 /\
    closed_value v2 /\
    forall a1 a2 (p1: closed_term a1),
      [ ρ ⊨ a1 ≡ a2 : A ]v ->
      [ ρ ⊨ v1 ≡ v2 : open 0 B a1 ]v;

  reducible_values ρ v1 v2 (T_exists A B) :=
    exists (_: is_erased_type B),
    closed_value v1 /\
    closed_value v2 /\
    clos_trans_1n _ (fun v1' v2' => exists a1 a2 (_: closed_term a1),
      [ ρ ⊨ a1 ≡ a2 : A ]v /\
      [ ρ ⊨ v1' ≡ v2' : open 0 B a1 ]v
    ) v1 v2;

  reducible_values ρ v1 v2 (T_rec n T0 Ts) :=
    closed_value v1 /\
    closed_value v2 /\
    is_erased_term n /\ (
      (star scbv_step n zero /\ [ ρ ⊨ v1 ≡ v2 : T0 ]v) \/
      (exists n' X (p1: is_nat_value n') (p2: star scbv_step n (succ n')),
         ~(X ∈ pfv T0 type_var) /\
         ~(X ∈ pfv Ts type_var) /\
         ~(X ∈ support ρ) /\
         [ (X, fun v1 v2 => reducible_values ρ v1 v2 (T_rec n' T0 Ts)) :: ρ ⊨
              v1 ≡ v2 : topen 0 Ts (fvar X type_var) ]v
      )
    );

  reducible_values _ _ _ _ := False
}
  where "'[' ρ '⊨' v1 '≡' v2 ':' T ']v'" :=
    (reducible_values ρ v1 v2 T)
  where "'[' ρ '⊨' t1 '≡' t2 ':' T ']'" :=
    (reduces_to (fun v1 v2 => reducible_values ρ v1 v2 T) t1 t2)
  where "'[' ρ '⊨' v ':' T ']v'" :=
    (reducible_values ρ v v T)
  where "'[' ρ '⊨' t ':' T ']'" :=
    (reduces_to (fun v1 v2 => reducible_values ρ v1 v2 T) t t).

Hint Transparent lt_measure: core.

Ltac reducibility_definition :=
  repeat step || autorewrite with bsize || unfold "<<", get_measure, closed_value, closed_term in *;
    try solve [ apply right_lex, right_lex, lt_index_step; steps ];
    try solve [ apply right_lex, lt_index_step; steps ];
    try solve [ apply leq_lt_measure; lia ];
    try solve [ apply left_lex; lia ].

Solve Obligations with reducibility_definition.

Fail Next Obligation. (* no more obligations for reducible_values *)

(* see https://github.com/coq/coq/issues/3814 *)
Instance: subrelation eq Basics.impl.
Proof.
  steps.
Qed.

Instance: subrelation eq (Basics.flip Basics.impl).
Proof.
  steps.
Qed.

Ltac simp_red_hyp :=
  match goal with
  | H: _ |- _ => rewrite_strat outermost hints reducible_values in H
  end.

Ltac simp_red_top_level_hyp :=
  match goal with
  | H: _ |- _ => rewrite_strat hints reducible_values in H
  end.

Ltac simp_red_goal := rewrite_strat outermost hints reducible_values.

Ltac simp_red := simp_red_hyp || simp_red_goal.

Ltac simp_red_nat :=
  match goal with
  | H: reducible_values _ _ T_nat |- _ => simp reducible_values in H
  end.
