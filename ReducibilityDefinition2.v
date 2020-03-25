Require Import Coq.Strings.String.

Require Export SystemFR.TermList.
Require Export SystemFR.ReducibilityMeasure.
Require Export SystemFR.ReducibilityCandidate2.

Require Import Equations.Equations.
Require Import Coq.Classes.RelationClasses.
Require Import Equations.Prop.Subterm.

Require Import Omega.

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

Equations reducible_values (theta: interpretation2) (v1 v2: tree) (T: tree): Prop
    by wf (get_measure T) lt_measure :=
  reducible_values theta v1 v2 (fvar X type_var) :=
    match lookup Nat.eq_dec theta X with
    | None => False
    | Some R => R v1 v2
    end;

  reducible_values theta v1 v2 T_unit := v1 = uu /\ v2 = uu;

  reducible_values theta v1 v2 T_bool :=
    (v1 = ttrue /\ v1 = ttrue) \/
    (v1 = tfalse /\ v2 = tfalse);

  reducible_values theta v1 v2 T_nat :=
    is_nat_value v1 /\ is_nat_value v2 /\ v1 = v2;

  reducible_values theta v1 v2 (T_abs T) :=
    closed_value v1 /\
    closed_value v2 /\
    exists X,
      ~(X ∈ support theta) /\
      ~(X ∈ pfv T type_var) /\
      forall RC,
        reducibility_candidate2 RC ->
        reducible_values ((X,RC) :: theta) v1 v2 (topen 0 T (fvar X type_var));

  reducible_values theta v1 v2 (T_arrow A B) :=
    exists (_: is_erased_type B),
    exists t1 t2,
      v1 = notype_lambda t1 /\
      v2 = notype_lambda t2 /\
      closed_value v1 /\
      closed_value v2 /\
      forall a1 a2 (p1: is_erased_term a1) (p2: is_erased_term a2),
        wf a1 0 ->
        pfv a1 term_var = nil ->
        wf a2 0 ->
        pfv a2 term_var = nil ->
        reducible_values theta a1 a2 A ->
        reduces_to (fun v1 v2 => reducible_values theta v1 v2 (open 0 B a1))
          (open 0 t1 a1)
          (open 0 t2 a1)
  ;

  reducible_values theta v1 v2 (T_prod A B) :=
    exists (_: is_erased_type B),
    closed_value v1 /\
    closed_value v1 /\
    exists a1 a2 b1 b2 (_: is_erased_term a1) (_: is_erased_term a2),
      wf a1 0 /\
      pfv a1 term_var = nil /\
      wf a2 0 /\
      pfv a2 term_var = nil /\
      v1 = pp a1 b1 /\
      v2 = pp a2 b2 /\
      reducible_values theta a1 a2 A /\
      reducible_values theta b1 b2 (open 0 B a1);

  reducible_values theta v1 v2 (T_sum A B) :=
    closed_value v1 /\
    closed_value v2 /\
    (
      (exists v1' v2', v1 = tleft v1'  /\ v2 = tleft v2'  /\ reducible_values theta v1' v2' A) \/
      (exists v1' v2', v1 = tright v1' /\ v2 = tright v2' /\ reducible_values theta v1' v2' B)
    );

  reducible_values theta v1 v2 (T_refine T p) :=
    closed_value v1 /\
    reducible_values theta v1 v2 T /\
    is_erased_term p /\
    wf p 1 /\
    pfv p term_var = nil /\
    star scbv_step (open 0 p v1) ttrue /\
    star scbv_step (open 0 p v2) ttrue;

  reducible_values theta v1 v2 (T_type_refine A B) :=
    exists (_: is_erased_type B),
    exists (_: closed_value v1),
    exists (_: closed_value v2),
      reducible_values theta v1 v2 A /\
      exists p1 p2, reducible_values theta p1 p2 (open 0 B v1);

  reducible_values theta v1 v2 (T_intersection A B) :=
    closed_value v1 /\
    closed_value v2 /\
    reducible_values theta v1 v2 A /\
    reducible_values theta v1 v2 B;

  reducible_values theta v1 v2 (T_union A B) :=
    closed_value v1 /\
    closed_value v2 /\
    (
      reducible_values theta v1 v2 A \/
      reducible_values theta v1 v2 B
    );

  reducible_values theta v1 v2 T_top := closed_value v1 /\ closed_value v2;

  reducible_values theta v1 v2 T_bot := False;

  reducible_values theta v1 v2 (T_equiv t1 t2) :=
    v1 = uu /\ v2 = uu /\
    equivalent_terms t1 t2;

  reducible_values theta v1 v2 (T_forall A B) :=
    exists (_: is_erased_type B),
    closed_value v1 /\
    closed_value v2 /\
    forall a1 a2 (p1: is_erased_term a1) (p2: is_erased_term a2),
      wf a1 0 ->
      pfv a1 term_var = nil ->
      wf a2 0 ->
      pfv a2 term_var = nil ->
      reducible_values theta a1 a2 A ->
      reducible_values theta v1 v2 (open 0 B a1);

  reducible_values theta v1 v2 (T_exists A B) :=
    exists (_: is_erased_type B),
    closed_value v1 /\
    closed_value v2 /\
    exists a1 a2 (_: is_erased_term a1) (_: is_erased_term a2),
      wf a1 0 /\
      pfv a1 term_var = nil /\
      wf a2 0 /\
      pfv a2 term_var = nil /\
      reducible_values theta a1 a2 A /\
      reducible_values theta v1 v2 (open 0 B a1);

  reducible_values theta v1 v2 (T_rec n T0 Ts) :=
    closed_value v1 /\
    closed_value v2 /\
    is_erased_term n /\ (
      (star scbv_step n zero /\ reducible_values theta v1 v2 T0) \/
      (exists n' X (p1: is_nat_value n') (p2: star scbv_step n (succ n')),
         ~(X ∈ pfv T0 type_var) /\
         ~(X ∈ pfv Ts type_var) /\
         ~(X ∈ support theta) /\
         reducible_values ((X, fun v1 v2 => reducible_values theta v1 v2 (T_rec n' T0 Ts)) :: theta)
                          v1 v2
                          (topen 0 Ts (fvar X type_var))
      )
    );

  reducible_values theta v1 v2 T := False
.

Hint Transparent lt_measure: core.

Ltac reducibility_definition :=
  repeat step || autorewrite with bsize || unfold "<<", get_measure, closed_value, closed_term in *;
    try solve [ apply right_lex, right_lex, lt_index_step; steps ];
    try solve [ apply right_lex, lt_index_step; steps ];
    try solve [ apply leq_lt_measure; omega ];
    try solve [ apply left_lex; omega ].

Solve Obligations with reducibility_definition.

Fail Next Obligation. (* no more obligations for reducible_values *)

Definition reducible2 (theta: interpretation2) t1 t2 T : Prop :=
  reduces_to (fun v1 v2 => reducible_values theta v1 v2 T) t1 t2.

Definition weak_subtype theta T1 T2 :=
  forall v, reducible_values theta v T1 -> reducible_values theta v T2.

Definition strong_subtype theta T1 T2 :=
  forall v, reducible_values theta v T1 -> reducible_values theta v T2.

Definition open_reducible (tvars: tvar_list) (gamma: context) t T : Prop :=
  forall theta lterms,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma lterms  ->
    support theta = tvars ->
    reducible theta
              (substitute t lterms)
              (substitute T lterms).

Definition open_subtype (tvars: tvar_list) (gamma: context) T1 T2 : Prop :=
  forall theta l,
   valid_interpretation theta ->
   satisfies (reducible_values theta) gamma l ->
   support theta = tvars ->
   subtype theta (substitute T1 l) (substitute T2 l).

Definition open_equivalent (tvars: tvar_list) (gamma: context) t1 t2 : Prop :=
  forall theta l,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    support theta = tvars ->
    equivalent_terms (substitute t1 l) (substitute t2 l).

Notation "'[' tvars ';' gamma '⊨' t ':' T ']'" := (open_reducible tvars gamma t T)
  (at level 50, t at level 50).

Notation "'[' tvars ';' gamma '⊨' T1 '<:' T2 ']'" := (open_subtype tvars gamma T1 T2)
  (at level 50, T1 at level 50).

Notation "'[' tvars ';' gamma '⊨' t1 '≡' t2 ']'" := (open_equivalent tvars gamma t1 t2)
  (at level 50, t1 at level 50).

Lemma reducibility_rewrite:
  forall theta t T,
    reduces_to (fun t => reducible_values theta t T) t =
    reducible theta t T.
Proof.
  reflexivity.
Qed.

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
