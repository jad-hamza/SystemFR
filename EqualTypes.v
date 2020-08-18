Require Import PeanoNat.
Require Import Relations.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.ReducibilityRenaming.
Require Export SystemFR.EquivalentWithRelation.

Opaque makeFresh.

Arguments PER { A }.
Arguments symmetric { A }.
Arguments transitive { A }.
Arguments same_relation { A }.

Reserved Notation "[ ρ ⊨ T1 '=' T2 ]"
  (ρ at level 60, T1 at level 60, T2 at level 60).
Reserved Notation "[ ρ ⊨ T1 '=' T2 | A ]"
  (ρ at level 60, T1 at level 60, T2 at level 60, A at level 60).

Inductive equal_types: interpretation -> tree -> tree -> Prop :=
| ETVar: forall ρ X Y R1 R2,
    lookup Nat.eq_dec ρ X = Some R1 ->
    lookup Nat.eq_dec ρ Y = Some R2 ->
    same_relation R1 R2 ->
    [ ρ ⊨ fvar X type_var = fvar Y type_var ]

| ETUnit: forall ρ,
    [ ρ ⊨ T_unit = T_unit ]

| ETBool: forall ρ,
    [ ρ ⊨ T_bool = T_bool ]

| ETNat: forall ρ,
    [ ρ ⊨ T_nat = T_nat ]

| ETTop: forall ρ,
    [ ρ ⊨ T_top = T_top ]

| ETBot: forall ρ,
    [ ρ ⊨ T_bot = T_bot ]

| ETAbs: forall ρ T1 T2 X,
    ~ X ∈ support ρ ->
    ~ X ∈ pfv T1 type_var ->
    ~ X ∈ pfv T2 type_var ->
    (forall RC, [ (X, RC) :: ρ ⊨ topen 0 T1 (fvar X type_var) = topen 0 T2 (fvar X type_var) ]) ->
    [ ρ ⊨ T_abs T1 = T_abs T2 ]

| ETArrow: forall ρ A1 B1 A2 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    [ ρ ⊨ A1 = A2 ] ->
    [ ρ ⊨ B1 = B2 | A1 ] ->
    [ ρ ⊨ T_arrow A1 B1 = T_arrow A2 B2 ]

| ETProd: forall ρ A1 B1 A2 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    [ ρ ⊨ A1 = A2 ] ->
    [ ρ ⊨ B1 = B2 | A1 ] ->
    [ ρ ⊨ T_prod A1 B1 = T_prod A2 B2 ]

| ETSum: forall ρ A1 B1 A2 B2,
    [ ρ ⊨ A1 = A2 ] ->
    [ ρ ⊨ B1 = B2 ] ->
    [ ρ ⊨ T_sum A1 B1 = T_sum A2 B2 ]

| ETIntersection: forall ρ A1 B1 A2 B2,
    [ ρ ⊨ A1 = A2 ] ->
    [ ρ ⊨ B1 = B2 ] ->
    [ ρ ⊨ T_intersection A1 B1 = T_intersection A2 B2 ]

| ETUnion: forall ρ A1 B1 A2 B2,
    [ ρ ⊨ A1 = A2 ] ->
    [ ρ ⊨ B1 = B2 ] ->
    [ ρ ⊨ T_union A1 B1 = T_union A2 B2 ]

| ETRefine: forall ρ A1 A2 p1 p2,
    is_erased_term p1 ->
    wf p1 1 ->
    pfv p1 term_var = nil ->
    is_erased_term p2 ->
    wf p2 1 ->
    pfv p2 term_var = nil ->
    (forall v1 v2, [ ρ ⊨ v1 ≡ v2 : A1 ]v -> [ open 0 p1 v1 ≡ open 0 p2 v2 ]) ->
    [ ρ ⊨ A1 = A2 ] ->
    [ ρ ⊨ T_refine A1 p1 = T_refine A2 p2 ]

| ETTypeRefine: forall ρ A1 A2 B1 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    [ ρ ⊨ A1 = A2 ] ->
    [ ρ ⊨ B1 = B2 | A1 ] ->
    [ ρ ⊨ T_type_refine A1 B1 = T_type_refine A2 B2 ]

where
  "[ ρ ⊨ A = B ]" := (equal_types ρ A B) and
  "[ ρ ⊨ A = B | C ]" := (
    forall v1 v2,
      [ ρ ⊨ v1 ≡ v2 : C ]v ->
      equal_types ρ (open 0 A v1) (open 0 B v2)
    ).

Definition PER_type_values ρ T := PER (fun v1 v2 => [ ρ ⊨ v1 ≡ v2 : T ]v).
Definition PER_type_expr ρ T   := PER (fun v1 v2 => [ ρ ⊨ v1 ≡ v2 : T ]).

Definition good_types ρ T1 T2 : Prop :=
  PER_type_values ρ T1 /\
  PER_type_values ρ T2 /\
  [ ρ ⊨ T1 =:= T2 ].

Lemma reducibility_candidate_PER_var:
  forall ρ X R,
    reducibility_candidate R ->
    PER (fun v1 v2 : tree => [(X, R) :: ρ ⊨ v1 ≡ v2 : fvar X type_var ]v).
Proof.
  unfold reducibility_candidate;
    repeat step || constructor || unfold symmetric, transitive || simp_red;
    eauto with PER.
Qed.

Lemma same_relation_PER:
  forall A (R1 R2: relation A),
    PER R1 ->
    same_relation R1 R2 ->
    PER R2.
Proof.
  unfold same_relation, inclusion; repeat step || constructor || unfold symmetric, transitive.
  - apply_any; eauto with PER.
  - apply_any. eapply PER_trans; eauto.
Qed.

Lemma same_relation_weaken:
  forall ρ X Y R,
    X <> Y ->
    same_relation
      (fun v1 v2 => [ ρ ⊨ v1 ≡ v2 : fvar X type_var ]v)
      (fun v1 v2 => [ (Y, R) :: ρ ⊨ v1 ≡ v2 : fvar X type_var ]v).
Proof.
  unfold same_relation, inclusion;
    repeat step || simp_red.
Qed.

Lemma in_valid_interpretation_per2: forall ρ X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  PER_type_values ρ (fvar X type_var).
Proof.
  unfold PER_type_values; induction ρ; steps;
    eauto using reducibility_candidate_PER_var;
    eauto using same_relation_PER, same_relation_weaken.
Qed.

Lemma good_types_fvar:
  forall ρ X Y R1 R2,
    lookup Nat.eq_dec ρ X = Some R1 ->
    lookup Nat.eq_dec ρ Y = Some R2 ->
    valid_interpretation ρ ->
    same_relation R1 R2 ->
    good_types ρ (fvar X type_var) (fvar Y type_var).
Proof.
  unfold good_types; steps;
    eauto using in_valid_interpretation_per2.

  unfold equivalent_types; repeat step || simp_red;
    eauto with same_relation_left;
    eauto with same_relation_right.
Qed.

Lemma PER_unit:
  forall ρ, PER_type_values ρ T_unit.
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red.
Qed.

Lemma PER_bool:
  forall ρ, PER_type_values ρ T_bool.
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red.
Qed.

Lemma PER_nat:
  forall ρ, PER_type_values ρ T_nat.
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red.
Qed.

Lemma PER_top:
  forall ρ, PER_type_values ρ T_top.
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red.
Qed.

Lemma PER_bot:
  forall ρ, PER_type_values ρ T_bot.
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red.
Qed.

Lemma good_types_unit:
  forall ρ, good_types ρ T_unit T_unit.
Proof.
  unfold good_types; steps;
    eauto using equivalent_types_refl;
    eauto using PER_unit.
Qed.

Lemma good_types_bool:
  forall ρ, good_types ρ T_bool T_bool.
Proof.
  unfold good_types; steps;
    eauto using equivalent_types_refl;
    eauto using PER_bool.
Qed.

Lemma good_types_nat:
  forall ρ, good_types ρ T_nat T_nat.
Proof.
  unfold good_types; steps;
    eauto using equivalent_types_refl;
    eauto using PER_nat.
Qed.

Lemma good_types_top:
  forall ρ, good_types ρ T_top T_top.
Proof.
  unfold good_types; steps;
    eauto using equivalent_types_refl;
    eauto using PER_top.
Qed.

Lemma good_types_bot:
  forall ρ, good_types ρ T_bot T_bot.
Proof.
  unfold good_types; steps;
    eauto using equivalent_types_refl;
    eauto using PER_bot.
Qed.

Lemma PER_abs:
  forall ρ X T,
    ~ X ∈ support ρ ->
    ~ X ∈ pfv T type_var ->
    valid_interpretation ρ ->
    (forall RC,
      reducibility_candidate RC ->
      PER_type_values ((X, RC) :: ρ) (topen 0 T (fvar X type_var))) ->
    PER_type_values ρ (T_abs T).
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red || exists X || instantiate_any.
  - unshelve eapply (PER_sym _ _ x y _ H12); steps;
      eauto using reducible_values_rename_one.
  - unshelve eapply (PER_trans _ _ x y z _ _ H18); steps;
      eauto using reducible_values_rename_one.
Qed.

Lemma good_types_abs:
  forall ρ T1 T2 X,
    ~ X ∈ support ρ ->
    ~ X ∈ pfv T1 type_var ->
    ~ X ∈ pfv T2 type_var ->
    (forall RC,
      valid_interpretation ((X, RC) :: ρ) ->
      good_types ((X, RC) :: ρ) (topen 0 T1 (fvar X type_var)) (topen 0 T2 (fvar X type_var))) ->
    valid_interpretation ρ ->
    good_types ρ (T_abs T1) (T_abs T2).
Proof.
  unfold good_types; steps;
    eauto using PER_abs with apply_any.

  unfold equivalent_types; repeat step || simp_red || exists X || instantiate_any.
  - apply_any; steps; eauto using reducible_values_rename_one.
  - apply_any; steps; eauto using reducible_values_rename_one.
Qed.

Ltac Build_PER :=
  match goal with
  | |- PER _ => apply Build_PER; unfold symmetric, transitive
  | |- PER_type_values _ _ => apply Build_PER; unfold symmetric, transitive
  | |- PER_type_expr _ _ => apply Build_PER; unfold symmetric, transitive
  end.

Lemma PER_values_sym:
  forall ρ T v1 v2,
    PER_type_values ρ T ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v1 : T ]v.
Proof.
  intros; unshelve eapply (PER_sym _ _ v1 v2 _ H); steps.
Qed.

Lemma PER_values_refl_left:
  forall ρ T v1 v2,
    PER_type_values ρ T ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v1 : T ]v.
Proof.
  intros; eapply (PER_refl_left tree (fun v1 v2 => [ ρ ⊨ v1 ≡ v2 : T ]v) v1 v2);
    steps; eauto with eapply_any.
Qed.

Lemma PER_values_refl_right:
  forall ρ T v1 v2,
    PER_type_values ρ T ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 : T ]v.
Proof.
  intros; eapply (PER_refl_right tree (fun v1 v2 => [ ρ ⊨ v1 ≡ v2 : T ]v) v1 v2);
    steps; eauto with eapply_any.
Qed.

Lemma PER_values_trans:
  forall ρ T v1 v2 v3,
    PER_type_values ρ T ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v3 : T ]v ->
    [ ρ ⊨ v1 ≡ v3 : T ]v.
Proof.
  intros; unshelve eapply (PER_trans _ _ v1 v2 v3 _ _ H); steps.
Qed.

Lemma PER_type_values_expr:
  forall ρ T,
    valid_interpretation ρ ->
    PER_type_values ρ T ->
    PER_type_expr ρ T.
Proof.
  repeat step || unfold reduces_to in * || Build_PER || t_deterministic_star.
  - exists v2, v1; eauto using PER_values_sym.
  - exists v0, v2; eauto using PER_values_trans.
Qed.

Hint Extern 1 => apply PER_type_values_expr: PER_type_values_expr.

Lemma PER_expr_sym:
  forall ρ T t1 t2,
    valid_interpretation ρ ->
    PER_type_values ρ T ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t2 ≡ t1 : T ].
Proof.
  intros; unshelve eapply (PER_sym _ _ t1 t2 _ _); steps; eauto with PER_type_values_expr.
Qed.

Lemma PER_expr_trans:
  forall ρ T t1 t2 t3,
    valid_interpretation ρ ->
    PER_type_values ρ T ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t2 ≡ t3 : T ] ->
    [ ρ ⊨ t1 ≡ t3 : T ].
Proof.
  intros; unshelve eapply (PER_trans _ _ t1 t2 t3 _ _ _); steps; eauto with PER_type_values_expr.
Qed.

Lemma PER_expr_refl_left:
  forall ρ T t1 t2,
    valid_interpretation ρ ->
    PER_type_values ρ T ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t1 : T ].
Proof.
  intros; eapply (PER_refl_left tree (fun t1 t2 => [ ρ ⊨ t1 ≡ t2 : T ]) t1 t2);
    eauto with PER_type_values_expr.
Qed.

Lemma PER_expr_refl_right:
  forall ρ T v1 v2,
    valid_interpretation ρ ->
    PER_type_values ρ T ->
    [ ρ ⊨ v1 ≡ v2 : T ] ->
    [ ρ ⊨ v2 : T ].
Proof.
  intros; eapply (PER_refl_right tree (fun v1 v2 => [ ρ ⊨ v1 ≡ v2 : T ]) v1 v2);
    eauto with PER_type_values_expr.
Qed.

Lemma PER_arrow:
  forall ρ A B,
    valid_interpretation ρ ->
    PER_type_values ρ A ->
    (forall a,
      [ ρ ⊨ a : A ]v ->
      PER_type_values ρ (open 0 B a)) ->
    (forall a1 a2,
      [ ρ ⊨ a1 ≡ a2 : A ]v ->
      [ ρ ⊨ open 0 B a1 =:= open 0 B a2 ]
    ) ->
    PER_type_values ρ (T_arrow A B).
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red.

  - eexists; eexists; steps.
    apply PER_expr_sym;
      eauto using swap_equivalent_types_back with eapply_any;
      eauto using PER_values_refl_left.

    eapply swap_equivalent_types_back; eauto.
    eapply_any; eauto using PER_values_sym; t_closer.

  - eexists; eexists; steps.
    eapply PER_expr_trans; eauto with eapply_any;
      eauto using PER_values_refl_left.

    eapply swap_equivalent_types_back; eauto with eapply_any.
    eapply_any; steps; eauto using PER_values_refl_right; t_closer.
Qed.

Lemma equivalent_types_open:
  forall ρ A B1 B2 a1 a2,
    valid_interpretation ρ ->
    [ ρ ⊨ a1 ≡ a2 : A ]v ->
    PER_type_values ρ A ->
    (forall v1 v2,
      [ ρ ⊨ v1 ≡ v2 : A ]v ->
      valid_interpretation ρ ->
      [ ρ ⊨ open 0 B1 v1 =:= open 0 B2 v2 ]) ->
    [ ρ ⊨ open 0 B1 a1 =:= open 0 B1 a2 ].
Proof.
  intros.
  eapply equivalent_types_trans; try apply_any; eauto.
  apply equivalent_types_sym.
  apply_any; eauto using PER_values_refl_right.
Qed.

Lemma equivalent_types_open2:
  forall ρ A B1 B2 a1 a2,
    valid_interpretation ρ ->
    [ρ ⊨ a1 ≡ a2 : A ]v ->
    PER_type_values ρ A ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A ]v ->
      valid_interpretation ρ ->
      [ρ ⊨ open 0 B1 v1 =:= open 0 B2 v2]) ->
    [ρ ⊨ open 0 B2 a1 =:= open 0 B2 a2].
Proof.
  intros.
  eapply (equivalent_types_open ρ A B2 B1 a1 a2); repeat step;
    eauto using PER_values_sym, equivalent_types_sym.
Qed.

Lemma subtype_arrow:
  forall ρ A1 B1 A2 B2,
    is_erased_type B2 ->
    valid_interpretation ρ ->
    PER_type_values ρ A2 ->
    [ ρ ⊨ A2 <: A1 ] ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      [ρ ⊨ open 0 B1 v1 <: open 0 B2 v2 ]) ->
    [ ρ ⊨ T_arrow A1 B1 <: T_arrow A2 B2 ].
Proof.
  intros; unfold strong_subtype; repeat step || simp_red.
  eexists; eexists; steps.
  apply swap_subtype with (open 0 B1 a1); eauto.
  apply_any; steps; apply_any; eauto using PER_values_refl_left.
Qed.

Lemma equivalent_types_arrow:
  forall ρ A1 B1 A2 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    valid_interpretation ρ ->
    PER_type_values ρ A1 ->
    PER_type_values ρ A2 ->
    [ ρ ⊨ A1 =:= A2 ] ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      valid_interpretation ρ ->
      [ρ ⊨ open 0 B1 v1 =:= open 0 B2 v2 ]) ->
    [ ρ ⊨ T_arrow A1 B1 =:= T_arrow A2 B2 ].
Proof.
  intros; apply strong_subtype_antisymmetric.
  - apply subtype_arrow; steps;
      eauto using equivalent_types_strong_subtype_1, equivalent_types_strong_subtype_2.
  - apply subtype_arrow; steps;
      eauto using equivalent_types_strong_subtype_1;
      eauto using equivalent_types_strong_subtype_2, PER_values_sym with apply_any.
Qed.

Lemma good_types_arrow:
  forall ρ A1 B1 A2 B2,
    valid_interpretation ρ ->
    is_erased_type B1 ->
    is_erased_type B2 ->
    good_types ρ A1 A2 ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      good_types ρ (open 0 B1 v1) (open 0 B2 v2)) ->
    good_types ρ (T_arrow A1 B1) (T_arrow A2 B2).
Proof.
  unfold good_types; steps.

  - eapply PER_arrow; steps; eauto with eapply_any.
    eapply equivalent_types_open; eauto 2 with step_tactic eapply_any.

  - eapply PER_arrow; steps; eauto with eapply_any.
    eapply equivalent_types_open2; steps; eapply_any; steps;
      eauto using swap_equivalent_types_values_back.

  - apply equivalent_types_arrow; steps; eauto with apply_any.
Qed.

Lemma PER_prod:
  forall ρ A B,
    valid_interpretation ρ ->
    PER_type_values ρ A ->
    (forall a,
      [ ρ ⊨ a : A ]v ->
      PER_type_values ρ (open 0 B a)) ->
    (forall a1 a2,
      [ ρ ⊨ a1 ≡ a2 : A ]v ->
      [ ρ ⊨ open 0 B a1 =:= open 0 B a2 ]
    ) ->
    PER_type_values ρ (T_prod A B).
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red.

  - do 4 eexists; steps; eauto; t_closer;
      eauto using PER_values_sym.
    apply_any; eauto using PER_values_refl_right.
    eapply swap_equivalent_types_values_back; eauto using PER_values_sym.

  - do 4 eexists; steps; eauto;
      eauto using PER_values_trans, PER_values_refl_left.

    eapply PER_values_trans; eauto using PER_values_refl_left.
    eapply swap_equivalent_types_values; eauto using PER_values_sym.
Qed.

Lemma subtype_prod:
  forall ρ A1 B1 A2 B2,
    is_erased_type B2 ->
    valid_interpretation ρ ->
    PER_type_values ρ A1 ->
    [ ρ ⊨ A1 <: A2 ] ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      [ρ ⊨ open 0 B1 v1 <: open 0 B2 v2 ]) ->
    [ ρ ⊨ T_prod A1 B1 <: T_prod A2 B2 ].
Proof.
  intros; unfold strong_subtype; repeat step || simp_red.
  eexists; eexists; eexists; eexists; steps; steps;
    eauto using PER_values_refl_left with eapply_any.
Qed.

Lemma equivalent_types_prod:
  forall ρ A1 B1 A2 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    valid_interpretation ρ ->
    PER_type_values ρ A1 ->
    PER_type_values ρ A2 ->
    [ ρ ⊨ A1 =:= A2 ] ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      [ρ ⊨ open 0 B1 v1 =:= open 0 B2 v2 ]) ->
    [ ρ ⊨ T_prod A1 B1 =:= T_prod A2 B2 ].
Proof.
  intros; apply strong_subtype_antisymmetric.
  - apply subtype_prod; steps;
      eauto using equivalent_types_strong_subtype_1, equivalent_types_strong_subtype_2.
  - apply subtype_prod; steps;
      eauto using equivalent_types_strong_subtype_1;
      eauto using equivalent_types_strong_subtype_2, PER_values_sym with apply_any.
Qed.

Lemma good_types_prod:
  forall ρ A1 B1 A2 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    valid_interpretation ρ ->
    good_types ρ A1 A2 ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      good_types ρ (open 0 B1 v1) (open 0 B2 v2)) ->
    good_types ρ (T_prod A1 B1) (T_prod A2 B2).
Proof.
  unfold good_types; steps.

  - apply PER_prod; steps; eauto with eapply_any.
    eapply equivalent_types_open; eauto 2 with step_tactic eapply_any.

  - apply PER_prod; steps; eauto with eapply_any.
    eapply equivalent_types_open2; steps; eauto 4 with step_tactic eapply_any.

  - apply equivalent_types_prod; steps; eauto with apply_any.
Qed.

Lemma PER_sum:
  forall ρ A B,
    PER_type_values ρ A ->
    PER_type_values ρ B ->
    PER_type_values ρ (T_sum A B).
Proof.
  repeat step || Build_PER || simp_red;
    eauto 7 using PER_values_sym;
    eauto 7 using PER_values_trans.
Qed.

Lemma subtype_sum:
  forall ρ A1 B1 A2 B2,
    PER_type_values ρ A2 ->
    [ ρ ⊨ A1 <: A2 ] ->
    [ ρ ⊨ B1 <: B2 ] ->
    [ ρ ⊨ T_sum A1 B1 <: T_sum A2 B2 ].
Proof.
  intros; unfold strong_subtype; repeat step || simp_red;
    eauto 4 with step_tactic.
Qed.

Lemma equivalent_types_sum:
  forall ρ A1 B1 A2 B2,
    PER_type_values ρ A1 ->
    PER_type_values ρ A2 ->
    [ ρ ⊨ A1 =:= A2 ] ->
    [ ρ ⊨ B1 =:= B2 ] ->
    [ ρ ⊨ T_sum A1 B1 =:= T_sum A2 B2 ].
Proof.
  intros; apply strong_subtype_antisymmetric;
    eauto using subtype_sum, equivalent_types_strong_subtype_1, equivalent_types_strong_subtype_2.
Qed.

Lemma good_types_sum:
  forall ρ A1 B1 A2 B2,
    good_types ρ A1 A2 ->
    good_types ρ B1 B2 ->
    good_types ρ (T_sum A1 B1) (T_sum A2 B2).
Proof.
  unfold good_types; steps;
    eauto using PER_sum;
    eauto using equivalent_types_sum.
Qed.

Lemma clos_trans_sym:
  forall ρ A B x y,
    clos_trans_1n tree (fun v1' v2' : tree => [ρ ⊨ v1' ≡ v2' : A ]v \/ [ρ ⊨ v1' ≡ v2' : B ]v) x y ->
    PER_type_values ρ A ->
    PER_type_values ρ B ->
    clos_trans_1n tree (fun v1' v2' : tree => [ρ ⊨ v1' ≡ v2' : A ]v \/ [ρ ⊨ v1' ≡ v2' : B ]v) y x.
Proof.
  induction 1; steps; eauto using t1n_step, PER_values_sym.
  - apply clos_trans_t1n, clos_tn1_trans.
    eapply Relation_Operators.tn1_trans; eauto using PER_values_sym.
    apply clos_trans_tn1, clos_t1n_trans; steps.
  - apply clos_trans_t1n, clos_tn1_trans.
    eapply Relation_Operators.tn1_trans; eauto using PER_values_sym.
    apply clos_trans_tn1, clos_t1n_trans; steps.
Qed.

Lemma PER_union:
  forall ρ A B,
    PER_type_values ρ A ->
    PER_type_values ρ B ->
    PER_type_values ρ (T_union A B).
Proof.
  repeat step || Build_PER || simp_red;
    eauto using clos_trans_sym;
    eauto using clos_trans_t1n, t_trans, t1n_trans.
Qed.

(*
Lemma subtype_sum:
  forall ρ A1 B1 A2 B2,
    PER_type_values ρ A2 ->
    [ ρ ⊨ A1 <: A2 ] ->
    [ ρ ⊨ B1 <: B2 ] ->
    [ ρ ⊨ T_sum A1 B1 <: T_sum A2 B2 ].
Proof.
  intros; unfold strong_subtype; repeat step || simp_red;
    eauto 4 with step_tactic.
Qed.

Lemma equivalent_types_sum:
  forall ρ A1 B1 A2 B2,
    PER_type_values ρ A1 ->
    PER_type_values ρ A2 ->
    [ ρ ⊨ A1 =:= A2 ] ->
    [ ρ ⊨ B1 =:= B2 ] ->
    [ ρ ⊨ T_sum A1 B1 =:= T_sum A2 B2 ].
Proof.
  intros; apply strong_subtype_antisymmetric;
    eauto using subtype_sum, equivalent_types_strong_subtype_1, equivalent_types_strong_subtype_2.
Qed.

Lemma good_types_sum:
  forall ρ A1 B1 A2 B2,
    valid_interpretation ρ ->
    good_types ρ A1 A2 ->
    good_types ρ B1 B2 ->
    good_types ρ (T_sum A1 B1) (T_sum A2 B2).
Proof.
  unfold good_types; steps;
    eauto using PER_sum;
    eauto using equivalent_types_sum.
Qed.
*)

Lemma PER_refine:
  forall ρ A p,
    PER_type_values ρ A ->
    PER_type_values ρ (T_refine A p).
Proof.
  repeat step || Build_PER || simp_red;
    eauto using PER_values_sym;
    eauto using PER_values_trans.
Qed.

Lemma subtype_refine:
  forall ρ A1 A2 p1 p2,
    is_erased_term p2 ->
    wf p2 1 ->
    pfv p2 term_var = nil ->
    PER_type_values ρ A1 ->
    (forall v1 v2,
      [ ρ ⊨ v1 ≡ v2 : A1 ]v ->
      [ open 0 p1 v1 ≡ open 0 p2 v2 ]) ->
    [ ρ ⊨ A1 <: A2 ] ->
    [ ρ ⊨ T_refine A1 p1 <: T_refine A2 p2 ].
Proof.
  intros; unfold strong_subtype; repeat step || simp_red;
    eauto 4 with step_tactic;
    eauto using equivalent_star_true, PER_values_sym.
Qed.

Lemma equivalent_types_refine:
  forall ρ A1 A2 p1 p2,
    is_erased_term p1 ->
    wf p1 1 ->
    pfv p1 term_var = nil ->
    is_erased_term p2 ->
    wf p2 1 ->
    pfv p2 term_var = nil ->
    PER_type_values ρ A1 ->
    PER_type_values ρ A2 ->
    (forall v1 v2, [ ρ ⊨ v1 ≡ v2 : A1 ]v -> [ open 0 p1 v1 ≡ open 0 p2 v2 ]) ->
    [ ρ ⊨ A1 =:= A2 ] ->
    [ ρ ⊨ T_refine A1 p1 =:= T_refine A2 p2 ].
Proof.
  intros; apply strong_subtype_antisymmetric;
    eauto 7 using subtype_refine, PER_values_sym, equivalent_sym,
                  equivalent_types_strong_subtype_1, equivalent_types_strong_subtype_2
      with eapply_any.
Qed.

Lemma good_types_refine:
  forall ρ A1 A2 p1 p2,
    is_erased_term p1 ->
    wf p1 1 ->
    pfv p1 term_var = nil ->
    is_erased_term p2 ->
    wf p2 1 ->
    pfv p2 term_var = nil ->
    (forall v1 v2, [ ρ ⊨ v1 ≡ v2 : A1 ]v -> [ open 0 p1 v1 ≡ open 0 p2 v2 ]) ->
    good_types ρ A1 A2 ->
    good_types ρ (T_refine A1 p1) (T_refine A2 p2).
Proof.
  unfold good_types; steps;
    eauto using PER_refine;
    eauto using equivalent_types_refine.
Qed.

Lemma PER_type_refine:
  forall ρ A B,
    valid_interpretation ρ ->
    PER_type_values ρ A ->
    (forall a1 a2,
      [ ρ ⊨ a1 ≡ a2 : A ]v ->
      [ ρ ⊨ open 0 B a1 =:= open 0 B a2 ]
    ) ->
    PER_type_values ρ (T_type_refine A B).
Proof.
  repeat step || constructor || unfold symmetric, transitive || simp_red;
    eauto using PER_values_sym;
    eauto using PER_values_trans;
    eauto with eapply_any.
Qed.

Lemma subtype_type_refine:
  forall ρ A1 B1 A2 B2,
    is_erased_type B2 ->
    valid_interpretation ρ ->
    PER_type_values ρ A1 ->
    [ ρ ⊨ A1 <: A2 ] ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      [ρ ⊨ open 0 B1 v1 <: open 0 B2 v2 ]) ->
    [ ρ ⊨ T_type_refine A1 B1 <: T_type_refine A2 B2 ].
Proof.
  intros; unfold strong_subtype; repeat step || simp_red.
  eexists; eexists; steps; steps;
    eauto using PER_values_refl_left with eapply_any.
Qed.

Lemma equivalent_types_type_refine:
  forall ρ A1 B1 A2 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    valid_interpretation ρ ->
    PER_type_values ρ A1 ->
    PER_type_values ρ A2 ->
    [ ρ ⊨ A1 =:= A2 ] ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      [ρ ⊨ open 0 B1 v1 =:= open 0 B2 v2 ]) ->
    [ ρ ⊨ T_type_refine A1 B1 =:= T_type_refine A2 B2 ].
Proof.
  intros; apply strong_subtype_antisymmetric.
  - apply subtype_type_refine; steps;
      eauto using equivalent_types_strong_subtype_1, equivalent_types_strong_subtype_2.
  - apply subtype_type_refine; steps;
      eauto using equivalent_types_strong_subtype_1;
      eauto using equivalent_types_strong_subtype_2, PER_values_sym with apply_any.
Qed.

Lemma good_types_type_refine:
  forall ρ A1 B1 A2 B2,
    is_erased_type B1 ->
    is_erased_type B2 ->
    valid_interpretation ρ ->
    good_types ρ A1 A2 ->
    (forall v1 v2,
      [ρ ⊨ v1 ≡ v2 : A1 ]v ->
      good_types ρ (open 0 B1 v1) (open 0 B2 v2)) ->
    good_types ρ (T_type_refine A1 B1) (T_type_refine A2 B2).
Proof.
  unfold good_types; steps.

  - eapply PER_type_refine; steps.
    eapply equivalent_types_open; eauto; steps; eauto with eapply_any.
  - eapply PER_type_refine; steps.
    eapply equivalent_types_open2; eauto; steps; eauto with eapply_any.
  - apply equivalent_types_type_refine; steps; eauto with eapply_any.
Qed.

Lemma equal_types_equivalent_types:
  forall ρ T1 T2,
    [ ρ ⊨ T1 = T2 ] ->
    valid_interpretation ρ ->
    good_types ρ T1 T2.
Proof.
  induction 1; intros; intuition auto;
    eauto using good_types_fvar;
    eauto using good_types_unit;
    eauto using good_types_bool;
    eauto using good_types_nat;
    eauto using good_types_abs;
    eauto using good_types_arrow;
    eauto using good_types_sum;
    eauto using good_types_prod;
    eauto using good_types_refine;
    eauto using good_types_type_refine.
Qed.
