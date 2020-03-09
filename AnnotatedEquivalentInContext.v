Require Import Coq.Lists.List.

Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.EquivalentStar.

Opaque reducible_values.

Lemma annotated_equivalent_refine_equivalent:
  forall tvars gamma gamma' x T p,
    is_annotated_term p ->
    ~ x ∈ pfv p term_var ->
    (forall z, z ∈ pfv p term_var -> z ∈ support gamma -> False) ->
    [[ tvars; gamma ++ (x, T_refine T p) :: gamma' ⊨ open 0 p (fvar x term_var) ≡ ttrue ]].
Proof.
  unfold annotated_equivalent, open_equivalent;
    repeat step || satisfies_cut || rewrite erase_context_append in * || step_inversion satisfies || list_utils || simp_red.

  rewrite substitute_append2; repeat step || fv_open || t_fv_erase || list_utils || erase_open || t_substitutions;
    eauto with fv;
    try solve [ equivalent_star ].

  apply (satisfies_y_in_support _ _ _ _ _ _ x0) in H3; repeat step;
    side_conditions.
Qed.

Lemma annotated_equivalence_in_context:
  forall tvars gamma gamma' x e1 e2,
    (forall z, z ∈ pfv e1 term_var -> z ∈ support gamma -> False) ->
    (forall z, z ∈ pfv e2 term_var -> z ∈ support gamma -> False) ->
    [[ tvars; gamma ++ (x, T_equiv e1 e2) :: gamma' ⊨ e1 ≡ e2 ]].
Proof.
  unfold annotated_equivalent, open_equivalent;
    repeat step || satisfies_cut || rewrite erase_context_append in * || step_inversion satisfies || list_utils || simp_red.

  rewrite substitute_append2; repeat step || fv_open || t_fv_erase || list_utils || t_substitutions.
  - rewrite substitute_append2; repeat step || fv_open || t_fv_erase || list_utils || t_substitutions.
    apply (satisfies_y_in_support _ _ _ _ _ _ x0) in H2; repeat step;
      side_conditions.
  - apply (satisfies_y_in_support _ _ _ _ _ _ x0) in H2; repeat step;
      side_conditions.
Qed.
