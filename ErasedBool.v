Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_true:
  forall ρ, reducible_values ρ ttrue ttrue T_bool.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_true:
  forall Θ Γ,
    [ Θ; Γ ⊨ ttrue : T_bool ].
Proof.
  unfold open_reducible, reduces_to, closed_term in *; steps;
    eauto using reducible_true with star.
Qed.

Lemma reducible_false:
  forall ρ, reducible_values ρ tfalse tfalse T_bool.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_false:
  forall Θ Γ,
    [ Θ; Γ ⊨ tfalse : T_bool ].
Proof.
  unfold open_reducible, reduces_to, closed_term in *; steps;
    eauto using reducible_false with star.
Qed.

Lemma open_reducible_ite:
  forall Θ Γ T b t t' x,
    wf t 0 ->
    wf t' 0 ->
    subset (fv t) (support Γ) ->
    subset (fv t') (support Γ) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ Θ) ->
    is_erased_term b ->
    is_erased_term t ->
    is_erased_term t' ->
    [ Θ; Γ ⊨ b : T_bool ] ->
    [ Θ; (x, T_equiv b ttrue)  :: Γ ⊨ t : T ] ->
    [ Θ; (x, T_equiv b tfalse) :: Γ ⊨ t' : T ] ->
    [ Θ; Γ ⊨ ite b t t' : T ].
Proof.
  intros; unfold open_reducible; steps.

  unfold open_reducible in *; repeat step || t_instantiate_sat3.

  top_level_unfold reducible; top_level_unfold reduces_to; repeat step || simp_red.

  - apply star_backstep_reducible with (psubstitute t l1 term_var) (psubstitute t l2 term_var);
      repeat step || list_utils;
      eauto using star_one, star_trans with cbvlemmas smallstep;
      t_closer.

    unshelve epose proof (H11 _ ((x, uu) :: l1) ((x, uu) :: l2) _ _ _);
      repeat step || apply SatCons || list_utils || simp_red || t_substitutions;
      try solve [ equivalent_star ].

  - apply star_backstep_reducible with (psubstitute t' l1 term_var) (psubstitute t' l2 term_var);
      repeat step || list_utils;
      eauto using star_one, star_trans with cbvlemmas smallstep;
      t_closer.

    unshelve epose proof (H12 _ ((x, uu) :: l1) ((x, uu) :: l2) _ _ _);
      repeat step || apply SatCons || list_utils || simp_red || t_substitutions;
      try solve [ equivalent_star ].
Qed.
