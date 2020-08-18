Require Export Equations.Equations.

Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma reducible_values_top:
  forall ρ v T,
    valid_interpretation ρ ->
    reducible_values ρ v T ->
    reducible_values ρ v T_top.
Proof.
  repeat step || simp reducible_values;
    eauto using reducible_values_closed.
Qed.

Lemma reducible_top:
  forall ρ t T,
    valid_interpretation ρ ->
    reducible ρ t T ->
    reducible ρ t T_top.
Proof.
  eauto using reducible_values_top, reducible_values_exprs.
Qed.

Lemma open_reducible_top:
  forall Θ Γ t T,
    [ Θ; Γ ⊨ t : T ] ->
    [ Θ; Γ ⊨ t : T_top ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3;
    eauto using reducible_top.
Qed.
