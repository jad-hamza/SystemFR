Require Export SystemFR.RedTactics.

Lemma open_reducible_err:
  forall Θ Γ T,
    [ Θ; Γ ⊨ tfalse ≡ ttrue ] ->
    [ Θ; Γ ⊨ notype_err : T ].
Proof.
  unfold open_reducible, open_equivalent;
    repeat step || t_instantiate_sat3;
    eauto using false_true_not_equivalent with exfalso.
Qed.
