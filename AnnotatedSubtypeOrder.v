Require Export SystemFR.Judgments.

Lemma subtype_refl:
  forall Θ Γ T,
    [[ Θ; Γ ⊨ T <: T ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype; steps.
Qed.

Lemma subtype_trans:
  forall Θ Γ T1 T2 T3,
    [[ Θ; Γ ⊨ T1 <: T2 ]] ->
    [[ Θ; Γ ⊨ T2 <: T3 ]] ->
    [[ Θ; Γ ⊨ T1 <: T3 ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype; steps.
Qed.
