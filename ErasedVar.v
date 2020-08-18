Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma open_reducible_weaken:
  forall ρ (Γ : context) (x : nat) T u U,
    open_reducible ρ Γ u U ->
    ~(x ∈ support Γ) ->
    ~(x ∈ fv u) ->
    ~(x ∈ fv U) ->
    [ ρ; (x, T) :: Γ ⊨ u : U ].
Proof.
  unfold open_reducible in *; repeat step || step_inversion satisfies || t_substitutions.
Qed.

Lemma open_reducible_var:
  forall Θ Γ x T,
    lookup Nat.eq_dec Γ x = Some T ->
    [ Θ; Γ ⊨ fvar x term_var : T ].
Proof.
  unfold open_reducible;
    repeat step || t_termlist || t_lookup;
    eauto using reducible_value_expr.
Qed.
