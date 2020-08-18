Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque Nat.eq_dec.
Opaque makeFresh.

Lemma reducible_values_refine_subtype:
  forall ρ A p q v,
    wf p 1 ->
    wf q 1 ->
    is_erased_term q ->
    pfv q term_var = nil ->
    star scbv_step (open 0 q v) ttrue ->
    reducible_values ρ v (T_refine A p) ->
    reducible_values ρ v (T_refine A q).
Proof.
  repeat step || simp_red.
Qed.
