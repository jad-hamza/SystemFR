Require Import Coq.Lists.List.

Require Export SystemFR.TreeLists.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma satisfies_erased_terms_1:
  forall ρ l1 l2 Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l1 l2 ->
    erased_terms l1.
Proof.
  induction l1; repeat step || step_inversion satisfies;
    eauto with erased.
Qed.

Hint Immediate satisfies_erased_terms_1: erased.

Lemma satisfies_erased_terms_2:
  forall ρ l1 l2 Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l1 l2 ->
    erased_terms l2.
Proof.
  induction l1; repeat step || step_inversion satisfies;
    eauto with erased.
Qed.

Hint Immediate satisfies_erased_terms_2: erased.

Lemma satisfies_weaken:
  forall ρ Γ1 Γ2 x A B l l',
    (forall v1 v2 l l',
      satisfies (reducible_values ρ) Γ2 l l' ->
      reducible_values ρ v1 v2 (substitute A l) ->
      reducible_values ρ v1 v2 (substitute B l)) ->
    subset (fv A) (support Γ2) ->
    subset (fv B) (support Γ2) ->
    NoDup (support (Γ1 ++ (x, A) :: Γ2)) ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, A) :: Γ2) l l' ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, B) :: Γ2) l l'.
Proof.
  induction Γ1;
    repeat step || list_utils || apply SatCons || step_inversion NoDup ||
           step_inversion satisfies; eauto.

  apply IHΓ1 with A; repeat step || list_utils; eauto.
Qed.
