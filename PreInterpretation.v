Require Import Coq.Lists.List.
Import ListNotations.

Require Export SystemFR.ReducibilityCandidate.

Fixpoint valid_pre_interpretation (P: tree -> Prop) (ρ: list (nat * (tree -> tree -> tree -> Prop))) : Prop :=
  match ρ with
  | nil => True
  | (_, RC) :: ρ' =>
    valid_pre_interpretation P ρ' /\
    forall a, P a -> reducibility_candidate (RC a)
  end.

Lemma valid_interpretation_equiv:
  forall P1 P2 pρ,
    valid_pre_interpretation P1 pρ ->
    (forall x, P1 x <-> P2 x) ->
    valid_pre_interpretation P2 pρ.
Proof.
  induction pρ; steps; eauto with eapply_any.
Qed.

Ltac t_valid_interpretation_equiv :=
  match goal with
  | H1: valid_pre_interpretation ?P1 ?pρ |- valid_pre_interpretation _ ?pρ => apply valid_interpretation_equiv with P1
  end.

Definition push_one (a: tree) (l: list (nat * (tree -> tree -> tree -> Prop))): interpretation :=
  map_values (fun rc => rc a) l.
Definition push_all (P: tree -> Prop) (l: list (nat * (tree -> tree -> tree -> Prop))): interpretation :=
  map_values (fun (rc: tree -> tree -> tree -> Prop) (v1 v2: tree) => (forall a, P a -> rc a v1 v2)) l.

Lemma valid_interpretation_one:
  forall a (P: tree -> Prop) ρ,
    P a ->
    valid_pre_interpretation P ρ ->
    valid_interpretation (push_one a ρ).
Proof.
  induction ρ; steps.
Qed.

Hint Resolve valid_interpretation_one: b_valid_interp.
Hint Extern 1 => eapply valid_interpretation_one; eauto: b_valid_interp.
