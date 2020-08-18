Require Import PeanoNat.
Require Import Relations.

Require Export SystemFR.ClosedTerm.
Require Export SystemFR.EquivalenceLemmas.

Open Scope list_scope.

Arguments PER { A }.

Definition reducibility_candidate (R: tree -> tree -> Prop): Prop :=
  PER R /\
  forall v1 v2, R v1 v2 ->
    closed_value v1 /\
    (forall v, cbv_value v /\ equivalent_terms v v1 -> R v v2).

(* an interpretation is a map from type variables to reducibility candidates *)
Definition interpretation: Type := list (nat * (tree -> tree -> Prop)).

Definition pre_interpretation: Type := list (nat * (tree -> tree -> tree -> Prop)).

Fixpoint valid_interpretation (ρ: interpretation): Prop :=
  match ρ with
  | nil => True
  | (x, R) :: ρ' => valid_interpretation ρ' /\ reducibility_candidate R
  end.

Lemma valid_interpretation_cons:
  forall ρ RC X,
    valid_interpretation ρ ->
    reducibility_candidate RC ->
    valid_interpretation ((X, RC) :: ρ).
Proof.
  steps.
Qed.

Lemma in_valid_interpretation_per: forall ρ X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  PER R.
Proof.
  induction ρ; repeat step || apply_any; eauto.
Qed.

Lemma PER_sym:
  forall T (R: T -> T -> Prop) v1 v2,
    R v1 v2 ->
    PER R ->
    R v2 v1.
Proof.
  intros.
  destruct H0.
  eauto with eapply_any.
Qed.

Hint Extern 1 => eapply PER_sym: PER.

Lemma PER_refl_left:
  forall T (R: T -> T -> Prop) v1 v2,
    R v1 v2 ->
    PER R ->
    R v1 v1.
Proof.
  intros.
  destruct H0.
  eauto with eapply_any.
Qed.

Hint Extern 1 => eapply PER_refl_left: PER.

Lemma PER_refl_right:
  forall T (R: T -> T -> Prop) v1 v2,
    R v1 v2 ->
    PER R ->
    R v2 v2.
Proof.
  intros.
  destruct H0.
  eauto with eapply_any.
Qed.

Hint Extern 1 => eapply PER_refl_right: PER.

Lemma PER_trans:
  forall T (R: T -> T -> Prop) v1 v2 v3,
    R v1 v2 ->
    R v2 v3 ->
    PER R ->
    R v1 v3.
Proof.
  intros.
  destruct H1.
  eauto with eapply_any.
Qed.

Hint Extern 1 => eapply PER_trans: PER.

Lemma in_valid_interpretation_sym: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  R v2 v1.
Proof.
  intros.
  eapply PER_sym; eauto.
  eapply in_valid_interpretation_per; eauto.
Qed.

Lemma in_valid_interpretation_refl_left: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  R v1 v1.
Proof.
  intros.
  eapply PER_refl_left; eauto.
  eapply in_valid_interpretation_per; eauto.
Qed.

Lemma in_valid_interpretation_refl_right: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  R v2 v2.
Proof.
  intros.
  eapply PER_refl_right; eauto.
  eapply in_valid_interpretation_per; eauto.
Qed.

Lemma in_valid_interpretation_trans: forall ρ v1 v2 v3 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  R v2 v3 ->
  R v1 v3.
Proof.
  intros.
  eapply PER_trans; eauto.
  eapply in_valid_interpretation_per; eauto.
Qed.

Lemma in_valid_interpretation_erased1: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  is_erased_term v1.
Proof.
  induction ρ;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate in *; eauto.
Qed.

Lemma in_valid_interpretation_erased2: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  is_erased_term v2.
Proof.
  intros.
  eapply in_valid_interpretation_erased1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_wf1: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  wf v1 0.
Proof.
  induction ρ;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate in *; eauto.
Qed.

Lemma in_valid_interpretation_wf2: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  wf v2 0.
Proof.
  intros.
  eapply in_valid_interpretation_wf1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_value1: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  cbv_value v1.
Proof.
  induction ρ;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate in *; eauto.
Qed.

Lemma in_valid_interpretation_value2: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  cbv_value v2.
Proof.
  intros.
  eapply in_valid_interpretation_value1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_fv1: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  pfv v1 term_var = nil.
Proof.
  induction ρ;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate in *; eauto.
Qed.

Lemma in_valid_interpretation_fv2: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  pfv v2 term_var = nil.
Proof.
  intros.
  eapply in_valid_interpretation_fv1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_tfv1: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  pfv v1 type_var = nil.
Proof.
  induction ρ;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate in * ||
           unfold closed_value, closed_term in *; eauto with fv.
Qed.

Lemma in_valid_interpretation_tfv2: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  pfv v2 type_var = nil.
Proof.
  intros.
  eapply in_valid_interpretation_tfv1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_pfv1: forall ρ v1 v2 X R tag,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  pfv v1 tag = nil.
Proof.
  destruct tag; eauto using in_valid_interpretation_fv1, in_valid_interpretation_tfv1.
Qed.

Lemma in_valid_interpretation_pfv2: forall ρ v1 v2 X R tag,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  pfv v2 tag = nil.
Proof.
  destruct tag; eauto using in_valid_interpretation_fv2, in_valid_interpretation_tfv2.
Qed.

Lemma in_valid_interpretation_twf1: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  twf v1 0.
Proof.
  eauto using is_erased_term_twf, in_valid_interpretation_erased1.
Qed.

Lemma in_valid_interpretation_twf2: forall ρ v1 v2 X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  twf v2 0.
Proof.
  eauto using is_erased_term_twf, in_valid_interpretation_erased2.
Qed.

Lemma in_valid_interpretation_equiv1: forall ρ v1 v2 v X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  equivalent_terms v1 v ->
  cbv_value v ->
  R v v2.
Proof.
  induction ρ; repeat step || unfold reducibility_candidate in * || instantiate_any;
    try solve [ eapply_any; steps; eauto using equivalent_sym ].
Qed.

Lemma in_valid_interpretation_equiv2: forall ρ v1 v2 v X R,
  valid_interpretation ρ ->
  lookup Nat.eq_dec ρ X = Some R ->
  R v1 v2 ->
  equivalent_terms v2 v ->
  cbv_value v ->
  R v1 v.
Proof.
  induction ρ; repeat step || unfold reducibility_candidate in * || instantiate_any;
    try solve [ eapply_any; steps; eauto using equivalent_sym ].
  apply PER_sym; auto.
  eapply_any; steps.
  - apply PER_sym; eauto.
  - eauto using equivalent_sym.
Qed.

Lemma valid_interpretation_append:
  forall ρ1 ρ2,
    valid_interpretation ρ1 ->
    valid_interpretation ρ2 ->
    valid_interpretation (ρ1 ++ ρ2).
Proof.
  induction ρ1; steps.
Qed.

Hint Resolve valid_interpretation_cons: b_valid_interp.
Hint Resolve valid_interpretation_append: b_valid_interp.
