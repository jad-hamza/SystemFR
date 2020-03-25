Require Import PeanoNat.
Require Import Relations.

Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.EquivalenceLemmas.

Open Scope list_scope.

Arguments PER { A }.

Definition reducibility_candidate2 (R: tree -> tree -> Prop): Prop :=
  PER R /\
  forall v1 v2, R v1 v2 ->
    closed_value v1 /\
    (forall v, cbv_value v /\ equivalent_terms v v1 -> R v v2).

(* an interpretation is a map from type variables to reducibility candidates *)
Definition interpretation2: Type := list (nat * (tree -> tree -> Prop)).

Definition pre_interpretation2: Type := list (nat * (tree -> tree -> tree -> Prop)).

Fixpoint valid_interpretation2 (theta: interpretation2): Prop :=
  match theta with
  | nil => True
  | (x, R) :: theta' => valid_interpretation2 theta' /\ reducibility_candidate2 R
  end.

Lemma valid_interpretation_cons:
  forall theta RC X,
    valid_interpretation2 theta ->
    reducibility_candidate2 RC ->
    valid_interpretation2 ((X, RC) :: theta).
Proof.
  steps.
Qed.

Lemma in_valid_interpretation_per: forall theta X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  PER R.
Proof.
  induction theta; repeat step || apply_any; eauto.
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

Lemma in_valid_interpretation_sym: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  R v2 v1.
Proof.
  intros.
  eapply PER_sym; eauto.
  eapply in_valid_interpretation_per; eauto.
Qed.

Lemma in_valid_interpretation_erased1: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  is_erased_term v1.
Proof.
  induction theta;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate2 in *; eauto.
Qed.

Lemma in_valid_interpretation_erased2: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  is_erased_term v2.
Proof.
  intros.
  eapply in_valid_interpretation_erased1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_wf1: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  wf v1 0.
Proof.
  induction theta;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate2 in *; eauto.
Qed.

Lemma in_valid_interpretation_wf2: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  wf v2 0.
Proof.
  intros.
  eapply in_valid_interpretation_wf1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_value1: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  cbv_value v1.
Proof.
  induction theta;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate2 in *; eauto.
Qed.

Lemma in_valid_interpretation_value2: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  cbv_value v2.
Proof.
  intros.
  eapply in_valid_interpretation_value1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_fv1: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  pfv v1 term_var = nil.
Proof.
  induction theta;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate2 in *; eauto.
Qed.

Lemma in_valid_interpretation_fv2: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  pfv v2 term_var = nil.
Proof.
  intros.
  eapply in_valid_interpretation_fv1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_tfv1: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  pfv v1 type_var = nil.
Proof.
  induction theta;
    repeat step || apply_any || instantiate_any ||
           unfold reducibility_candidate2 in * ||
           unfold closed_value, closed_term in *; eauto with fv.
Qed.

Lemma in_valid_interpretation_tfv2: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  pfv v2 type_var = nil.
Proof.
  intros.
  eapply in_valid_interpretation_tfv1; eauto.
  eapply in_valid_interpretation_sym; eauto.
Qed.

Lemma in_valid_interpretation_pfv1: forall theta v1 v2 X R tag,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  pfv v1 tag = nil.
Proof.
  destruct tag; eauto using in_valid_interpretation_fv1, in_valid_interpretation_tfv1.
Qed.

Lemma in_valid_interpretation_pfv2: forall theta v1 v2 X R tag,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  pfv v2 tag = nil.
Proof.
  destruct tag; eauto using in_valid_interpretation_fv2, in_valid_interpretation_tfv2.
Qed.

Lemma in_valid_interpretation_twf1: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  twf v1 0.
Proof.
  eauto using is_erased_term_twf, in_valid_interpretation_erased1.
Qed.

Lemma in_valid_interpretation_twf2: forall theta v1 v2 X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  twf v2 0.
Proof.
  eauto using is_erased_term_twf, in_valid_interpretation_erased2.
Qed.

Lemma in_valid_interpretation_equiv1: forall theta v1 v2 v X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  equivalent_terms v1 v ->
  cbv_value v ->
  R v v2.
Proof.
  induction theta; repeat step || unfold reducibility_candidate2 in * || instantiate_any;
    try solve [ eapply_any; steps; eauto using equivalent_sym ].
Qed.

Lemma in_valid_interpretation_equiv2: forall theta v1 v2 v X R,
  valid_interpretation2 theta ->
  lookup Nat.eq_dec theta X = Some R ->
  R v1 v2 ->
  equivalent_terms v2 v ->
  cbv_value v ->
  R v1 v.
Proof.
  induction theta; repeat step || unfold reducibility_candidate2 in * || instantiate_any;
    try solve [ eapply_any; steps; eauto using equivalent_sym ].
  apply PER_sym; auto.
  eapply_any; steps.
  - apply PER_sym; eauto.
  - eauto using equivalent_sym.
Qed.

Lemma valid_interpretation_append:
  forall theta1 theta2,
    valid_interpretation2 theta1 ->
    valid_interpretation2 theta2 ->
    valid_interpretation2 (theta1 ++ theta2).
Proof.
  induction theta1; steps.
Qed.

Hint Resolve valid_interpretation_cons: b_valid_interp.
Hint Resolve valid_interpretation_append: b_valid_interp.
