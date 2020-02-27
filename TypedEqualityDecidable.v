Require Import List.
Import ListNotations.

Require Export SystemFR.TypedEquality.
Require Export SystemFR.NatRecognizer.

Opaque reducible_values.

Definition decidable theta T : Prop :=
  forall v,
    reducible_values theta v T ->
    exists f,
      is_erased_term f /\
      wf f 0 /\
      pfv f term_var = nil /\
      reducible_values theta f (T_arrow T T_bool) /\
      forall v',
        cbv_value v' ->
        star scbv_step (app f v') ttrue <-> v = v'.

Lemma decidable_nat:
  decidable [] T_nat.
Proof.
  unfold decidable; repeat step || simp_red.
  exists (notype_lambda (nat_recognizer v)); steps;
    eauto using is_erased_term_nat_recognizer;
    eauto using wf_nat_recognizer;
    eauto using fv_nat_recognizer.

  - apply reducible_lambda; repeat step || simp_red;
      eauto using is_erased_term_nat_recognizer;
      eauto using wf_nat_recognizer;
      eauto using fv_nat_recognizer.

    unshelve epose proof (eval_nat_recognizer2 v u _);
      repeat step || unfold reducible, reduces_to || unfold closed_term;
      eauto using is_erased_term_nat_recognizer with erased;
      eauto using wf_nat_recognizer with wf;
      eauto using fv_nat_recognizer with fv;
      try solve [ eexists; steps; try eassumption; repeat step || simp_red ].

  - star_smallstep_app_onestep; steps.
    apply_anywhere true_nat_recognizer; steps.

  - eapply Trans; eauto with smallstep values;
      eauto using eval_nat_recognizer.
Qed.

Lemma typed_equality_decidable:
  forall theta T v1 v2,
    equivalent_at theta T v1 v2 ->
    decidable theta T ->
    cbv_value v1 ->
    cbv_value v2 ->
    v1 = v2.
Proof.
  unfold decidable, equivalent_at;
    repeat step.

  unshelve epose proof (H0 v1 _);
    repeat step;
    eauto using reducible_expr_value.

  apply_any; steps.
  eapply equivalent_star_true; eauto with apply_any.
Qed.
