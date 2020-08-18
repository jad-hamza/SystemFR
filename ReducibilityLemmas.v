Require Import Coq.Strings.String.

Require Import Equations.Equations.

Require Export SystemFR.TermList.
Require Export SystemFR.FVLemmasEval.
Require Export SystemFR.WFLemmasEval.
Require Export SystemFR.ReducibilityDefinition.
Opaque reducible_values. (* workaround for rewriting speed *)

Lemma reducible_values_closed_1:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    closed_value v1.
Proof.
  destruct T;
    repeat simp_red || step || destruct_tag || unfold closed_value, closed_term in *;
      eauto using in_valid_interpretation_erased1 with erased;
      eauto using in_valid_interpretation_pfv1 with fv;
      eauto using in_valid_interpretation_wf1 with wf;
      eauto using in_valid_interpretation_value1;
      eauto 2 using is_nat_value_erased;
      eauto 2 using is_nat_value_value.
Qed.

Lemma reducible_values_closed_2:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    closed_value v2.
Proof.
  destruct T;
    repeat simp_red || step || destruct_tag || unfold closed_value, closed_term in *;
      eauto using in_valid_interpretation_erased2 with erased;
      eauto using in_valid_interpretation_pfv2 with fv;
      eauto using in_valid_interpretation_wf2 with wf;
      eauto using in_valid_interpretation_value2;
      eauto 2 using is_nat_value_erased;
      eauto 2 using is_nat_value_value.
Qed.

Lemma reducible_values_props:
  forall ρ v1 v2 T tag,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
      (
        is_erased_term v1 /\ pfv v1 tag = nil /\ wf v1 0 /\ cbv_value v1 /\
        is_erased_term v2 /\ pfv v2 tag = nil /\ wf v2 0 /\ cbv_value v2
      ).
Proof.
  intros ρ v1 v2 T tag H1 H2; destruct tag;
    pose proof (reducible_values_closed_1 ρ v1 v2 T H1 H2);
    pose proof (reducible_values_closed_2 ρ v1 v2 T H1 H2);
    unfold closed_value, closed_term in *; steps;
      eauto using is_erased_term_tfv.
Qed.

Lemma reducible_values_erased_1:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    is_erased_term v1.
Proof.
  intros ρ v1 v2 T H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps.
Qed.

Hint Immediate reducible_values_erased_1: erased.

Lemma reducible_values_erased_2:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    is_erased_term v2.
Proof.
  intros ρ v1 v2 T H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps.
Qed.

Hint Immediate reducible_values_erased_2: erased.

Lemma reducible_erased_1:
  forall ρ t1 t2 T,
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    valid_interpretation ρ ->
    is_erased_term t1.
Proof.
  unfold reduces_to, closed_term; steps.
Qed.

Lemma reducible_erased_2:
  forall ρ t1 t2 T,
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    valid_interpretation ρ ->
    is_erased_term t2.
Proof.
  unfold reduces_to, closed_term; steps.
Qed.

Hint Immediate reducible_erased_1: erased.
Hint Immediate reducible_erased_2: erased.

Lemma reducible_val_fv_1:
  forall ρ v1 v2 T tag,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    pfv v1 tag = nil.
Proof.
  intros ρ v1 v2 T tag H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T tag H1 H2); steps.
Qed.

Lemma reducible_val_fv_2:
  forall ρ v1 v2 T tag,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    pfv v2 tag = nil.
Proof.
  intros ρ v1 v2 T tag H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T tag H1 H2); steps.
Qed.

Hint Immediate reducible_val_fv_1: fv.
Hint Immediate reducible_val_fv_2: fv.

Lemma fv_red_1:
  forall v1 v2 x tag ρ T,
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    x ∈ pfv v1 tag ->
    False.
Proof.
  intros; erewrite reducible_val_fv_1 in *; eauto; steps.
Qed.

Lemma fv_red_2:
  forall v1 v2 x tag ρ T,
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    x ∈ pfv v2 tag ->
    False.
Proof.
  intros; erewrite reducible_val_fv_2 in *; eauto; steps.
Qed.

Hint Extern 1 => solve [ exfalso; eapply reducible_val_fv_1; eauto ] : fv.
Hint Extern 1 => solve [ exfalso; eapply reducible_val_fv_2; eauto ] : fv.

Lemma reducible_val_wf_1:
  forall ρ v1 v2 T k,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    wf v1 k.
Proof.
  intros ρ v1 v2 T k H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps; eauto with wf.
Qed.

Lemma reducible_val_wf_2:
  forall ρ v1 v2 T k,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    wf v2 k.
Proof.
  intros ρ v1 v2 T k H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps; eauto with wf.
Qed.

Hint Immediate reducible_val_wf_1: wf.
Hint Immediate reducible_val_wf_2: wf.

Lemma reducible_val_twf_1:
  forall ρ v1 v2 T k,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    twf v1 k.
Proof.
  intros ρ v1 v2 T k H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps;
    eauto using is_erased_term_twf.
Qed.

Lemma reducible_val_twf_2:
  forall ρ v1 v2 T k,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    twf v2 k.
Proof.
  intros ρ v1 v2 T k H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps;
    eauto using is_erased_term_twf.
Qed.

Hint Immediate reducible_val_twf_1: twf.
Hint Immediate reducible_val_twf_2: twf.

Lemma reducible_val_closed_term_1:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    closed_term v1.
Proof.
  intros ρ v1 v2 T H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2);
    unfold closed_term; steps.
Qed.

Lemma reducible_val_closed_term_2:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    closed_term v2.
Proof.
  intros ρ v1 v2 T H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2);
    unfold closed_term; steps.
Qed.

Hint Immediate reducible_val_closed_term_1: closed.
Hint Immediate reducible_val_closed_term_2: closed.

Lemma red_is_val_1:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    cbv_value v1.
Proof.
  intros ρ v1 v2 T H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps.
Qed.

Lemma red_is_val_2:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    cbv_value v2.
Proof.
  intros ρ v1 v2 T H1 H2.
  pose proof (reducible_values_props ρ v1 v2 T term_var H1 H2); steps.
Qed.

Hint Immediate red_is_val_1: values.
Hint Immediate red_is_val_2: values.

Lemma reducible_val_closed_value_1:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    closed_value v1.
Proof.
  unfold closed_value; steps; eauto with closed values.
Qed.

Lemma reducible_val_closed_value_2:
  forall ρ v1 v2 T,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    valid_interpretation ρ ->
    closed_value v2.
Proof.
  unfold closed_value; steps; eauto with closed values.
Qed.

Hint Immediate reducible_val_closed_value_1: closed.
Hint Immediate reducible_val_closed_value_2: closed.

Ltac values_info :=
  match goal with
  | H1: valid_interpretation ?ρ, H2: reducible_values ?ρ ?v1 ?v2 ?T  |- _ =>
    poseNew (Mark (v1, v2) "");
    pose proof (red_is_val_1 _ _ _ _ H2 H1);
    pose proof (red_is_val_2 _ _ _ _ H2 H1)
  end.

Lemma smallstep_reducible_aux_1:
  forall n ρ t1 t2 T,
    type_nodes T < n ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    forall t1',
      scbv_step t1 t1' ->
      [ ρ ⊨ t1' ≡ t2 : T ].
Proof.
  unfold reduces_to; steps;
    eauto using closed_term_scbv_step.

  eexists; eexists; steps; try eassumption;
    eauto using red_is_val_1, star_one_step_val.
Qed.

Lemma smallstep_reducible_1:
  forall ρ t1 t1' t2 T,
    valid_interpretation ρ ->
    scbv_step t1 t1' ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t1' ≡ t2 : T ].
Proof.
  eauto using smallstep_reducible_aux_1.
Qed.

Lemma smallstep_reducible_aux_2:
  forall n ρ t1 t2 T,
    type_nodes T < n ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    forall t2',
      scbv_step t2 t2' ->
      [ ρ ⊨ t1 ≡ t2' : T ].
Proof.
  unfold reduces_to; steps;
    eauto using closed_term_scbv_step.

  eexists; eexists; steps; try eassumption;
    eauto using red_is_val_2, star_one_step_val.
Qed.

Lemma smallstep_reducible_2:
  forall ρ t1 t2 t2' T,
    valid_interpretation ρ ->
    scbv_step t2 t2' ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t1 ≡ t2' : T ].
Proof.
  eauto using smallstep_reducible_aux_2.
Qed.

Lemma star_smallstep_reducible_1:
  forall t1 t1',
    star scbv_step t1 t1' ->
    forall ρ t2 T,
      valid_interpretation ρ ->
      [ ρ ⊨ t1 ≡ t2 : T ] ->
      [ ρ ⊨ t1' ≡ t2 : T ].
Proof.
  induction 1; steps; eauto using smallstep_reducible_1.
Qed.

Lemma star_smallstep_reducible_2:
  forall t2 t2',
    star scbv_step t2 t2' ->
    forall ρ t1 T,
      valid_interpretation ρ ->
      [ ρ ⊨ t1 ≡ t2 : T ] ->
      [ ρ ⊨ t1 ≡ t2' : T ].
Proof.
  induction 1; steps; eauto using smallstep_reducible_2.
Qed.

Lemma star_smallstep_reducible:
  forall t1 t2 t1' t2',
    star scbv_step t1 t1' ->
    star scbv_step t2 t2' ->
    forall ρ T,
      valid_interpretation ρ ->
      [ ρ ⊨ t1 ≡ t2 : T ] ->
      [ ρ ⊨ t1' ≡ t2' : T ].
Proof.
  eauto using star_smallstep_reducible_1, star_smallstep_reducible_2.
Qed.

Lemma backstep_reducible_aux_1:
  forall n ρ t1' t2 T,
    type_nodes T < n ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1' ≡ t2 : T ] ->
    forall t1,
      closed_term t1 ->
      scbv_step t1 t1' ->
      [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  unfold reduces_to; steps; eauto 6 with star.
Qed.

Lemma backstep_reducible_1:
  forall ρ t1 t1' t2 T,
    valid_interpretation ρ ->
    scbv_step t1 t1' ->
    closed_term t1 ->
    [ ρ ⊨ t1' ≡ t2 : T ] ->
    [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  eauto using backstep_reducible_aux_1.
Qed.

Lemma star_backstep_reducible_1:
  forall t1 t1' t2 T ρ,
    star scbv_step t1 t1' ->
    valid_interpretation ρ ->
    closed_term t1 ->
    [ ρ ⊨ t1' ≡ t2 : T ] ->
    [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  induction 1; steps; eauto using closed_term_scbv_step, backstep_reducible_1.
Qed.

Lemma backstep_reducible_aux_2:
  forall n ρ t1 t2' T,
    type_nodes T < n ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2' : T ] ->
    forall t2,
      closed_term t2 ->
      scbv_step t2 t2' ->
      [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  unfold reduces_to; steps; eauto 6 with star.
Qed.

Lemma backstep_reducible_2:
  forall ρ t1 t2 t2' T,
    valid_interpretation ρ ->
    scbv_step t2 t2' ->
    closed_term t2 ->
    [ ρ ⊨ t1 ≡ t2' : T ] ->
    [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  eauto using backstep_reducible_aux_2.
Qed.

Lemma star_backstep_reducible_2:
  forall t1 t2 t2' T ρ,
    star scbv_step t2 t2' ->
    valid_interpretation ρ ->
    closed_term t2 ->
    [ ρ ⊨ t1 ≡ t2' : T ] ->
    [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  induction 1; steps; eauto using closed_term_scbv_step, backstep_reducible_2.
Qed.

Lemma backstep_reducible:
  forall ρ t1 t1' t2 t2' T,
    valid_interpretation ρ ->
    scbv_step t1 t1' ->
    scbv_step t2 t2' ->
    closed_term t1 ->
    closed_term t2 ->
    [ ρ ⊨ t1' ≡ t2' : T ] ->
    [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  eauto using backstep_reducible_1, backstep_reducible_2.
Qed.

Lemma star_backstep_reducible:
  forall t1 t1' t2 t2' T ρ,
    star scbv_step t1 t1' ->
    star scbv_step t2 t2' ->
    valid_interpretation ρ ->
    closed_term t1 ->
    closed_term t2 ->
    [ ρ ⊨ t1' ≡ t2' : T ] ->
    [ ρ ⊨ t1 ≡ t2 : T ].
Proof.
  eauto using star_backstep_reducible_1, star_backstep_reducible_2.
Qed.

Lemma reducible_values_exprs:
  forall ρ v1 v2 T T',
    (forall v1 v2, ([ ρ ⊨ v1 ≡ v2 : T ]v -> [ ρ ⊨ v1 ≡ v2 : T' ]v)) ->
    [ ρ ⊨ v1 ≡ v2 : T ] ->
    [ ρ ⊨ v1 ≡ v2 : T' ].
Proof.
  unfold reduces_to; steps; eauto 6.
Qed.

Fixpoint are_values (l: list (nat * tree)) :=
  match l with
  | nil => True
  | (x,v) :: l' => cbv_value v /\ are_values l'
  end.

Lemma reducible_values_list_1:
  forall ρ l1 l2 Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l1 l2 ->
    are_values l1.
Proof.
  induction l1; repeat step || step_inversion satisfies; eauto using red_is_val_1.
Qed.

Hint Immediate reducible_values_list_1: values.

Lemma reducible_values_list_2:
  forall ρ l1 l2 Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l1 l2 ->
    are_values l2.
Proof.
  induction l1; repeat step || step_inversion satisfies; eauto using red_is_val_2.
Qed.

Hint Immediate reducible_values_list_2: values.

Lemma reducible_expr_value:
  forall ρ v1 v2 T,
    cbv_value v1 ->
    cbv_value v2 ->
    [ ρ ⊨ v1 ≡ v2 : T ] ->
    [ ρ ⊨ v1 ≡ v2 : T ]v.
Proof.
  unfold reduces_to; repeat step || t_invert_star.
Qed.

Lemma reducible_wf_1:
  forall ρ t1 t2 T k,
    [ ρ ⊨ t1 ≡ t2 : T ] -> wf t1 k.
Proof.
  unfold reduces_to, closed_term; steps; eauto with wf.
Qed.

Hint Immediate reducible_wf_1: wf.

Lemma reducible_wf_2:
  forall ρ t1 t2 T k,
    [ ρ ⊨ t1 ≡ t2 : T ] -> wf t2 k.
Proof.
  unfold reduces_to, closed_term; steps; eauto with wf.
Qed.

Hint Immediate reducible_wf_2: wf.

Lemma reducible_twf_1:
  forall ρ t1 t2 T k,
    [ ρ ⊨ t1 ≡ t2 : T ] -> twf t1 k.
Proof.
  unfold reduces_to, closed_term; steps; eauto using is_erased_term_twf.
Qed.

Hint Immediate reducible_twf_1: twf.

Lemma reducible_twf_2:
  forall ρ t1 t2 T k,
    [ ρ ⊨ t1 ≡ t2 : T ] -> twf t1 k.
Proof.
  unfold reduces_to, closed_term; steps; eauto using is_erased_term_twf.
Qed.

Hint Immediate reducible_twf_2: twf.

Lemma reducible_fv_1:
  forall ρ t1 t2 T tag, [ ρ ⊨ t1 ≡ t2 : T ] -> pfv t1 tag = nil.
Proof.
  destruct tag; unfold reduces_to, closed_term; steps; eauto using is_erased_term_tfv.
Qed.

Hint Immediate reducible_fv_1: fv.

Lemma reducible_fv_2:
  forall ρ t1 t2 T tag, [ ρ ⊨ t1 ≡ t2 : T ] -> pfv t2 tag = nil.
Proof.
  destruct tag; unfold reduces_to, closed_term; steps; eauto using is_erased_term_tfv.
Qed.

Hint Immediate reducible_fv_2: fv.

Lemma reducible_value_expr:
  forall ρ v1 v2 T,
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v1 ≡ v2 : T ].
Proof.
  unfold reduces_to, closed_term; steps;
    eauto with wf;
    eauto with fv;
    eauto with star;
    eauto with erased.
Qed.
