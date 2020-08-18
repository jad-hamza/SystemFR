Require Export SystemFR.WFLemmasEval.
Require Export SystemFR.FVLemmasEval.

Definition closed_term t :=
  pfv t term_var = nil /\
  wf t 0 /\
  is_erased_term t.

Definition closed_value v :=
  closed_term v /\
  cbv_value v.

Lemma closed_term_scbv_step:
  forall t1 t2,
    closed_term t1 ->
    scbv_step t1 t2 ->
    closed_term t2.
Proof.
  unfold closed_term; steps; eauto with wf erased fv.
Qed.

Lemma twf_open2:
  forall T k i v,
    twf T k ->
    closed_value v ->
    twf (open i T v) k.
Proof.
  unfold closed_value, closed_term; intros; apply twf_open; steps; eauto with twf.
Qed.

Hint Immediate twf_open2: twf.

Lemma is_erased_type_open2:
  forall T i v,
    is_erased_type T ->
    closed_value v ->
    is_erased_type (open i T v).
Proof.
  unfold closed_value, closed_term; intros; apply is_erased_type_open; steps.
Qed.

Hint Immediate is_erased_type_open2: erased.
