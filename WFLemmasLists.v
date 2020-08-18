Require Export SystemFR.TermList.
Require Export SystemFR.WFLemmas.

Lemma satisfies_wfs_1:
  forall R l1 l2 Γ k,
    satisfies R Γ l1 l2 ->
    wfs l1 k.
Proof.
  induction l1;
    repeat step || step_inversion satisfies || apply_any; eauto with wf lia.
Qed.

Hint Immediate satisfies_wfs_1: wf.

Lemma satisfies_wfs_2:
  forall R l1 l2 Γ k,
    satisfies R Γ l1 l2 ->
    wfs l2 k.
Proof.
  induction l1; repeat step || step_inversion satisfies; eauto with wf lia.
Qed.

Hint Immediate satisfies_wfs_2: wf.

Lemma satisfies_twfs_1:
  forall R l1 l2 Γ k,
    satisfies R Γ l1 l2 ->
    twfs l1 k.
Proof.
  induction l1; repeat step || step_inversion satisfies; eauto with twf lia.
Qed.

Hint Immediate satisfies_twfs_1: twf.

Lemma satisfies_twfs_2:
  forall R l1 l2 Γ k,
    satisfies R Γ l1 l2 ->
    twfs l2 k.
Proof.
  induction l1; repeat step || step_inversion satisfies; eauto with twf lia.
Qed.

Hint Immediate satisfies_twfs_2: twf.
