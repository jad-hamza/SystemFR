Require Import Relations.

Require Export SystemFR.Tactics.

Arguments same_relation { A }.

Lemma same_relation_refl:
  forall A (R: relation A), same_relation R R.
Proof.
  unfold same_relation; steps.
Qed.

Lemma same_relation_left:
  forall A (R1 R2: relation A) v v',
    same_relation R1 R2 ->
    R1 v v' ->
    R2 v v'.
Proof.
  unfold same_relation; intros; apply_any; assumption.
Qed.

Hint Extern 1 => eapply same_relation_left: same_relation_left.

Lemma same_relation_right:
  forall A (R1 R2: relation A) v v',
    same_relation R1 R2 ->
    R2 v v' ->
    R1 v v'.
Proof.
  unfold same_relation; intros; apply_any; assumption.
Qed.

Hint Extern 1 => eapply same_relation_right: same_relation_right.

Lemma same_relation_sym:
  forall A (R1 R2: relation A), same_relation R1 R2 -> same_relation R2 R1.
Proof.
  unfold same_relation; repeat step || apply_any.
Qed.
