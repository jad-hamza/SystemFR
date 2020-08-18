Require Import Equations.Equations.

Require Export SystemFR.RedTactics.

Definition reducible_values_trans_prop T : Prop :=
  forall ρ v1 v2 v3,
    valid_interpretation ρ ->
    [ ρ ⊨v v1 ≡ v2 : T ] ->
    [ ρ ⊨v v2 ≡ v3 : T ] ->
    [ ρ ⊨v v1 ≡ v3 : T ].

Lemma reducible_values_trans_inst:
  forall T ρ v1 v2 v3,
    reducible_values_trans_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨v v1 ≡ v2 : T ] ->
    [ ρ ⊨v v2 ≡ v3 : T ] ->
    [ ρ ⊨v v1 ≡ v3 : T ].
Proof.
  unfold reducible_values_trans_prop; steps; eauto.
Qed.

Lemma reducible_trans_inst:
  forall T ρ t1 t2 t3,
    reducible_values_trans_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t2 ≡ t3 : T ] ->
    [ ρ ⊨ t1 ≡ t3 : T ].
Proof.
  unfold reducible_values_trans_prop, reduces_to;
    repeat step || t_deterministic_star; eauto 6.
Qed.

Lemma reducible_values_trans_fvar:
  forall m tag x,
    prop_until reducible_values_trans_prop m ->
    prop_at reducible_values_trans_prop m (fvar x tag).
Proof.
  unfold prop_at, reducible_values_trans_prop;
    repeat step || destruct_tag || simp_red;
    try solve [ eapply in_valid_interpretation_trans; eauto ].
Qed.

Lemma reducible_values_trans_arrow:
  forall m T1 T2,
    prop_until reducible_values_trans_prop m ->
    prop_at reducible_values_trans_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at, reducible_values_trans_prop;
    repeat step || simp_red.

  eexists; eexists; repeat step || rewrite reducible_def in *.

Lemma reducible_values_trans:
  forall (m: measure_domain) T, prop_at reducible_values_trans_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    repeat step;
    try solve [ unfold prop_at, reducible_values_left_prop; repeat step || simp_red ];
    eauto using reducible_values_trans_fvar.
