Require Import Equations.Equations.
Require Import Equations.Prop.Subterm. (* lexicographic ordering *)

Require Export SystemFR.RedTactics.

Definition reducible_values_sym_prop T : Prop :=
  forall ρ v1 v2,
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v1 : T ]v.

Lemma reducible_values_sym_inst:
  forall T ρ v1 v2,
    reducible_values_sym_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v1 : T ]v.
Proof.
  unfold reducible_values_sym_prop; steps.
Qed.

Lemma reducible_sym_inst:
  forall T ρ t1 t2,
    reducible_values_sym_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t2 ≡ t1 : T ].
Proof.
  unfold reducible_values_sym_prop, reduces_to;
    repeat step || t_deterministic_star; eauto 6.
Qed.

Lemma reducible_values_sym_fvar:
  forall m tag x,
    prop_at reducible_values_sym_prop m (fvar x tag).
Proof.
  unfold prop_at, reducible_values_sym_prop;
    repeat step || destruct_tag || simp_red;
    try solve [ eapply in_valid_interpretation_sym; eauto ];
    try solve [ eapply in_valid_interpretation_trans; eauto ].
Qed.

Lemma reducible_values_sym_arrow:
  forall m T1 T2,
    prop_until reducible_values_sym_prop m ->
    prop_at reducible_values_sym_prop m (T_arrow T1 T2).
Proof.
  intros;
    unfold prop_at, reducible_values_sym_prop;
    repeat step || simp_red.

  eexists; eexists; repeat step;
    eapply reducible_sym_inst; eauto 3 using reducible_values_sym_inst with prop_until apply_any.
Qed.

Lemma reducible_values_sym_prod:
  forall m T1 T2,
    prop_until reducible_values_sym_prop m ->
    prop_at reducible_values_sym_prop m (T_prod T1 T2).
Proof.
  intros;
    unfold prop_at, reducible_values_sym_prop;
    repeat step || simp_red.

  eexists; eexists; eexists; eexists; steps; repeat step;
    eauto 3 using reducible_values_sym_inst with prop_until.
  - eexists; eexists; eexists; eexists; steps; repeat step;
      try solve [
        eapply reducible_values_trans_inst;
          eauto 3 using reducible_values_refl_left, reducible_values_refl_right
                  with prop_until apply_any
      ].

    + eapply reducible_values_trans_inst;
          eauto 3 using reducible_values_refl_left, reducible_values_refl_right
                  with prop_until apply_any.

      eauto 3 using reducible_values_sym_inst with prop_until.
   repeat step;
      eapply reducible_sym_inst; eauto 3 using reducible_values_sym_inst with prop_until apply_any.
  - eexists; eexists; repeat step;
      eapply reducible_trans_inst;
        eauto 3 using reducible_values_refl_left, reducible_values_refl_right with prop_until apply_any.
Qed.

Lemma reducible_values_sym:
  forall (m: measure_domain) T, prop_at reducible_values_sym_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    steps;
    try solve [
      unfold prop_at, reducible_values_sym_prop, reducible_values_sym_prop, reducible_values_trans_prop;
        repeat step || simp_red
    ];
    eauto using reducible_values_sym_fvar;
    eauto using reducible_values_sym_arrow.
Qed.
