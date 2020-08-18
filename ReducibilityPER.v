Require Import Equations.Equations.
Require Import Equations.Prop.Subterm. (* lexicographic ordering *)

Require Export SystemFR.RedTactics.

Definition reducible_values_sym_prop T : Prop :=
  forall ρ v1 v2,
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v1 : T ]v.

Definition reducible_values_trans_prop T : Prop :=
  forall ρ v1 v2 v3,
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v3 : T ]v ->
    [ ρ ⊨ v1 ≡ v3 : T ]v.

Definition reducible_values_per_prop T : Prop :=
  reducible_values_sym_prop T /\
  reducible_values_trans_prop T.

Lemma reducible_values_sym_inst:
  forall T ρ v1 v2,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v1 : T ]v.
Proof.
  unfold reducible_values_per_prop; steps.
Qed.

Lemma reducible_values_trans_inst:
  forall T ρ v1 v2 v3,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 ≡ v3 : T ]v ->
    [ ρ ⊨ v1 ≡ v3 : T ]v.
Proof.
  unfold reducible_values_per_prop; steps; eauto.
Qed.

Lemma reducible_values_refl_left:
  forall T ρ v1 v2,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v1 : T ]v.
Proof.
  eauto using reducible_values_trans_inst, reducible_values_sym_inst.
Qed.

Lemma reducible_values_refl_right:
  forall T ρ v1 v2,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    [ ρ ⊨ v2 : T ]v.
Proof.
  eauto using reducible_values_trans_inst, reducible_values_sym_inst.
Qed.

Lemma reducible_trans_inst:
  forall T ρ t1 t2 t3,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t2 ≡ t3 : T ] ->
    [ ρ ⊨ t1 ≡ t3 : T ].
Proof.
  unfold reducible_values_per_prop;
  unfold reducible_values_trans_prop, reduces_to;
    repeat step || t_deterministic_star; eauto 6.
Qed.

Lemma reducible_sym_inst:
  forall T ρ t1 t2,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t2 ≡ t1 : T ].
Proof.
  unfold reducible_values_per_prop, reduces_to;
    repeat step || t_deterministic_star; eauto 6.
Qed.

Lemma reducible_refl_left:
  forall T ρ t1 t2,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t1 : T ].
Proof.
  eauto using reducible_trans_inst, reducible_sym_inst.
Qed.

Lemma reducible_refl_right:
  forall T ρ t1 t2,
    reducible_values_per_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ]v ->
    [ ρ ⊨ t2 : T ]v.
Proof.
  eauto using reducible_values_trans_inst, reducible_values_sym_inst.
Qed.

Lemma reducible_values_per_fvar:
  forall m tag x,
    prop_at reducible_values_per_prop m (fvar x tag).
Proof.
  unfold prop_at, reducible_values_per_prop, reducible_values_sym_prop, reducible_values_trans_prop;
    repeat step || destruct_tag || simp_red;
    try solve [ eapply in_valid_interpretation_sym; eauto ];
    try solve [ eapply in_valid_interpretation_trans; eauto ].
Qed.

Ltac setoid_rewrite_all f :=
  match goal with
  | H: _ |- _ => setoid_rewrite f in H
  | _ => setoid_rewrite f
  end.

Lemma reducible_values_per_arrow:
  forall m T1 T2,
    prop_until reducible_values_per_prop m ->
    prop_at reducible_values_per_prop m (T_arrow T1 T2).
Proof.
  intros;
    unfold prop_at, reducible_values_per_prop,
           reducible_values_sym_prop, reducible_values_trans_prop;
    repeat step || simp_red.

  - eexists; eexists; repeat step;
      eapply reducible_sym_inst; eauto 3 using reducible_values_sym_inst with prop_until apply_any.
  - eexists; eexists; repeat step;
      eapply reducible_trans_inst;
        eauto 3 using reducible_values_refl_left, reducible_values_refl_right with prop_until apply_any.
Qed.

Lemma reducible_values_per_prod:
  forall m T1 T2,
    prop_until reducible_values_per_prop m ->
    prop_at reducible_values_per_prop m (T_prod T1 T2).
Proof.
  intros;
    unfold prop_at, reducible_values_per_prop,
           reducible_values_sym_prop, reducible_values_trans_prop;
    repeat step || simp_red.

  - eexists; eexists; eexists; eexists; steps; repeat step;
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

Lemma reducible_values_per:
  forall (m: measure_domain) T, prop_at reducible_values_per_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    steps;
    try solve [
      unfold prop_at, reducible_values_per_prop, reducible_values_sym_prop, reducible_values_trans_prop;
        repeat step || simp_red
    ];
    eauto using reducible_values_per_fvar;
    eauto using reducible_values_per_arrow.
Qed.
