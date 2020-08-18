Require Import Equations.Equations.

Require Export SystemFR.RedTactics.

Definition reducible_values_sym_prop T : Prop :=
  forall ρ v1 v2 v3,
    valid_interpretation ρ ->
    [ ρ ⊨v v1 ≡ v2 : T ] ->
    [ ρ ⊨v v2 ≡ v3 : T ] ->
    [ ρ ⊨v v1 ≡ v3 : T ].

Definition reducible_values_trans_prop T : Prop :=
  forall ρ v1 v2 v3,
    valid_interpretation ρ ->
    [ ρ ⊨v v1 ≡ v2 : T ] ->
    [ ρ ⊨v v2 ≡ v3 : T ] ->
    [ ρ ⊨v v1 ≡ v3 : T ].

Lemma reducible_values_left_inst:
  forall T ρ v1 v2,
    reducible_values_left_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨v v1 ≡ v2 : T ] ->
    [ ρ ⊨v v1 : T ].
Proof.
  unfold reducible_values_left_prop; steps; eauto.
Qed.

Lemma reducible_left_inst:
  forall T ρ t1 t2,
    reducible_values_left_prop T ->
    valid_interpretation ρ ->
    [ ρ ⊨ t1 ≡ t2 : T ] ->
    [ ρ ⊨ t1 : T ].
Proof.
  unfold reducible_values_left_prop, reduces_to; steps; eauto 6.
Qed.

Lemma reducible_values_left_fvar:
  forall m tag x,
    prop_until reducible_values_left_prop m ->
    prop_at reducible_values_left_prop m (fvar x tag).
Proof.
  unfold prop_at, reducible_values_left_prop;
    repeat step || destruct_tag || simp_red;
    try solve [ eapply in_valid_interpretation_refl_left; eauto ].
Qed.

Lemma reducible_values_left_arrow:
  forall m T1 T2,
    prop_until reducible_values_left_prop m ->
    prop_at reducible_values_left_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at, reducible_values_left_prop;
    repeat step. || simp_red.

  eexists; eexists; repeat step || rewrite reducible_def in *.
  eapply reducible_left_inst.

  
  unfold reduces_to in *; steps; t_closer.
  eexists; eexists; steps.
  
  || unfold reduces_to in *.

  

  eapply reducible_values_exprs.
  admit.
  eauto using reducible_values_left_inst.


  try eassumption; steps.
  apply_any.

  || rewrite reducible_def in * || eexists.

  eexists; eexists; steps.
Qed.

Lemma reducible_diagonal_left:
  forall (m: measure_domain) T, prop_at reducible_values_left_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    steps;
    try solve [ unfold prop_at, reducible_values_left_prop; repeat step || simp_red ];
    eauto using reducible_values_left_fvar.

  - unfold prop_at, reducible_values_left_prop; repeat step || simp_red.
  



Lemma reducible_values_left:
  forall ρ v1 v2 T,
    [ ρ ⊨v v1 ≡ v2 : T ] ->
    [ ρ ⊨v v1 : T ].
Proof.
