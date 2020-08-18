Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Export SystemFR.OpenReducibilityDefinition.
Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_lambda:
  forall ρ t1 t2 U V,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf U 0 ->
    wf t1 1 ->
    wf t2 1 ->
    pfv U term_var = nil ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    valid_interpretation ρ ->
    is_erased_type V ->
    (forall u1 u2, reducible_values ρ u1 u2 U ->
              reducible ρ (open 0 t1 u1) (open 0 t2 u2) (open 0 V u1)) ->
    [ ρ ⊨v notype_lambda t1 ≡ notype_lambda t2 : T_arrow U V ].
Proof.
  repeat step || list_utils || simp_red.

  eexists; eexists; repeat step || rewrite reducible_def; t_closer.
Qed.

Lemma open_reducible_lambda:
  forall Θ Γ x t U V,
    wf U 0 ->
    wf t 1 ->
    subset (fv_context Γ) (support Γ) ->
    subset (fv U) (support Γ) ->
    subset (fv t) (support Γ) ->
    ~(x ∈ support Γ) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv V) ->
    is_erased_term t ->
    is_erased_type V ->
    [ Θ; (x, U) :: Γ ⊨ open 0 t (fvar x term_var) : open 0 V (fvar x term_var) ] ->
    [ Θ; Γ ⊨ notype_lambda t : T_arrow U V ].
Proof.
  unfold open_reducible in *; steps.

  apply reducible_value_expr; repeat step; eauto with erased.
  apply reducible_lambda; steps; t_closer.

  unshelve epose proof (H9 ρ ((x, u1) :: l1) ((x, u2) :: l2) _ _ _);
    repeat step || apply SatCons || t_substitutions;
    t_closer.
Qed.

Lemma reducible_app:
  forall ρ U V t1 t2 u1 u2,
    valid_interpretation ρ ->
    is_erased_type V ->
    wf V 1 ->
    pfv V term_var = nil ->
    (forall u1 u2, [ ρ ⊨ u1 ≡ u2 : U ] -> [ ρ ⊨ open 0 V u1 = open 0 V u2 ]) ->
    [ ρ ⊨ t1 ≡ t2 : T_arrow U V ] ->
    [ ρ ⊨ u1 ≡ u2 : U ] ->
    [ ρ ⊨ app t1 u1 ≡ app t2 u2 : open 0 V u1 ].
Proof.
  repeat step || list_utils || simp_red || top_level_unfold reducible || top_level_unfold reduces_to.

  instantiate_reducible; repeat step || rewrite reducible_def in *; t_closer.

  apply star_backstep_reducible with (open 0 t0 v1) (open 0 t3 v2); steps; t_closer;
    eauto 8 using star_trans, star_one with cbvlemmas values smallstep.

  eapply swap_equivalent_types; eauto.
  apply_any.

  exists v0, v3; steps;
  - admit.
  - eapply star_trans; eauto.
    eapply star_trans; eauto with cbvlemmas.
    eapply star_trans; eauto with cbvlemmas values.
    apply star_one. eauto with values smallstep.
    eauto using star_one, star_trans with star cbvlemmas.

  lazymatch goal with
  | H1: forall a, _,
    H2: reducible_values _ ?v _ |- _ =>
    unshelve epose proof (H1 v _ _ _)
  end; steps; unfold closed_value, closed_term in *; repeat step || list_utils;
    eauto with erased wf fv.

  exists v1; repeat step || simp_red;
    eauto using star_trans with cbvlemmas values;
    t_closer;
    eauto using reducibility_values_rtl.
Qed.

Lemma reducible_app2:
  forall ρ e1 e2 U V,
    wf V 0 ->
    valid_interpretation ρ ->
    reducible ρ e1 (T_arrow U V) ->
    reducible ρ e2 U ->
    reducible ρ (app e1 e2) V.
Proof.
  intros; unfold reducible in *; unfold reduces_to in *;
    repeat step || list_utils || simp_red || instantiate_any || unfold reduces_to in *;
      t_closer.

  match goal with
  | H: forall a, _ |- _ => unshelve epose proof (H v _ _ _ _)
  end; steps; eauto with erased wf fv.

  rewrite open_none in *; auto.
  eexists; repeat step || t_closing; eauto;
    eauto using star_trans with cbvlemmas values.
Qed.

Lemma open_reducible_app:
  forall Θ Γ U V t1 t2,
    is_erased_type V ->
    wf V 1 ->
    subset (fv V) (support Γ) ->
    [ Θ; Γ ⊨ t1 : T_arrow U V ] ->
    [ Θ; Γ ⊨ t2 : U ] ->
    [ Θ; Γ ⊨  app t1 t2 : open 0 V t2 ].
Proof.
  unfold open_reducible in *;
    repeat step || t_substitutions;
    eapply reducible_app;
    eauto with erased;
    try solve [ unshelve eauto with wf; auto ];
    eauto with fv.
Qed.
