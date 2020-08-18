Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque Nat.eq_dec.
Opaque makeFresh.

Lemma reducible_ext_pair:
  forall ρ A B v,
    cbv_value v ->
    valid_interpretation ρ ->
    reducible ρ (pi1 v) A ->
    reducible ρ (pi2 v) (open 0 B (pi1 v)) ->
    is_erased_type B ->
    wf B 1 ->
    pfv B term_var = nil ->
    exists a b,
      v = pp a b /\
      reducible_values ρ a A /\
      reducible_values ρ b (open 0 B a).
Proof.
  repeat step || unfold reduces_to in * || values_info || t_invert_star ||
             t_deterministic_star ||
             match goal with
              | H1: cbv_value ?v,
                H2: star scbv_step (pi1 ?t) ?v |- _ =>
                poseNew (Mark H2 "inv pi1");
                unshelve epose proof (star_smallstep_pi1_inv _ v H2 H1 t eq_refl)
              | H1: cbv_value ?v,
                H2: star scbv_step (pi2 ?t) ?v |- _ =>
                poseNew (Mark H2 "inv pi2");
                unshelve epose proof (star_smallstep_pi2_inv _ v H2 H1 t eq_refl)
              end.

  eexists; eexists; steps; eauto.
  eapply reducibility_values_ltr; eauto; repeat step || list_utils;
    eauto with wf;
    eauto with fv;
    eauto with erased.
Qed.

Lemma subtype_prod2:
  forall ρ Γ l A B T v x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv T) ->
    valid_interpretation ρ ->
    open_reducible (support ρ) ((x, T) :: Γ) (pi1 (fvar x term_var)) A ->
    open_reducible (support ρ)
                   ((x, T) :: Γ) (pi2 (fvar x term_var)) (open 0 B (pi1 (fvar x term_var))) ->
    satisfies (reducible_values ρ) Γ l ->
    is_erased_type B ->
    wf B 1 ->
    subset (fv B) (support Γ) ->
    reducible_values ρ v (substitute T l) ->
    reducible_values ρ v (T_prod (substitute A l) (substitute B l)).
Proof.
  repeat step || simp_red || rewrite reducible_def ;
    eauto using red_is_val, values_normalizing with wf fv;
    t_closer.

  unfold open_reducible in *.

  unshelve epose proof (H4 ρ ((x,v) :: l) _ _ _) as HP1;
  unshelve epose proof (H5 ρ ((x,v) :: l) _ _ _) as HP2;
    repeat step || list_utils || apply SatCons || t_substitutions;
    eauto with fv wf erased twf.
  unshelve epose proof reducible_ext_pair _ _ _ _ _ _ HP1 HP2 _ _ _; steps;
    eauto with values;
    eauto with fv;
    try solve [ unshelve eauto with wf; auto ].
  unshelve exists a, b; steps; eauto with erased wf fv.
Qed.

Lemma reducible_values_prod_subtype:
  forall ρ A1 A2 B1 B2 t,
    valid_interpretation ρ ->
    (forall a t, reducible_values ρ a A1 ->
        reducible_values ρ t (open 0 A2 a) ->
        reducible_values ρ t (open 0 B2 a)
    ) ->
   (forall t, reducible_values ρ t A1 -> reducible_values ρ t B1) ->
   is_erased_type B2 ->
   reducible_values ρ t (T_prod A1 A2) ->
   reducible_values ρ t (T_prod B1 B2).
Proof.
  repeat step || simp_red || rewrite reducible_def in *;
    eauto using reducible_values_exprs.
  eexists; eexists; steps; eauto.
Qed.

Lemma reducible_prod_subtype_subst:
  forall ρ A1 A2 B1 B2 t x l Γ,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A1) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    (forall t l,
       satisfies (reducible_values ρ) ((x, A1) :: Γ) l ->
       reducible_values ρ t (substitute (open 0 A2 (fvar x term_var)) l) ->
       reducible_values ρ t (substitute (open 0 B2 (fvar x term_var)) l)) ->
    (forall t, reducible_values ρ t (substitute A1 l) -> reducible_values ρ t (substitute B1 l)) ->
    is_erased_type B2 ->
    reducible_values ρ t (T_prod (substitute A1 l) (substitute A2 l)) ->
    reducible_values ρ t (T_prod (substitute B1 l) (substitute B2 l)).
Proof.
  intros.
  apply reducible_values_prod_subtype with (substitute A1 l) (substitute A2 l);
      steps; eauto with erased.
  unshelve epose proof (H6 t0 ((x,a) :: l) _ _);
    repeat step || list_utils || apply SatCons || t_substitutions;
    t_closer;
    eauto with twf.
Qed.
