Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque Nat.eq_dec.
Opaque makeFresh.

Lemma subtype_arrow2:
  forall Θ ρ x f Γ l A B T v,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv T) ->
    ~(f ∈ fv_context Γ) ->
    ~(f ∈ fv A) ->
    ~(f ∈ fv B) ->
    ~(f ∈ fv T) ->
    ~(x = f) ->
    is_erased_type B ->
    open_reducible Θ ((x, A) :: (f, T) :: Γ)
                   (app (fvar f term_var) (fvar x term_var))
                   (open 0 B (fvar x term_var)) ->
    valid_interpretation ρ ->
    support ρ = Θ ->
    satisfies (reducible_values ρ) Γ l ->
    reducible_values ρ v (substitute T l) ->
    reducible_values ρ v (T_arrow (substitute A l) (substitute B l)).
Proof.
  repeat step || simp_red || rewrite reducible_def ;
    eauto using red_is_val, values_normalizing with wf fv;
    eauto 3 with erased;
    eauto using reducible_values_closed.
  unfold open_reducible in *.
  unshelve epose proof (H9 ρ ((x,a) :: (f,v) :: l) _ _ _);
    repeat step || list_utils || apply SatCons || t_substitutions;
    eauto with fv wf erased twf.
Qed.

Lemma reducible_values_refine_subtype:
  forall ρ A p q v,
    wf p 1 ->
    wf q 1 ->
    is_erased_term q ->
    pfv q term_var = nil ->
    star scbv_step (open 0 q v) ttrue ->
    reducible_values ρ v (T_refine A p) ->
    reducible_values ρ v (T_refine A q).
Proof.
  repeat step || simp_red.
Qed.

Lemma reducible_values_arrow_subtype:
  forall ρ A1 A2 B1 B2 t,
    valid_interpretation ρ ->
    (forall a t, reducible_values ρ a B1 ->
        reducible_values ρ t (open 0 A2 a) ->
        reducible_values ρ t (open 0 B2 a)
    ) ->
   (forall t, reducible_values ρ t B1 -> reducible_values ρ t A1) ->
   is_erased_type B2 ->
   reducible_values ρ t (T_arrow A1 A2) ->
   reducible_values ρ t (T_arrow B1 B2).
Proof.
  repeat step || simp_red || unfold reduces_to || list_utils;
    t_closer.
    match goal with
    | H: forall a, _ |- _ =>
      unshelve epose proof (H a _ _ _ _); repeat step || unfold reduces_to in *; eauto
    end.
Qed.

Lemma reducible_arrow_subtype_subst:
  forall ρ A1 A2 B1 B2 t l Γ x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    (forall t l,
       satisfies (reducible_values ρ) ((x, B1) :: Γ) l ->
       reducible_values ρ t (substitute (open 0 A2 (fvar x term_var)) l) ->
       reducible_values ρ t (substitute (open 0 B2 (fvar x term_var)) l)) ->
    (forall t, reducible_values ρ t (substitute B1 l) -> reducible_values ρ t (substitute A1 l)) ->
    is_erased_type B2 ->
    reducible_values ρ t (T_arrow (substitute A1 l) (substitute A2 l)) ->
    reducible_values ρ t (T_arrow (substitute B1 l) (substitute B2 l)).
Proof.
  intros.
  apply reducible_values_arrow_subtype with (substitute A1 l) (substitute A2 l);
      steps; eauto with erased.
  unshelve epose proof (H5 t0 ((x,a) :: l) _ _);
    repeat step || list_utils || apply SatCons || t_substitutions;
    eauto with fv wf erased twf.
Qed.
