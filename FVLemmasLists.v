Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.FVLemmas.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.TermList.



Lemma satisfies_closed_mapping_1:
  forall R l1 l2 Γ tag,
    satisfies R Γ l1 l2 ->
    pclosed_mapping l1 tag.
Proof.
  induction l1; destruct tag;
    repeat step || step_inversion satisfies ||
           unfold closed_term in *; eauto.
Qed.

Hint Extern 50 => solve [ eapply satisfies_closed_mapping_1; eassumption ]: fv.

Lemma satisfies_closed_mapping_2:
  forall R l1 l2 Γ tag,
    satisfies R Γ l1 l2 ->
    pclosed_mapping l2 tag.
Proof.
  induction l1; destruct tag;
    repeat step || step_inversion satisfies ||
           unfold closed_term in *; eauto.
Qed.

Hint Extern 50 => solve [ eapply satisfies_closed_mapping_2; eassumption ]: fv.

Lemma closed_mapping_append1:
  forall l1 l2 tag,
    pclosed_mapping (l1 ++ l2) tag ->
    pclosed_mapping l1 tag.
Proof.
  induction l1; steps; eauto.
Qed.

Lemma closed_mapping_append2:
  forall l1 l2 tag,
    pclosed_mapping (l1 ++ l2) tag ->
    pclosed_mapping l2 tag.
Proof.
  induction l1; steps.
Qed.

Hint Extern 50 => solve [ eapply closed_mapping_append1; eauto 1 ]: b_cmap.
Hint Extern 50 => solve [ eapply closed_mapping_append2; eauto 1 ]: b_cmap.

Lemma closed_mapping_append:
  forall l1 l2 tag,
    pclosed_mapping l1 tag ->
    pclosed_mapping l2 tag ->
    pclosed_mapping (l1 ++ l2) tag.
Proof.
  induction l1; steps.
Qed.

Hint Extern 50 => eapply closed_mapping_append: b_cmap.

Lemma satisfies_fv_nil_1:
  forall R Γ l1 l2,
    satisfies R Γ l1 l2 ->
    forall t, t ∈ range l1 -> fv t = nil.
Proof.
  steps.
  eapply closed_mapping_range; eauto.
  eapply satisfies_closed_mapping_1; eauto.
Qed.

Hint Extern 50 => eapply satisfies_fv_nil_1: fv.

Lemma satisfies_fv_nil_2:
  forall R Γ l1 l2,
    satisfies R Γ l1 l2 ->
    forall t, t ∈ range l2 -> fv t = nil.
Proof.
  steps.
  eapply closed_mapping_range; eauto.
  eapply satisfies_closed_mapping_2; eauto.
Qed.

Hint Extern 50 => eapply satisfies_fv_nil_2: fv.

Lemma fv_satisfies_nil_1:
  forall R Γ l1 l2 t,
    satisfies R Γ l1 l2 ->
    subset (fv t) (support Γ) ->
    fv (substitute t l1) = nil.
Proof.
  repeat step || t_termlist || list_utils || apply fv_nils2 || rewrite_any;
    eauto with fv b_cmap.
Qed.

Lemma fv_satisfies_nil_2:
  forall R Γ l1 l2 t,
    satisfies R Γ l1 l2 ->
    subset (fv t) (support Γ) ->
    fv (substitute t l1) = nil.
Proof.
  repeat step || t_termlist || list_utils || apply fv_nils2 || rewrite_any;
    eauto with fv b_cmap.
Qed.

Hint Extern 50 => eapply fv_satisfies_nil_2: fv.

Lemma subset_same_support_1:
  forall R Γ l1 l2 S,
    satisfies R Γ l1 l2 ->
    subset S (support Γ) ->
    subset S (support l1).
Proof.
  repeat step || t_termlist || rewrite_any.
Qed.

Hint Immediate subset_same_support_1: fv.

Lemma subset_same_support_2:
  forall R Γ l1 l2 S,
    satisfies R Γ l1 l2 ->
    subset S (support Γ) ->
    subset S (support l2).
Proof.
  repeat step || t_termlist || rewrite_any.
Qed.

Hint Immediate subset_same_support_2: fv.

Lemma fv_nils3_1:
  forall R Γ t l1 l2,
    is_annotated_term t ->
    subset (pfv t term_var) (support Γ) ->
    satisfies R (erase_context Γ) l1 l2 ->
    pfv (psubstitute (erase_term t) l1 term_var) term_var = nil.
Proof.
  intros.
  apply fv_nils2; eauto with fv.
  eapply subset_same_support_1; eauto;
    repeat step || t_subset_erase || rewrite erased_context_support.
Qed.

Hint Immediate fv_nils3_1: fv.

Lemma fv_nils3_2:
  forall R Γ t l1 l2,
    is_annotated_term t ->
    subset (pfv t term_var) (support Γ) ->
    satisfies R (erase_context Γ) l1 l2 ->
    pfv (psubstitute (erase_term t) l2 term_var) term_var = nil.
Proof.
  intros.
  apply fv_nils2; eauto with fv.
  eapply subset_same_support_2; eauto;
    repeat step || t_subset_erase || rewrite erased_context_support.
Qed.

Hint Immediate fv_nils3_2: fv.

Lemma fv_subst_different_tag:
  forall t l tag tag',
    pclosed_mapping l tag ->
    tag <> tag' ->
    pfv (psubstitute t l tag') tag = pfv t tag.
Proof.
  induction t; repeat step || f_equal; eauto with fv.
Qed.

Lemma pfv_in_subst:
  forall (T : tree) (l : list (nat * tree)) (tag1 tag2 : fv_tag) (X : nat),
    pclosed_mapping l tag1 ->
    X ∈ pfv (psubstitute T l tag2) tag1->
    X ∈ pfv T tag1.
Proof.
  destruct tag1, tag2; repeat step || rewrite fv_subst_different_tag in * by steps.
  - epose proof (fv_subst2 _ _ _ X H0);
    repeat step || list_utils;
    eauto using closed_mapping_fv with exfalso.
  - epose proof (fv_subst2 _ _ _ X H0);
    repeat step || list_utils;
    eauto using closed_mapping_fv with exfalso.
Qed.

Ltac t_pfv_in_subst :=
  match goal with
  | H: _ ∈ pfv (psubstitute _ _ _) _ |- _ =>
      poseNew (Mark H "pfv_in_subst");
      unshelve epose proof (pfv_in_subst _ _ _ _ _ _ H)
  end.
