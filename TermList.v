Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.Syntax.

Require Export SystemFR.FVLemmas.
Require Export SystemFR.SubstitutionLemmas.

Open Scope list_scope.

Inductive satisfies (R: tree -> tree -> tree -> Prop):
  list (nat * tree) -> (* Γ *)
  list (nat * tree) -> (* l1 *)
  list (nat * tree) -> (* l2 *)
  Prop :=
| SatNil: satisfies R nil nil nil
| SatCons:
    forall x t1 t2 T Γ l1 l2,
      ~(x ∈ fv T) ->
      ~(x ∈ fv_context Γ) ->
      pfv t1 term_var = nil ->
      pfv t2 term_var = nil ->
      pfv t1 type_var = nil ->
      pfv t2 type_var = nil ->
      wf t1 0 ->
      wf t2 0 ->
      twf t1 0 ->
      twf t2 0 ->
      R t1 t2 (substitute T l1) ->
      satisfies R Γ l1 l2 ->
      satisfies R
        ((x, T) :: Γ)
        ((x, t1) :: l1)
        ((x, t2) :: l2).

Lemma satisfies_nodup:
  forall R Γ l1 l2,
    satisfies R Γ l1 l2 ->
    NoDup (support Γ).
Proof.
  induction 1; repeat step; eauto with fv.
Qed.

Ltac satisfies_nodup :=
  match goal with
  | H: satisfies ?R ?G ?L1 ?L2 |- _ =>
    poseNew (Mark (R,G,L1,L2) "satisfies_nodup");
    pose proof (satisfies_nodup _ _ _ _ H)
  end.

Lemma satisfies_lookup:
  forall R Γ l1 l2,
    satisfies R Γ l1 l2 ->
    forall x t1 t2 T,
      lookup Nat.eq_dec Γ x = Some T ->
      lookup Nat.eq_dec l1 x = Some t1 ->
      lookup Nat.eq_dec l2 x = Some t2 ->
      R t1 t2 (substitute T l1).
Proof.
  induction 1; steps; eauto.
  - rewrite substitute_nothing2; eauto.
  - rewrite substitute_cons; eauto.
    apply IHsatisfies with x0; eauto.
    rewrite substitute_nothing; repeat step; eauto with fv.
Qed.

Lemma satisfies_lookup2:
  forall R Γ l1 l2 x t1 t2 T,
    satisfies R Γ l1 l2 ->
    lookup Nat.eq_dec Γ x = Some T ->
    lookup Nat.eq_dec l1 x = Some t1 ->
    lookup Nat.eq_dec l2 x = Some t2 ->
    R t1 t2 (substitute T l1).
Proof.
  intros; eapply satisfies_lookup; eauto.
Qed.

Lemma satisfies_same_support1:
  forall R Γ l1 l2,
    satisfies R Γ l1 l2 ->
    support Γ = support l1.
Proof.
  induction 1; steps.
Qed.

Lemma satisfies_same_support2:
  forall R Γ l1 l2,
    satisfies R Γ l1 l2 ->
    support Γ = support l2.
Proof.
  induction 1; steps.
Qed.

Ltac t_instantiate_sat :=
  match goal with
  | H1: forall lterms, satisfies ?P ?G lterms -> _,
    H2: satisfies ?P ?G _ |- _ =>
      pose proof (H1 _ H2); clear H1
  | H1: forall g lterms, satisfies ?P _ lterms -> _,
    H2: satisfies ?P _ _ |- _ =>
      pose proof (H1 _ _ H2); clear H1
end.

Ltac t_termlist :=
  match goal with
  | _ => t_instantiate_sat
  | H: satisfies ?R ?G ?l1 ?l2 |- _ =>
      poseNew (Mark (G,l1,l2) "same support1");
      pose proof (satisfies_same_support1 _ _ _ _ H)
  | H: satisfies ?R ?G ?l1 ?l2 |- _ =>
      poseNew (Mark (G,l1,l2) "same support2");
      pose proof (satisfies_same_support2 _ _ _ _ H)
  | H1: lookup _ ?g ?x = Some ?T,
    H2: lookup _ ?l1 ?x = Some ?t1,
    H3: lookup _ ?l2 ?x = Some ?t2,
    H4: satisfies ?R ?g ?l1 ?l2 |- _ =>
      poseNew (Mark (R,T,l1,l2) "satisfies");
      pose proof (satisfies_lookup _ _ _ _ H3 _ _ _ _ H1 H2 H3)
  end.

Lemma satisfies_cut:
  forall R Γ1 Γ2 l l',
    satisfies R (Γ1 ++ Γ2) l l' ->
    exists l1 l2 l1' l2',
      l = l1 ++ l2 /\
      l' = l1' ++ l2' /\
      support Γ1 = support l1 /\
      support Γ1 = support l1' /\
      support Γ2 = support l2 /\
      support Γ2 = support l2' /\
      satisfies R Γ2 l2 l2'.
Proof.
  induction Γ1; destruct l; destruct l';
    repeat step || step_inversion satisfies.
  - exists nil, nil, nil, nil; steps.
  - exists nil, ((n,t0) :: l), nil, ((n,t) :: l');
      repeat step || t_termlist || apply SatCons;  eauto with btermlist.
  - instantiate_any; steps.
    exists ((n0, t1) :: l1), l2, ((n0, t0) :: l1'), l2'; repeat step.
Qed.

Ltac satisfies_cut :=
  match goal with
  | H: satisfies ?R (?G1 ++ ?G2) ?L ?L' |- _ =>
    poseNew (Mark (R,G1,G2,L,L') "satisfies_cut");
    pose proof (satisfies_cut _ _ _ _ _ H)
  end.

Lemma satisfies_fair_split:
  forall R Γ1 Γ2 l1 l2 x t T l',
    satisfies R (Γ1 ++ (x, T) :: Γ2) (l1 ++ (x, t) :: l2) l' ->
    support Γ1 = support l1.
Proof.
  induction Γ1; destruct l1;
    repeat
      step || step_inversion satisfies ||
      satisfies_nodup || rewrite support_append in * || t_equality ||
      t_termlist || rewrite fv_context_append in * || list_utils;
      eauto.

  exfalso. apply H7.
  apply fv_context_support.
  repeat rewrite_any; auto using in_middle.
Qed.

Lemma x_not_in_support:
  forall R Γ1 Γ2 l l' x T,
    satisfies R (Γ1 ++ (x, T) :: Γ2) l l' ->
    x ∈ support Γ1 ->
    False.
Proof.
  repeat step || satisfies_nodup || rewrite support_append in *;
    eauto using NoDup_append with step_tactic.
Qed.

Hint Immediate x_not_in_support: fv.

Lemma x_not_in_support2:
  forall P Γ l1 l2 l' x t,
    satisfies P Γ (l1 ++ (x, t) :: l2) l' ->
    x ∈ support l1 ->
    False.
Proof.
  intros.
  satisfies_nodup.
  erewrite satisfies_same_support1 in H1; try eassumption.
  rewrite support_append in *;
    eauto using NoDup_append with step_tactic.
Qed.

Hint Immediate x_not_in_support2: fv.

Lemma satisfies_y_in_support:
  forall R Γ1 Γ2 l1 l2 l' x y t T,
    satisfies R (Γ1 ++ (x, T) :: Γ2) (l1 ++ (x, t) :: l2) l' ->
    y ∈ support l1 ->
    y ∈ support Γ1.
Proof.
  intros.
  erewrite satisfies_fair_split; eauto.
Qed.

Hint Immediate satisfies_y_in_support: fv.
