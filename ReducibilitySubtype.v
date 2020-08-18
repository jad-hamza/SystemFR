Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.
Opaque Nat.eq_dec.

Definition weak_subtype ρ T1 T2 :=
  forall v, [ ρ ⊨ v : T1 ]v -> [ ρ ⊨ v : T2 ]v.

Definition strong_subtype ρ T1 T2 :=
  forall v1 v2, [ ρ ⊨ v1 ≡ v2 : T1 ]v -> [ ρ ⊨ v1 ≡ v2 : T2 ]v.

Definition equivalent_types ρ T1 T2 :=
  forall v1 v2, [ ρ ⊨ v1 ≡ v2 : T1 ]v <-> [ ρ ⊨ v1 ≡ v2 : T2 ]v.

Notation "'[' ρ ⊨ T1 '=:=' T2 ']'" := (equivalent_types ρ T1 T2)
  (ρ at level 60, T1 at level 60, T2 at level 60).

Notation "'[' ρ ⊨ T1 '<:?' T2 ']'" := (weak_subtype ρ T1 T2)
  (ρ at level 60, T1 at level 60, T2 at level 60).

Notation "'[' ρ ⊨ T1 '<:' T2 ']'" := (strong_subtype ρ T1 T2)
  (ρ at level 60, T1 at level 60, T2 at level 60).

Lemma equivalent_types_refl:
  forall ρ T, [ ρ ⊨ T =:= T ].
Proof.
  unfold equivalent_types; steps.
Qed.

Lemma equivalent_types_trans:
  forall ρ T1 T2 T3,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ T2 =:= T3 ] ->
    [ ρ ⊨ T1 =:= T3 ].
Proof.
  unfold equivalent_types; steps; eauto with eapply_any;
    try solve [ eapply_any; rewrite_back_any; auto ].
Qed.

Lemma equivalent_types_sym:
  forall ρ T1 T2,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ T2 =:= T1 ].
Proof.
  unfold equivalent_types; steps; eauto with eapply_any.
Qed.

Lemma strong_subtype_refl:
  forall ρ T, [ ρ ⊨ T <: T ].
Proof.
  unfold strong_subtype; steps.
Qed.

Lemma strong_subtype_trans:
  forall ρ T1 T2 T3,
    [ ρ ⊨ T1 <: T2 ] ->
    [ ρ ⊨ T2 <: T3 ] ->
    [ ρ ⊨ T1 <: T3 ].
Proof.
  unfold strong_subtype; steps; eauto.
Qed.

Lemma weak_subtype_refl:
  forall ρ T, [ ρ ⊨ T <:? T ].
Proof.
  unfold weak_subtype; steps.
Qed.

Lemma weak_subtype_trans:
  forall ρ T1 T2 T3,
    [ ρ ⊨ T1 <:? T2 ] ->
    [ ρ ⊨ T2 <:? T3 ] ->
    [ ρ ⊨ T1 <:? T3 ].
Proof.
  unfold weak_subtype; steps; eauto.
Qed.

Lemma strong_subtype_antisymmetric:
  forall ρ T1 T2,
    [ ρ ⊨ T1 <: T2 ] ->
    [ ρ ⊨ T2 <: T1 ] ->
    [ ρ ⊨ T1 =:= T2 ].
Proof.
  unfold strong_subtype, equivalent_types; steps; eauto.
Qed.

Lemma strong_subtype_weak_subtype:
  forall ρ T1 T2,
    [ ρ ⊨ T1 <: T2 ] ->
    [ ρ ⊨ T1 <:? T2 ].
Proof.
  unfold weak_subtype, strong_subtype; steps.
Qed.

Lemma equivalent_types_strong_subtype_1:
  forall ρ T1 T2,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ T1 <: T2 ].
Proof.
  unfold equivalent_types, strong_subtype; steps; eauto with apply_any.
Qed.

Lemma equivalent_types_strong_subtype_2:
  forall ρ T1 T2,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ T2 <: T1 ].
Proof.
  unfold equivalent_types, strong_subtype; steps; eauto with apply_any.
Qed.

Lemma swap_subtype:
  forall ρ t t' T1 T2,
    [ ρ ⊨ T1 <: T2 ] ->
    [ ρ ⊨ t ≡ t' : T1 ] ->
    [ ρ ⊨ t ≡ t' : T2 ].
Proof.
  unfold strong_subtype; steps; eauto using reducible_values_exprs.
Qed.

Lemma swap_equivalent_types:
  forall ρ t t' T1 T2,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ t ≡ t' : T1 ] ->
    [ ρ ⊨ t ≡ t' : T2 ].
Proof.
  eauto using swap_subtype, equivalent_types_strong_subtype_1.
Qed.

Lemma swap_equivalent_types_back:
  forall ρ t t' T1 T2,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ t ≡ t' : T2 ] ->
    [ ρ ⊨ t ≡ t' : T1 ].
Proof.
  eauto using swap_subtype, equivalent_types_strong_subtype_2.
Qed.

Lemma swap_equivalent_types_values:
  forall ρ t t' T1 T2,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ t ≡ t' : T1 ]v ->
    [ ρ ⊨ t ≡ t' : T2 ]v.
Proof.
  eauto with eapply_any.
Qed.

Lemma swap_equivalent_types_values_back:
  forall ρ t t' T1 T2,
    [ ρ ⊨ T1 =:= T2 ] ->
    [ ρ ⊨ t ≡ t' : T2 ]v ->
    [ ρ ⊨ t ≡ t' : T1 ]v.
Proof.
  eauto with eapply_any.
Qed.
