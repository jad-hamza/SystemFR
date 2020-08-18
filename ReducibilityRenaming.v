Require Import Relations.
Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Require Export SystemFR.IdRelation.
Require Export SystemFR.RedTactics.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.
Opaque lt.

Definition renamable_values_prop T: Prop :=
  forall T' v1 v2 ρ ρ' rel,
    equivalent_with_relation rel ρ ρ' same_relation ->
    equal_with_relation type_var rel T T' ->
      [ ρ ⊨ v1 ≡ v2 : T ]v <->
      [ ρ' ⊨ v1 ≡ v2 : T' ]v.

Lemma renamable_values_inst:
  forall ρ ρ' rel A A' v1 v2,
    renamable_values_prop A ->
    equal_with_relation type_var rel A A' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ ⊨ v1 ≡ v2 : A ]v ->
    [ ρ' ⊨ v1 ≡ v2 : A' ]v.
Proof.
  unfold renamable_values_prop; repeat step || eapply_any.
Qed.

Lemma renamable_values_inst_back:
  forall ρ ρ' rel A A' v1 v2,
    renamable_values_prop A ->
    equal_with_relation type_var rel A A' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ' ⊨ v1 ≡ v2 : A' ]v ->
    [ ρ ⊨ v1 ≡ v2 : A ]v.
Proof.
  unfold renamable_values_prop; repeat step || eapply_any.
Qed.

Lemma renamable_inst:
  forall ρ ρ' rel A A' t1 t2,
    renamable_values_prop A ->
    equal_with_relation type_var rel A A' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ ⊨ t1 ≡ t2 : A ] ->
    [ ρ' ⊨ t1 ≡ t2 : A' ].
Proof.
  unfold reduces_to; repeat step || eexists || eauto using renamable_values_inst.
Qed.

Lemma renamable_inst_back:
  forall ρ ρ' rel A A' t1 t2,
    renamable_values_prop A ->
    equal_with_relation type_var rel A A' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ' ⊨ t1 ≡ t2 : A' ] ->
    [ ρ ⊨ t1 ≡ t2 : A ].
Proof.
  unfold reduces_to; repeat step || eexists || eauto using renamable_values_inst_back.
Qed.

Lemma renamable_values_inst_open:
  forall ρ ρ' rel B B' v1 v2 a,
    renamable_values_prop (open 0 B a) ->
    equal_with_relation type_var rel B B' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ ⊨ v1 ≡ v2 : open 0 B a ]v ->
    is_erased_term a ->
    [ ρ' ⊨ v1 ≡ v2 : open 0 B' a ]v.
Proof.
  unfold renamable_values_prop;
    repeat step || eapply_any || apply equal_with_relation_open2 || apply equal_with_relation_refl;
    eauto with fv.
Qed.

Lemma renamable_values_inst_open_back:
  forall ρ ρ' rel B B' v1 v2 a,
    renamable_values_prop (open 0 B a) ->
    equal_with_relation type_var rel B B' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ' ⊨ v1 ≡ v2 : open 0 B' a ]v ->
    is_erased_term a ->
    [ ρ ⊨ v1 ≡ v2 : open 0 B a ]v.
Proof.
  unfold renamable_values_prop;
    repeat step || eapply_any || apply equal_with_relation_open2 || apply equal_with_relation_refl;
    eauto with fv.
Qed.

Lemma renamable_inst_open:
  forall ρ ρ' rel B B' t1 t2 a,
    renamable_values_prop (open 0 B a) ->
    equal_with_relation type_var rel B B' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ ⊨ t1 ≡ t2 : open 0 B a ] ->
    is_erased_term a ->
    [ ρ' ⊨ t1 ≡ t2 : open 0 B' a ].
Proof.
  unfold reduces_to; repeat step || eexists || eauto using renamable_values_inst_open.
Qed.

Lemma renamable_inst_open_back:
  forall ρ ρ' rel B B' t1 t2 a,
    renamable_values_prop (open 0 B a) ->
    equal_with_relation type_var rel B B' ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    [ ρ' ⊨ t1 ≡ t2 : open 0 B' a ] ->
    is_erased_term a ->
    [ ρ ⊨ t1 ≡ t2 : open 0 B a ].
Proof.
  unfold reduces_to; repeat step || eexists || eauto using renamable_values_inst_open_back.
Qed.

Ltac t_inst :=
  eapply renamable_values_inst; eauto 1; eauto 1 with prop_until.

Ltac t_inst_back :=
  eapply renamable_values_inst_back; eauto 1; eauto 1 with prop_until.

Ltac t_inst_open :=
  unfold closed_value, closed_term in *; steps;
    eapply renamable_values_inst_open; eauto 1; eauto 1 with prop_until; t_closer.

Ltac t_inst_open_back :=
  unfold closed_value, closed_term in *; steps;
    eapply renamable_values_inst_open_back; eauto 1; eauto 1 with prop_until; t_closer.

Ltac t_inst_solve :=
  solve [ t_inst ] ||
  solve [ t_inst_back ] ||
  solve [ t_inst_open ] ||
  solve [ t_inst_open_back ].

Ltac t_prove_reduces_to :=
  match goal with
  | H: forall a, _ -> _ -> reduces_to _ _ _ |- _ => apply H; eauto; [ idtac ]
  | H: forall a, _ -> _ -> reduces_to _ _ _ |- _ => apply H; eauto; fail
  end.

Lemma reducible_rename_fvar: forall m n f, prop_at renamable_values_prop m (fvar n f).
Proof.
  unfold prop_at, renamable_values_prop; intros.
  force_invert equal_with_relation;
      repeat step || destruct_tag || simp_red || t_lookup || t_lookup_same || t_instantiate_rel;
      try solve [ eapply same_relation_left; eauto 1 ];
      try solve [ eapply same_relation_right; eauto 1 ].
Qed.

Hint Immediate reducible_rename_fvar: b_rename.

Lemma reducible_rename_arrow:
  forall m T1 T2,
    prop_until renamable_values_prop m ->
    prop_at renamable_values_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at, get_measure; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation;
    eauto 2 with erased.

  - eexists; eexists; steps.
    + eapply renamable_inst_open; eauto; eauto with prop_until apply_any; t_closer.
      apply_any; steps; try solve [ t_inst_back ].

  - eexists; eexists; steps.
    + eapply renamable_inst_open_back; eauto; eauto with prop_until apply_any; t_closer.
      apply_any; steps; try solve [ t_inst ].
Qed.

Hint Immediate reducible_rename_arrow: b_rename.

Lemma reducible_rename_prod: forall m T1 T2, prop_until renamable_values_prop m -> prop_at renamable_values_prop m (T_prod T1 T2).
Proof.
  unfold prop_at, get_measure; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation || (repeat eexists; steps);
    t_closer;
    try t_inst_solve.
Qed.

Hint Immediate reducible_rename_prod: b_rename.

Lemma reducible_rename_sum:
  forall m T1 T2,
    prop_until renamable_values_prop m ->
    prop_at renamable_values_prop m (T_sum T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation;
    try solve [ left; find_exists2; t_inst_solve ];
    try solve [ right; find_exists2; t_inst_solve ].
Qed.

Hint Immediate reducible_rename_sum: b_rename.

Lemma reducible_rename_refine: forall m T b, prop_until renamable_values_prop m -> prop_at renamable_values_prop m (T_refine T b).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_inst_solve || equal_with_erased.
Qed.

Hint Immediate reducible_rename_refine: b_rename.

Lemma reducible_rename_type_refine:
  forall m T1 T2, prop_until renamable_values_prop m -> prop_at renamable_values_prop m (T_type_refine T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_inst_solve || (exists p1, p2);
  eauto 2 with erased.
Qed.

Hint Immediate reducible_rename_type_refine: b_rename.

Lemma reducible_rename_intersection: forall m T1 T2, prop_until renamable_values_prop m -> prop_at renamable_values_prop m (T_intersection T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_inst_solve.
Qed.

Hint Immediate reducible_rename_intersection: b_rename.

Lemma reducible_rename_clos_trans_union_1:
  forall T1 T2 v1 v2 ρ ρ' rel A' B',
    clos_trans_1n tree (fun v1' v2' : tree => [ρ ⊨ v1' ≡ v2' : T1 ]v \/ [ρ ⊨ v1' ≡ v2' : T2 ]v) v1 v2 ->
    prop_until renamable_values_prop (get_measure (T_union T1 T2)) ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    equal_with_relation type_var rel T1 A' ->
    equal_with_relation type_var rel T2 B' ->
    clos_trans_1n tree (fun v1' v2' : tree => [ρ' ⊨ v1' ≡ v2' : A' ]v \/ [ρ' ⊨ v1' ≡ v2' : B' ]v) v1 v2.
Proof.
  induction 1; steps.
  - apply t1n_step; left; t_inst_solve.
  - apply t1n_step; right; t_inst_solve.
  - apply Relation_Operators.t1n_trans with y; steps; left; t_inst_solve.
  - apply Relation_Operators.t1n_trans with y; steps; right; t_inst_solve.
Qed.

Lemma reducible_rename_clos_trans_union_2:
  forall T1 T2 v1 v2 ρ ρ' rel A' B',
    clos_trans_1n tree (fun v1' v2' : tree => [ρ' ⊨ v1' ≡ v2' : A' ]v \/ [ρ' ⊨ v1' ≡ v2' : B' ]v) v1 v2 ->
    prop_until renamable_values_prop (get_measure (T_union T1 T2)) ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    equal_with_relation type_var rel T1 A' ->
    equal_with_relation type_var rel T2 B' ->
    clos_trans_1n tree (fun v1' v2' : tree => [ρ ⊨ v1' ≡ v2' : T1 ]v \/ [ρ ⊨ v1' ≡ v2' : T2 ]v) v1 v2.
Proof.
  induction 1; steps.
  - apply t1n_step; left; t_inst_solve.
  - apply t1n_step; right; t_inst_solve.
  - apply Relation_Operators.t1n_trans with y; steps; left; t_inst_solve.
  - apply Relation_Operators.t1n_trans with y; steps; right; t_inst_solve.
Qed.

Lemma reducible_rename_union: forall m T1 T2,
  prop_until renamable_values_prop m ->
  prop_at renamable_values_prop m (T_union T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
    repeat step || simp_red || step_inversion equal_with_relation;
    eauto 2 using reducible_rename_clos_trans_union_1;
    eauto 2 using reducible_rename_clos_trans_union_2.
Qed.

Hint Immediate reducible_rename_union: b_rename.

Lemma reducible_rename_equal: forall m t1 t2,
  prop_until renamable_values_prop m ->
  prop_at renamable_values_prop m (T_equiv t1 t2).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_inst_solve ||
         unfold equivalent_terms in * || equal_with_erased;
  eauto with apply_any.
Qed.

Hint Immediate reducible_rename_equal: b_rename.

Lemma reducible_rename_forall: forall m T1 T2, prop_until renamable_values_prop m -> prop_at renamable_values_prop m (T_forall T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat step || simp_red || step_inversion equal_with_relation || instantiate_reducible_rel ||
         t_inst_solve;
  eauto 2 with erased;
  eauto 2 with wf.
(*
  - eapply renamable_values_inst_open; eauto; t_closer; eauto with prop_until.
    apply (H5 a1 a2); t_closer; t_inst_solve.
  - eapply renamable_values_inst_open; eauto; t_closer; eauto with prop_until.
    apply (H5 a1 a2); t_closer; t_inst_solve.
  - eapply renamable_values_inst_open_back; eauto; t_closer; eauto with prop_until.
    apply (H6 a1 a2); t_closer; t_inst_solve.
  - eapply renamable_values_inst_open_back; eauto; t_closer; eauto with prop_until.
    apply (H6 a1 a2); t_closer; t_inst_solve. *)
Qed.

Hint Immediate reducible_rename_forall: b_rename.

Lemma reducible_rename_clos_trans_exists_1:
  forall T1 T2 v1 v2 ρ ρ' rel A' B',
    clos_trans_1n tree
      (fun v1' v2' : tree =>
         exists (a1 a2 : tree) (_ : closed_term a1),
           [ρ ⊨ a1 ≡ a2 : T1 ]v /\ [ρ ⊨ v1' ≡ v2' : open 0 T2 a1 ]v) v1 v2 ->
    is_erased_type T2 ->
    prop_until renamable_values_prop (get_measure (T_exists T1 T2)) ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    equal_with_relation type_var rel T1 A' ->
    equal_with_relation type_var rel T2 B' ->
    clos_trans_1n tree
      (fun v1' v2' : tree =>
         exists (a1 a2 : tree) (_ : closed_term a1),
           [ρ' ⊨ a1 ≡ a2 : A' ]v /\ [ρ' ⊨ v1' ≡ v2' : open 0 B' a1 ]v) v1 v2.
Proof.
  induction 1; steps.
  - apply t1n_step; eexists; eexists; steps; try solve [ t_inst_solve ]; auto.
  - apply Relation_Operators.t1n_trans with y; steps;
      eexists; eexists; steps; try solve [ t_inst_solve ]; auto.
Qed.

Lemma reducible_rename_clos_trans_exists_2:
  forall T1 T2 v1 v2 ρ ρ' rel A' B',
    clos_trans_1n tree
      (fun v1' v2' : tree =>
         exists (a1 a2 : tree) (_ : closed_term a1),
           [ρ' ⊨ a1 ≡ a2 : A' ]v /\ [ρ' ⊨ v1' ≡ v2' : open 0 B' a1 ]v) v1 v2 ->
    is_erased_type T2 ->
    prop_until renamable_values_prop (get_measure (T_exists T1 T2)) ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    equal_with_relation type_var rel T1 A' ->
    equal_with_relation type_var rel T2 B' ->
    clos_trans_1n tree
      (fun v1' v2' : tree =>
         exists (a1 a2 : tree) (_ : closed_term a1),
           [ρ ⊨ a1 ≡ a2 : T1 ]v /\ [ρ ⊨ v1' ≡ v2' : open 0 T2 a1 ]v) v1 v2.
Proof.
  induction 1; steps.
  - apply t1n_step; eexists; eexists; steps; try solve [ t_inst_solve ]; auto.
  - apply Relation_Operators.t1n_trans with y; steps;
      eexists; eexists; steps; try solve [ t_inst_solve ]; auto.
Qed.

Lemma reducible_rename_exists: forall m T1 T2,
  prop_until renamable_values_prop m ->
  prop_at renamable_values_prop m (T_exists T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
    repeat step || simp_red || step_inversion equal_with_relation;
    eauto 2 with erased;
    eauto 2 using reducible_rename_clos_trans_exists_1;
    eauto 2 using reducible_rename_clos_trans_exists_2.
Qed.

Hint Immediate reducible_rename_exists: b_rename.

Lemma reducible_rename_type_abs: forall m T,
  prop_until renamable_values_prop m ->
  prop_at renamable_values_prop m (T_abs T).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat match goal with
         | H1: equal_with_relation _ ?rel ?T ?T' |- exists X, (X ∈ ?L -> False) /\ _ =>
             exists (makeFresh (L :: (range rel) :: (range (swap rel)) :: (pfv T type_var) :: (pfv T' type_var) :: nil))
         | _ => step || simp_red || step_inversion equal_with_relation
         end; try finisher.

  - instantiate_any.
    eapply renamable_values_inst; try eassumption;
      repeat step || apply equivalent_with_relation_topen ||
             apply equivalent_with_relation_add || apply equal_with_relation_topen;
      eauto 1 with prop_until;
      eauto 2 using same_relation_refl;
      try finisher.

  - instantiate_any.
    eapply renamable_values_inst_back; try eassumption;
      repeat step || apply equivalent_with_relation_topen ||
             apply equivalent_with_relation_add || apply equal_with_relation_topen;
      eauto 1 with prop_until;
      eauto 2 using same_relation_refl;
      try finisher.
Qed.

Hint Immediate reducible_rename_type_abs: b_rename.

Lemma reducible_rename_rec: forall m n T0 Ts, prop_until renamable_values_prop m -> prop_at renamable_values_prop m (T_rec n T0 Ts).
Proof.
  unfold prop_at; intros; unfold renamable_values_prop;
  repeat match goal with
         | H: star scbv_step _ zero |- _ \/ _ => left
         | H: star scbv_step _ (succ _) |- _ => right
         | _ => step || simp_red || step_inversion equal_with_relation ||
               equal_with_erased || find_exists || t_inst_solve
         end.

  - unshelve eexists n', (makeFresh (pfv T0' type_var :: pfv Ts' type_var ::  support ρ' :: nil)), _, _; eauto;
      repeat step || finisher.
    eapply renamable_values_inst; try eassumption;
      repeat step || unfold same_relation, inclusion ||
             apply equivalent_with_relation_topen ||
             apply equivalent_with_relation_add ||
             apply equal_with_relation_topen;
      eauto 1 with prop_until;
      try finisher.

    + eapply renamable_values_inst; try eassumption;
        repeat step; eauto with prop_until;
          eauto using equal_with_relation_refl with fv equal_with_relation.

    + eapply renamable_values_inst_back; try eassumption;
        repeat step; eauto with prop_until;
          eauto using equal_with_relation_refl with fv equal_with_relation.

  - (* case recursive type at n + 1 *)
   unshelve eexists n'0, (makeFresh (pfv T0 type_var :: pfv Ts type_var :: support ρ :: nil)), _, _; eauto;
      repeat step || finisher.

   eapply renamable_values_inst_back; try eassumption;
     repeat step || unfold same_relation, inclusion ||
            apply equivalent_with_relation_topen ||
            apply equivalent_with_relation_add ||
            apply equal_with_relation_topen;
     eauto 1 with prop_until;
     try finisher.

   + eapply renamable_values_inst; try eassumption;
       repeat step; eauto with prop_until;
         eauto using equal_with_relation_refl with fv equal_with_relation.

   + eapply renamable_values_inst_back; try eassumption;
       repeat step; eauto with prop_until;
         eauto using equal_with_relation_refl with fv equal_with_relation.
Qed.

Hint Immediate reducible_rename_rec: b_rename.

Lemma reducible_rename_aux: forall (m: measure_domain) T, prop_at renamable_values_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 with b_rename;
    try solve [
      unfold prop_at; intros; unfold renamable_values_prop;
      repeat step || simp_red || step_inversion equal_with_relation
    ].
Qed.

Lemma reducible_values_rename :
  forall T T' v1 v2 ρ ρ' rel,
    [ ρ ⊨ v1 ≡ v2 : T ]v ->
    equivalent_with_relation rel ρ ρ' same_relation ->
    equal_with_relation type_var rel T T' ->
    [ ρ' ⊨ v1 ≡ v2 : T' ]v     .
Proof.
  intros; eapply (reducible_rename_aux _ T eq_refl T' v1 v2 ρ ρ' rel);
    eauto 1.
Qed.

Lemma reducible_values_rename_one:
  forall RC ρ v1 v2 T X Y,
    [ (X,RC) :: ρ ⊨ v1 ≡ v2 : topen 0 T (fvar X type_var) ]v ->
    (X ∈ pfv T type_var -> False) ->
    (Y ∈ pfv T type_var -> False) ->
    [ (Y,RC) :: ρ ⊨ v1 ≡ v2 : topen 0 T (fvar Y type_var) ]v.
Proof.
  intros.
  eapply (reducible_values_rename _ _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || t_idrel || t_lookup ||
           apply equivalent_with_relation_add ||
           apply equal_with_relation_topen ||
           apply equal_with_idrel ||
           unfold equivalent_with_relation;
           eauto using equivalent_with_refl, same_relation_refl.
Qed.

Ltac reducible_values_rename_one :=
  match goal with
  | H: [ (?X,?RC) :: ?ρ ⊨ ?v1 ≡ ?v2 : topen 0 ?T (fvar ?X type_var) ]v |-
       [ (?Y,?RC) :: ?ρ ⊨ ?v1 ≡ ?v2 : topen 0 ?T (fvar ?Y type_var) ]v =>
    apply reducible_values_rename_one with X
  end.

Lemma reducible_values_rename_one_rc:
  forall RC RC' ρ v1 v2 T X Y,
    [ (X,RC) :: ρ ⊨ v1 ≡ v2 : topen 0 T (fvar X type_var) ]v ->
    same_relation RC RC' ->
    (X ∈ pfv T type_var -> False) ->
    (Y ∈ pfv T type_var -> False) ->
    [ (Y,RC') :: ρ ⊨ v1 ≡ v2 : topen 0 T (fvar Y type_var) ]v.
Proof.
  intros.
  eapply (reducible_values_rename _ _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || t_idrel || t_lookup ||
           apply equivalent_with_relation_add ||
           apply equal_with_relation_topen ||
           apply equal_with_idrel ||
           unfold equivalent_with_relation;
           eauto using same_relation_refl, equivalent_with_refl.
Qed.

Lemma reducible_values_rename_rc:
  forall RC RC' ρ v1 v2 T X,
    [ (X, RC) :: ρ ⊨ v1 ≡ v2 : topen 0 T (fvar X type_var) ]v ->
    same_relation RC RC' ->
    (X ∈ pfv T type_var -> False) ->
    [ (X, RC') :: ρ ⊨ v1 ≡ v2 : topen 0 T (fvar X type_var) ]v.
Proof.
  eauto using reducible_values_rename_one_rc.
Qed.

Lemma reducible_values_rename_permute:
  forall T ρ1 ρ2 X Y RC v1 v2,
    ~(Y ∈ support ρ1) ->
    ~(X ∈ pfv T type_var) ->
    ~(Y ∈ pfv T type_var) ->
    [ (X, RC) :: ρ1 ++ ρ2 ⊨ v1 ≡ v2 : topen 0 T (fvar X type_var) ]v ->
    [ ρ1 ++ (Y, RC) :: ρ2 ⊨ v1 ≡ v2 : topen 0 T (fvar Y type_var) ]v.
Proof.
  intros.
  eapply (reducible_values_rename _ _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || apply valid_interpretation_append || apply equal_with_relation_topen;
    eauto using equal_with_idrel.

  apply equivalent_with_relation_permute2; steps; eauto using same_relation_refl.
Qed.

Lemma rename_var_arrow:
  forall X Y RC ρ f1 f2 A,
    twf A 0 ->
    ~X ∈ pfv A type_var ->
    ~Y ∈ pfv A type_var ->
    [ (X, RC) :: ρ ⊨ f1 ≡ f2 : T_arrow A (fvar X type_var) ]v <->
    [ (Y, RC) :: ρ ⊨ f1 ≡ f2 : T_arrow A (fvar Y type_var) ]v.
Proof.
  steps.

  - assert (T_arrow A (fvar Y type_var) = topen 0 (T_arrow A (lvar 0 type_var)) (fvar Y type_var))
      as R.
    + repeat step || rewrite topen_none by auto.
    + rewrite R.
      apply reducible_values_rename_one with X;
        repeat step || list_utils || rewrite topen_none in * by auto.

  - assert (T_arrow A (fvar X type_var) = topen 0 (T_arrow A (lvar 0 type_var)) (fvar X type_var))
      as R.
    + repeat step || rewrite topen_none by auto.
    + rewrite R.
      apply reducible_values_rename_one with Y;
        repeat step || list_utils || rewrite topen_none in * by auto.
Qed.
