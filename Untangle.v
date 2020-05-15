Require Import Psatz.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.EquivalentContext.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.FVLemmasClose.
Require Export SystemFR.WFLemmasClose.
Require Export SystemFR.Existss.
Require Export SystemFR.NormalizationPi.
Require Export SystemFR.NormalizationExists.
Require Export SystemFR.NormalizationList.
Require Export SystemFR.TauProperty.

Opaque reducible_values.

Definition incomparable_keys keys : Prop :=
  forall key1 key2, key1 ∈ keys -> key2 ∈ keys ->
    key1 = key2 \/ (~ prefix key1 key2 /\ ~ prefix key2 key1).

Definition apps fs ts := List.map (fun p => app (fst p) (snd p)) (combine fs ts).

Inductive untangle: context -> tree -> tree -> Prop :=
| UntangleFreshen:
    forall Γ T T' template xs ys fs keys m,
      is_erased_type template ->
      wf template 0 ->
      Forall (fun key => [ key : T_key ]v) keys ->
      Forall (fun f => wf f 0) fs ->
      Forall is_erased_term fs ->
      functional (combine ys keys) ->
      functional (combine keys ys) ->
      incomparable_keys keys ->
      ~ m ∈ fv template ->
      length keys = length xs ->
      length fs = length xs ->
      length ys = length xs ->
      (forall f, f ∈ fs -> m ∈ fv f -> False) ->
      (forall y, y ∈ ys -> y ∈ support Γ -> False) ->
      (forall y, y ∈ ys -> y ∈ fv template -> False) ->
      (forall x, x ∈ xs -> x ∈ support Γ -> False) ->
      (forall f, f ∈ fs -> subset (fv f) (support Γ)) ->
      (forall f, f ∈ fs -> [ Γ ⊨ f : T_tau ]) ->
      (forall x, x ∈ fv template -> x ∈ xs \/ x ∈ support Γ) ->
      T  = substitute template
        (List.combine xs (apps fs (List.map (fun key => append_key key (fvar m term_var)) keys))) ->
      T' = substitute template
        (List.combine xs (apps fs (List.map (fun y => fvar y term_var) ys))) ->
      untangle Γ
               (T_exists T_trail (close 0 T m))
               (T_exists_vars ys T_trail T')

| UntangleAbstract:
    forall Γ T A,
      is_erased_type A ->
      is_erased_type T ->
      wf T 1 ->
      wf A 0 ->
      subset (fv A) (support Γ) ->
      subset (fv T) (support Γ) ->
      [ Γ ⊨ tnil : A ] ->
      untangle Γ (T_exists T_trail (shift_open 0 T (tlookup A (lvar 0 term_var)))) (T_exists A T)

| UntanglePi:
    forall Γ S S' T T' x,
      is_erased_type T ->
      is_erased_type T' ->
      wf T 1 ->
      wf T' 1 ->
      subset (fv T) (support Γ) ->
      subset (fv T') (support Γ) ->
      ~ x ∈ pfv S term_var ->
      ~ x ∈ pfv S' term_var ->
      ~ x ∈ pfv_context Γ term_var ->
      untangle Γ S S' ->
      untangle ((x, S') :: Γ) (open 0 T (fvar x term_var)) (open 0 T' (fvar x term_var)) ->
      untangle Γ (T_arrow S T) (T_arrow S' T')

| UntangleExists:
    forall Γ S S' T T' x,
      is_erased_type T ->
      is_erased_type T' ->
      wf T 1 ->
      wf T' 1 ->
      subset (fv T) (support Γ) ->
      subset (fv T') (support Γ) ->
      ~ x ∈ pfv S' term_var ->
      ~ x ∈ pfv_context Γ term_var ->
      untangle Γ S S' ->
      untangle ((x, S') :: Γ) (open 0 T (fvar x term_var)) (open 0 T' (fvar x term_var)) ->
      untangle Γ (T_exists S T) (T_exists S' T')

| UntangleCons:
    forall Γ H H' T T',
      is_erased_type T ->
      is_erased_type T' ->
      wf T 0 ->
      wf T' 0 ->
      untangle Γ H H' ->
      untangle Γ T T' ->
      untangle Γ (Cons H T) (Cons H' T')

| UntangleSingleton:
    forall Γ T T' t,
      untangle Γ T T' ->
      untangle Γ (T_singleton T t) (T_singleton T' t)

| UntangleRefl: forall Γ T, untangle Γ T T
.

Lemma list_map_subst:
  forall l f t m v,
    (forall e, e ∈ l -> m ∈ fv e -> False) ->
    List.map (fun e => app f (pp (psubstitute e ((m, v) :: nil) term_var) t)) l =
    List.map (fun e => app f (pp e t)) l.
Proof.
  induction l; repeat step || t_substitutions || t_equality; eauto.
Qed.

Lemma list_map_subst2:
  forall l f m v,
    (forall e, e ∈ l -> m ∈ fv e -> False) ->
    List.map (fun key => app f (psubstitute (append_key key (fvar m term_var))
                                                     ((m, v) :: nil) term_var)) l =
    List.map (fun key => app f (append_key key v)) l.
Proof.
  induction l; repeat step || t_substitutions || rewrite psubstitute_append_key || t_equality; eauto.
Qed.

Lemma combine_equivalent_wfs1:
  forall ts1 ts2 xs,
    length xs = length ts1 ->
    length xs = length ts2 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    wfs (combine xs ts1) 0.
Proof.
  induction ts1; destruct ts2; destruct xs;
    repeat step || list_utils || list_utils2; eauto.
  unshelve epose proof (H1 a t _); steps; t_closer.
Qed.

Lemma combine_equivalent_wfs2:
  forall ts1 ts2 xs,
    length xs = length ts1 ->
    length xs = length ts2 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    wfs (combine xs ts2) 0.
Proof.
  induction ts1; destruct ts2; destruct xs;
    repeat step || list_utils || list_utils2; eauto.
  unshelve epose proof (H1 a t _); steps; t_closer.
Qed.

Lemma combine_wfs3:
  forall xs ts,
    (forall x t, (x, t) ∈ combine xs ts -> wf t 0) ->
    wfs (combine xs ts) 0.
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma combine_wfs4:
  forall xs ts,
    (forall t, t ∈ ts -> wf t 0) ->
    wfs (combine xs ts) 0.
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma combine_wfs5:
  forall xs ts,
    Forall (fun v => wf v 0) ts ->
    wfs (combine xs ts) 0.
Proof.
  intros; apply combine_wfs4; apply Forall_forall; auto.
Qed.

Lemma combine_equivalent_is_erased_term:
  forall xs ts,
    Forall is_erased_term ts ->
    erased_terms (combine xs ts).
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma combine_closed_mapping:
  forall xs ts tag,
    Forall (fun t => pfv t tag = nil) ts ->
    pclosed_mapping (combine xs ts) tag.
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma reducibility_equivalent_substititions_helper:
  forall xs T ρ v ts1 ts2,
    [ ρ | v : psubstitute T (combine xs ts1) term_var ]v ->
    valid_interpretation ρ ->
    length ts1 = length xs ->
    length ts2 = length xs ->
    is_erased_type T ->
    wf T 0 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    Forall (fun v => wf v 0) ts1 ->
    Forall (fun v => wf v 0) ts2 ->
    Forall (fun v => pfv v term_var = nil) ts1 ->
    Forall (fun v => pfv v term_var = nil) ts2 ->
    Forall is_erased_term ts1 ->
    Forall is_erased_term ts2 ->
    (forall x, x ∈ fv T -> x ∈ xs) ->
    [ ρ | v : psubstitute T (combine xs ts2) term_var ]v.
Proof.
  induction xs; repeat step || t_substitutions.
  rewrite <- (open_close2 T a 0) by auto.
  rewrite substitute_open3; steps;
    try solve [ apply combine_equivalent_wfs4; repeat step || rewrite Forall_forall in *; eauto ];
    try solve [ apply_anywhere fv_close; steps ].

  eapply reducibility_open_equivalent; eauto;
    repeat step || apply subst_erased_type || apply wf_subst || apply wf_close;
    eauto with erased wf fv;
    eauto using combine_equivalent_is_erased_term.

  - rewrite substitute_open2;
      repeat step || list_utils || list_utils2 ||
             rewrite open_close by auto;
      eauto using combine_wfs5.
    apply IHxs with l0;
      repeat step || apply subst_erased_type || apply wf_subst || t_pfv_in_subst;
      eauto.
    + rewrite <- substitute_cons; steps.
    + clear_marked; apply pfv_in_subst2 in H6; steps.
      instantiate_any; steps.
  - apply wfs_monotone2.
    apply combine_wfs4; repeat step || rewrite Forall_forall in *; eauto with wf.
  - apply fv_nils2; repeat step || list_utils2 || unfold subset || apply_anywhere fv_close;
      eauto using combine_closed_mapping.
    apply_anywhere H12; steps.
  - apply combine_wfs5; auto.
Qed.

Lemma reducibility_equivalent_substititions:
  forall xs T ρ v ts1 ts2,
    [ ρ | v : psubstitute T (combine xs ts1) term_var ]v ->
    valid_interpretation ρ ->
    length ts1 = length xs ->
    length ts2 = length xs ->
    is_erased_type T ->
    wf T 0 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    (forall x, x ∈ fv T -> x ∈ xs) ->
    [ ρ | v : psubstitute T (combine xs ts2) term_var ]v.
Proof.
  intros; eapply reducibility_equivalent_substititions_helper; try eassumption;
    repeat step || rewrite Forall_forall || find_fst || find_snd;
    eauto using combine_equivalent_wfs1;
    try solve [ instantiate_any; t_closer ].
Qed.

Lemma erased_terms_combine:
  forall xs f ys,
    is_erased_term f ->
    erased_terms (combine xs (List.map (fun y : nat => app f (fvar y term_var)) ys)).
Proof.
  induction xs; destruct ys; steps.
Qed.

Lemma wfs_combine6:
  forall xs fs keys m,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun t => wf t 0) fs ->
    length keys = length xs ->
    length fs = length xs ->
    wfs
      (combine xs
         (List.map (fun p => app (fst p) (snd p))
            (combine fs (List.map (fun key => append_key key (fvar m term_var)) keys)))) 0.
Proof.
  induction xs; destruct fs; destruct keys;
    repeat step || apply wf_append_key;
    eauto using reducible_val_wf with step_tactic.
Qed.

Lemma wfs_combine7:
  forall xs fs keys m,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun t => wf t 0) fs ->
    length keys = length xs ->
    length fs = length xs ->
    wfs (combine xs (apps fs (List.map (fun key : tree => append_key key (fvar m term_var)) keys))) 0.
Proof.
  induction xs; destruct fs; destruct keys;
    repeat step || apply wf_append_key;
    eauto using reducible_val_wf with step_tactic.
Qed.

Lemma list_map_apps:
  forall fs ts l tag,
    length fs = length ts ->
    List.map (fun t => psubstitute t l tag) (apps fs ts) =
    apps (List.map (fun t => psubstitute t l tag) fs) (List.map (fun t => psubstitute t l tag) ts).
Proof.
  induction fs; destruct ts; repeat step || t_equality; eauto.
Qed.

Lemma apps_cons:
  forall f fs t ts,
    apps (f :: fs) (t :: ts) = app f t :: apps fs ts.
Proof.
  steps.
Qed.

Lemma length_apps_cons:
  forall f fs t ts,
    length (apps (f :: fs) (t :: ts)) = 1 + length (apps fs ts).
Proof.
  repeat step.
Qed.

Opaque apps.

Lemma length_apps:
  forall fs ts,
    length fs = length ts ->
    length (apps fs ts) = length fs.
Proof.
  induction fs; destruct ts; try solve [
    repeat step || rewrite length_apps_cons; try lia
  ].
  intros.
  rewrite length_apps_cons; cbn; apply f_equal; apply_any; steps.
Qed.

Lemma substitute_nothing6:
  forall fs m v,
    (forall f, f ∈ fs -> m ∈ fv f -> False) ->
    List.map (fun t => psubstitute t ((m, v) :: nil) term_var) fs = fs.
Proof.
  induction fs; repeat step || t_substitutions || apply f_equal; eauto.
Qed.

Lemma list_map_subst3:
  forall keys m v,
    Forall (fun key => [ key : T_key ]v) keys ->
    List.map (fun x => psubstitute (append_key x (fvar m term_var)) ((m, v) :: nil) term_var) keys =
    List.map (fun x => append_key x v) keys.
Proof.
  induction keys;
    repeat step || rewrite psubstitute_append_key || t_substitutions.
  rewrite substitute_nothing5; eauto using reducible_val_fv with step_tactic.
  apply f_equal; eauto.
Qed.

Lemma wfs_combine8:
  forall xs fs ys,
    length fs = length xs ->
    length ys = length xs ->
    Forall (fun f => wf f 0) fs ->
    wfs (combine xs (apps fs (List.map (fun y : nat => fvar y term_var) ys))) 0.
Proof.
  induction xs; destruct fs; destruct ys; intros;
    repeat rewrite apps_cons in * || step.
Qed.

Lemma erased_terms_combine2:
  forall xs fs ys,
    length fs = length xs ->
    length ys = length xs ->
    Forall is_erased_term fs ->
    erased_terms (combine xs (apps fs (List.map (fun y => fvar y term_var) ys))).
Proof.
  induction xs; destruct fs; destruct ys; intros;
    repeat rewrite apps_cons in * || step.
Qed.

Lemma erased_terms_combine3:
  forall xs keys fs m,
    length fs = length xs ->
    length keys = length xs ->
    Forall is_erased_term fs ->
    Forall (fun key => [ key : T_key ]v) keys ->
    erased_terms (combine xs (apps fs (List.map (fun key => append_key key (fvar m term_var)) keys))).
Proof.
  induction xs; destruct keys; destruct fs; intros;
    repeat rewrite apps_cons in * || step || apply is_erased_term_append_key;
    try solve [ eapply reducible_values_erased; eauto; steps ].
Qed.

Lemma forall_append_key_trails:
  forall keys trail,
    Forall (fun key => [ key : T_key ]v) keys ->
    [ trail : T_trail ]v ->
    Forall (fun t => [ t : T_trail ]v) (List.map (fun key : tree => append_key key trail) keys).
Proof.
  induction keys; repeat step || constructor; eauto using append_key_trail.
Qed.

Lemma list_map_subst4:
  forall keys a l,
    Forall (fun key : tree => [key : T_key ]v) keys ->
    [ a : T_trail ]v ->
    List.map (fun x => psubstitute (append_key x a) l term_var) keys =
    List.map (fun x => append_key x a) keys.
Proof.
  induction keys; repeat step || t_substitutions || rewrite psubstitute_append_key.
  repeat rewrite substitute_nothing5 by eauto using reducible_val_fv with step_tactic.
  apply f_equal; eauto.
Qed.

Lemma list_map_subst5:
  forall ys l,
    (forall y, y ∈ ys -> y ∈ support l -> False) ->
    List.map (fun x =>
       match lookup PeanoNat.Nat.eq_dec l x with
       | Some e => e
       | None => fvar x term_var
       end) ys =
    List.map (fun x => fvar x term_var) ys.
Proof.
  induction ys; repeat step || t_lookup || apply f_equal; eauto with exfalso.
Qed.

Lemma list_map_subst6:
  forall fs l ys zs,
    (forall f, f ∈ fs -> subset (fv f) (support l)) ->
    pclosed_mapping l term_var ->
    List.map
      (fun f =>
         psubstitute (psubstitute f l term_var)
         (combine ys zs) term_var)
      fs =
    List.map
      (fun f => psubstitute f l term_var)
      fs.
Proof.
  induction fs; repeat step; eauto.
  rewrite substitute_nothing5; eauto with fv.
  apply f_equal; eauto.
Qed.

Lemma list_map_change_list:
  forall A B C (l1: list A) (l2: list B) (f: A -> C) (g: B -> C),
    (forall a b, (a, b) ∈ combine l1 l2 -> f a = g b) ->
    length l1 = length l2 ->
    List.map f l1 = List.map g l2.
Proof.
  induction l1; destruct l2; repeat step || f_equal.
Qed.

Lemma lookup_combine:
  forall A B (l1: list nat) (l2: list A) x a (f: A -> B),
    length l1 = length l2 ->
    functional (combine l1 l2) ->
    (x, a) ∈ combine l1 l2 ->
    lookup Nat.eq_dec (combine l1 (List.map f l2)) x = Some (f a).
Proof.
  induction l1; destruct l2; repeat step || step_inversion NoDup;
    eauto using in_combine_l with exfalso;
    try solve [ eapply_anywhere functional_head; eauto; steps ];
    eauto using functional_tail.
Qed.

Lemma list_map_subst7:
  forall ys keys a,
    length ys = length keys ->
    functional (combine ys keys) ->
    List.map
      (fun y =>
         match
           lookup PeanoNat.Nat.eq_dec
             (combine ys (List.map (fun key => append_key key a) keys)) y
         with
         | Some e1 => e1
         | None => fvar y term_var
         end) ys =
    List.map (fun key => append_key key a) keys.
Proof.
  intros; apply list_map_change_list; repeat step || step_inversion NoDup;
    eauto using in_combine_l with exfalso;
    try solve [ erewrite_anywhere lookup_combine; eauto; steps ].
Qed.

Lemma lookup_combine2:
  forall A B (l1: list nat) (l2: list A) x a (f: A -> B),
    length l1 = length l2 ->
    functional (combine l1 l2) ->
    (x, a) ∈ combine l1 l2 ->
    lookup Nat.eq_dec (combine l1 l2) x = Some a.
Proof.
  induction l1; destruct l2; repeat step || step_inversion NoDup;
    eauto using in_combine_l with exfalso;
    try solve [ eapply_anywhere functional_head; eauto; steps ];
    eauto using functional_tail.
Qed.

Lemma list_map_subst8:
  forall ys vs l,
    length vs = length ys ->
    functional (combine ys vs) ->
    (forall y, y ∈ ys -> y ∈ support l -> False) ->
    List.map
      (fun x =>
       psubstitute
         match lookup Nat.eq_dec l x with
         | Some e => e
         | None => fvar x term_var
         end (combine ys vs) term_var) ys = vs.
Proof.
  intros.
  rewrite <- map_id.
  apply list_map_change_list;
    repeat step || step_inversion NoDup || t_lookup || list_utils2;
    eauto using in_combine_l with exfalso;
    try solve [ erewrite_anywhere lookup_combine2; eauto; steps ].
Qed.

Lemma is_erased_term_global_trail':
  forall keys vs acc0,
    is_erased_term acc0 ->
    Forall is_erased_term keys ->
    Forall is_erased_term vs ->
    is_erased_term (fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0).
Proof.
  induction keys; repeat step || apply_any; eauto with erased.
Qed.

Lemma wfs_global_trail':
  forall keys vs acc0,
    wf acc0 0 ->
    Forall (fun v => wf v 0) keys ->
    Forall (fun v => wf v 0) vs ->
    wf (fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0) 0.
Proof.
  induction keys; repeat step || apply_any; eauto with wf.
Qed.

Lemma fvs_global_trail':
  forall keys vs acc0 tag,
    pfv acc0 tag = nil ->
    Forall (fun v => pfv v tag = nil) keys ->
    Forall (fun v => pfv v tag = nil) vs ->
    pfv (fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0) tag = nil.
Proof.
  induction keys; repeat step || apply_any || rewrite pfv_update || list_utils.
Qed.

Lemma global_trail_is_trail':
  forall keys vs acc0,
    [ acc0 : T_trail ]v  ->
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun trail => [ trail : T_trail ]v) vs ->
    [ fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0 : T_trail ]v.
Proof.
  induction keys; repeat step || apply_any; eauto using update_type.
Qed.

Definition global_trail keys vs :=
  fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) empty_trail.

Lemma is_erased_term_global_trail:
  forall keys vs,
    Forall is_erased_term keys ->
    Forall is_erased_term vs ->
    is_erased_term (global_trail keys vs).
Proof.
  intros; apply is_erased_term_global_trail'; steps;
    try solve [ eapply reducible_values_erased; eauto using empty_trail_type; steps ].
Qed.

Lemma wfs_global_trail:
  forall keys vs,
    Forall (fun v => wf v 0) keys ->
    Forall (fun v => wf v 0) vs ->
    wf (global_trail keys vs) 0.
Proof.
  intros; apply wfs_global_trail'; steps;
    try solve [ eapply reducible_val_wf; eauto using empty_trail_type; steps ].
Qed.

Lemma fvs_global_trail:
  forall keys vs tag,
    Forall (fun v => pfv v tag = nil) keys ->
    Forall (fun v => pfv v tag = nil) vs ->
    pfv (global_trail keys vs) tag = nil.
Proof.
  intros; apply fvs_global_trail'; steps;
    try solve [ eapply reducible_val_fv; eauto using empty_trail_type; steps ].
Qed.

Lemma global_trail_is_trail:
  forall keys vs,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun trail => [ trail : T_trail ]v) vs ->
    [ global_trail keys vs : T_trail ]v.
Proof.
  intros; apply global_trail_is_trail'; steps; eauto using empty_trail_type.
Qed.

Lemma typed_erased_terms:
  forall ρ T l,
    valid_interpretation ρ ->
    Forall (fun v => [ ρ | v : T ]v) l ->
    Forall is_erased_term l.
Proof.
  induction l; repeat step || constructor;
    try solve [ eapply reducible_values_erased; eauto using empty_trail_type; steps ].
Qed.

Lemma typed_erased_terms':
  forall T l,
    Forall (fun v => [ v : T ]v) l ->
    Forall is_erased_term l.
Proof.
  intros; eapply typed_erased_terms; eauto; steps.
Qed.

Lemma typed_wfs:
  forall ρ T l,
    valid_interpretation ρ ->
    Forall (fun v => [ ρ | v : T ]v) l ->
    Forall (fun v => wf v 0) l.
Proof.
  induction l; repeat step || constructor;
    try solve [ eapply reducible_val_wf; eauto using empty_trail_type; steps ].
Qed.

Lemma typed_wfs':
  forall T l,
    Forall (fun v => [ v : T ]v) l ->
    Forall (fun v => wf v 0) l.
Proof.
  intros; eapply typed_wfs; eauto; steps.
Qed.

Lemma typed_fv:
  forall ρ T l tag,
    valid_interpretation ρ ->
    Forall (fun v => [ ρ | v : T ]v) l ->
    Forall (fun v => pfv v tag = nil) l.
Proof.
  induction l; repeat step || constructor;
    try solve [ eapply reducible_val_fv; eauto using empty_trail_type; steps ].
Qed.

Lemma typed_fv':
  forall T l tag,
    Forall (fun v => [ v : T ]v) l ->
    Forall (fun v => pfv v tag = nil) l.
Proof.
  intros; eapply typed_fv; eauto; steps.
Qed.

Lemma fvs_global_trail2:
  forall keys vs tag x,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun trail => [ trail : T_trail ]v) vs ->
    x ∈ pfv (global_trail keys vs) tag ->
    False.
Proof.
  intros; rewrite fvs_global_trail in *; steps; eauto using typed_fv'.
Qed.

Notation "'υ'" := (fun (acc : tree) (p : tree * tree) => update acc (fst p) (snd p))
  (at level 0).

Lemma fold_left_update_move:
  forall keys trails old_trail key0 trail0,
    [ old_trail : T_trail ]v ->
    [ trail0 : T_trail ]v ->
    [ key0 : T_key ]v ->
    Forall (fun trail => [ trail : T_trail ]v) trails ->
    Forall (fun k => [ k : T_key ]v) keys ->
    functional (combine (key0 :: keys) (trail0 :: trails)) ->
    incomparable_keys (key0 :: keys) ->
    fold_left υ (combine keys trails) (update old_trail key0 trail0) =
    update (fold_left υ (combine keys trails) old_trail) key0 trail0.
Proof.
  unfold incomparable_keys; induction keys; destruct trails; repeat step.
  repeat rewrite IHkeys by (steps; eauto using update_type, functional_tail, functional_tail2).
  unshelve epose proof (H5 a key0 _ _); steps; eauto.

  - unfold functional in *; steps.
    unshelve epose proof (H4 key0 trail0 t _ _); steps.

  - apply update_commutative; repeat step || apply global_trail_is_trail'.
Qed.

Definition good_trail (trail: tree) (key: tree) (trail': tree) : Prop :=
  forall f,
    [ f: T_tau ] ->
    [ app f trail' ≡ app f (append_key key trail) ].

Lemma good_trail_equivalent:
  forall key trail trail' f,
    good_trail trail key trail' ->
    [ f : T_tau ] ->
    [ app f trail' ≡ app f (append_key key trail) ].
Proof.
  unfold good_trail; steps.
Qed.

Lemma global_trail_good_trail':
  forall keys trails key0 acc trail0,
    length keys = length trails ->
    Forall (fun trail => [ trail : T_trail ]v) trails ->
    Forall (fun k => [ k : T_key ]v) keys ->
    [ acc : T_trail ]v ->
    (key0, trail0) ∈ combine keys trails ->
    functional (combine keys trails) ->
    incomparable_keys keys ->
    good_trail (fold_left υ (combine keys trails) acc) key0 trail0.
Proof.
  unfold incomparable_keys; unfold good_trail; induction keys; destruct trails; repeat step;
    try solve [ apply_any; steps; eauto using update_type, functional_tail ].
  rewrite fold_left_update_move; steps; eauto using functional_tail.
  apply tau_property; steps;
    eauto using global_trail_is_trail'.
Qed.

Lemma global_trail_good_trail:
  forall keys trails key0 trail0,
    length keys = length trails ->
    Forall (fun trail => [ trail : T_trail ]v) trails ->
    Forall (fun k => [ k : T_key ]v) keys ->
    functional (combine keys trails) ->
    incomparable_keys keys ->
    (key0, trail0) ∈ combine keys trails ->
    good_trail (global_trail keys trails) key0 trail0.
Proof.
  intros; apply global_trail_good_trail'; steps; eauto using empty_trail_type.
Qed.

Opaque global_trail.

Lemma in_combine_equivalent:
  forall fs keys vs t1 l t2 trail,
    length fs = length vs ->
    length fs = length keys ->
    (forall f, f ∈ fs -> [ psubstitute f l term_var : T_tau ]) ->
    (forall key v, (key, v) ∈ combine keys vs -> good_trail trail key v) ->
    (t1, t2) ∈
      combine
        (apps (List.map (fun f => psubstitute f l term_var) fs) vs)
        (apps (List.map (fun f => psubstitute f l term_var) fs)
          (List.map (fun x => append_key x trail) keys)) ->
    [t1 ≡ t2].
Proof.
  induction fs; destruct keys; destruct vs;
    repeat rewrite apps_cons in * || step;
    try solve [ apply IHfs with keys vs l trail; steps ].

  unshelve epose proof (H1 a _); steps.
  unshelve epose proof (H2 t t0 _); steps;
    eauto using good_trail_equivalent.
Qed.

Lemma in_combine_equivalent':
  forall fs keys vs t1 l t2,
    length fs = length vs ->
    length fs = length keys ->
    Forall (fun v => [ v : T_trail ]v) vs ->
    Forall (fun k => [ k : T_key ]v) keys ->
    (forall f, f ∈ fs -> [ psubstitute f l term_var : T_tau ]) ->
    functional (combine keys vs) ->
    incomparable_keys keys ->
    (t1, t2) ∈
      combine
        (apps (List.map (fun f => psubstitute f l term_var) fs) vs)
        (apps (List.map (fun f => psubstitute f l term_var) fs)
          (List.map (fun x => append_key x (global_trail keys vs)) keys)) ->
    [t1 ≡ t2].
Proof.
  intros; apply in_combine_equivalent with fs keys vs l (global_trail keys vs);
    repeat step || apply global_trail_good_trail.
Qed.

Opaque T_trail.
Opaque T_tau.

Lemma untangle_freshen:
  forall Γ fs template xs ys keys m,
    is_erased_type template ->
    wf template 0 ->
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun f => wf f 0) fs ->
    Forall is_erased_term fs ->
    functional (combine ys keys) ->
    functional (combine keys ys) ->
    incomparable_keys keys ->
    ~ m ∈ fv template ->
    length keys = length xs ->
    length fs = length xs ->
    length ys = length xs ->
    (forall f, f ∈ fs -> m ∈ fv f -> False) ->
    (forall y, y ∈ ys -> y ∈ support Γ -> False) ->
    (forall y, y ∈ ys -> y ∈ fv template -> False) ->
    (forall x, x ∈ xs -> x ∈ support Γ -> False) ->
    (forall f, f ∈ fs -> subset (fv f) (support Γ)) ->
    (forall f, f ∈ fs -> [ Γ ⊨ f : T_tau ]) ->
    (forall x, x ∈ fv template -> x ∈ xs \/ x ∈ support Γ) ->
    [Γ
    ⊨ T_exists T_trail
        (close 0
           (psubstitute template
              (List.combine xs
                (apps fs (List.map (fun key => append_key key (fvar m term_var)) keys))) term_var)
            m) =
    T_exists_vars ys T_trail
      (psubstitute template
                   (List.combine xs (apps fs (List.map (fun y => fvar y term_var) ys)))
                   term_var) ].
Proof.
  unfold open_equivalent_types, equivalent_types; intros;
    repeat step || list_utils || list_utils2 || simp_red_top_level_hyp || rewrite substitute_trail in *.

  - rewrite substitute_open2 in *; repeat step || list_utils; eauto with wf.
    rewrite open_close in *; steps; eauto using wfs_combine7 with wf.
    rewrite (subst_subst template) in * |-;
      repeat step || t_substitutions ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             rewrite List.map_map in *.
    rewrite list_map_subst3 in *; steps; eauto.
    rewrite psubstitute_texists_vars;
      repeat step || rewrite substitute_trail || rewrite <- satisfies_same_support in *;
      eauto with fv;
      eauto using var_in_support.
    apply reducible_exists_vars with (List.map (fun key => append_key key a) keys);
      repeat step || apply wf_subst || apply subst_erased_type || list_utils || list_utils2 ||
             Forall_inst || (erewrite reducible_val_fv in * by eauto) ||
             apply wfs_combine8 || apply erased_terms_combine2 || rewrite pfv_append_key in *;
      eauto 3 with wf step_tactic;
      eauto with erased;
      try solve [ eapply satisfies_erased_terms; eauto; steps ];
      eauto 2 using forall_append_key_trails.

    rewrite (subst_subst2 template) in * |-;
      repeat step || list_utils2 || rewrite list_map_subst4 in * ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv.

    rewrite (subst_subst2 template);
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             (rewrite list_map_subst5 by (steps; eauto using var_in_support));
      eauto using var_in_support;
      eauto with fv.

    rewrite (subst_subst (psubstitute template l term_var));
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv;
      try solve [ t_pfv_in_subst; eauto with fv ].

    rewrite list_map_subst6; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.
    rewrite list_map_subst7; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.

  - rewrite psubstitute_texists_vars in *;
      repeat step || rewrite substitute_trail in * || rewrite <- satisfies_same_support in *;
      eauto with fv;
      eauto using var_in_support.

    apply_anywhere reducible_exists_vars2;
      repeat step || apply subst_erased_type || apply wf_subst;
      eauto using wfs_combine8, erased_terms_combine2 with wf fv erased;
      try solve [ eapply satisfies_erased_terms; eauto; steps ].

    rewrite (subst_subst2 template) in *;
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             (rewrite list_map_subst5 by (steps; eauto using var_in_support));
      eauto using var_in_support;
      eauto with fv.

    rewrite (subst_subst (psubstitute template l term_var)) in *;
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv;
      try solve [ t_pfv_in_subst; eauto with fv ].

    rewrite list_map_subst6 in *; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.
    rewrite list_map_subst8 in *; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.

    simp_red_goal; repeat step || apply subst_erased_type || apply is_erased_type_close;
      eauto 3 with erased step_tactic;
      eauto 3 using wfs_combine8, erased_terms_combine3 with wf fv erased;
      try solve [ eapply satisfies_erased_terms; eauto; steps ];
      try solve [ eapply reducible_values_closed; eauto; steps ].

     exists (global_trail keys vs); repeat step;
       eauto using typed_erased_terms', is_erased_term_global_trail;
       eauto using typed_fv', fvs_global_trail;
       eauto using typed_wfs', wfs_global_trail;
       eauto using global_trail_is_trail.

    rewrite substitute_open2 in *; repeat step || list_utils; eauto with wf;
      eauto using fvs_global_trail2.
    rewrite open_close in *; steps; eauto using wfs_combine7 with wf.
    rewrite (subst_subst template);
      repeat step || t_substitutions ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             rewrite List.map_map in *.
    rewrite list_map_subst3 in *; steps; eauto.

    rewrite (subst_subst2 template);
      repeat step || list_utils2 || rewrite list_map_subst4 in * ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv;
      eauto using global_trail_is_trail.

    eapply reducibility_equivalent_substititions; try eassumption;
      repeat step || list_utils || list_utils2 || apply subst_erased_type ||
             t_pfv_in_subst ||
             rewrite length_apps by (repeat step || list_utils2);
      eauto with erased wf fv;
      try solve [ eapply satisfies_erased_terms; eauto; steps ].

    + apply in_combine_equivalent' with fs keys vs l; steps.
      * unfold open_reducible in *; repeat step.
        unshelve epose proof (H16 f _ nil l _ _ _);
          repeat step || rewrite substitute_tau in *.
      * apply functional_trans with _ ys; steps.

    + instantiate_any; steps.
      clear_marked; apply_anywhere pfv_in_subst2; steps; eauto with fv.
Qed.

Lemma untangle_abstract:
  forall Γ T A,
    is_erased_type A ->
    is_erased_type T ->
    wf T 1 ->
    wf A 0 ->
    subset (fv A) (support Γ) ->
    subset (fv T) (support Γ) ->
    [ Γ ⊨ tnil : A ] ->
    [ Γ ⊨ T_exists T_trail (shift_open 0 T (tlookup A (lvar 0 term_var))) = T_exists A T ].
Proof.
  unfold open_equivalent_types, equivalent_types; intros;
    repeat step || list_utils || list_utils2 || simp_red_top_level_hyp || rewrite substitute_trail in *.

  - rewrite substitute_open2 in *; repeat step || list_utils; eauto with wf.
    rewrite open_shift_open4 in *; repeat step || rewrite open_lookup in * || open_none.
    rewrite no_shift_open in H13;
      repeat step || apply subst_erased_type;
      eauto with wf;
      try solve [ eapply satisfies_erased_terms; eauto; steps ].

    apply reducible_expr_value;
      try solve [ eapply reducible_values_closed; eauto; steps ].
    apply reducible_exists with (tlookup (psubstitute A l term_var) a); steps;
      repeat step || rewrite lookup_fv || list_utils ||
             apply subst_erased_type || t_substitutions ||
             (rewrite (substitute_nothing5 a) in * by auto) ||
             rewrite substitute_lookup in * || apply lookup_type ||
             apply is_erased_term_lookup;
      eauto with erased wf fv;
      try solve [ eapply satisfies_erased_terms; eauto; steps ];
      try solve [ apply reducible_value_expr; steps ].

    unfold open_reducible in *; repeat step.
    unshelve epose proof (H5 nil l _ _ _); steps;
      eauto using reducible_expr_value with values.

  - unshelve epose proof (lookup_onto _ _ H11);
      repeat step || simp_red_goal || apply subst_erased_type;
      try solve [ eapply satisfies_erased_terms; eauto; steps ];
      eauto 3 with erased.

    exists trail; steps; eauto with erased fv wf.
    rewrite substitute_open2;
      repeat step || list_utils ||
             (unshelve erewrite reducible_val_fv in * by (eauto; steps));
      eauto with wf.
    rewrite open_shift_open4; repeat step || rewrite open_lookup in * || open_none; eauto with wf.
    rewrite no_shift_open;
      repeat step || apply subst_erased_type || t_substitutions;
      eauto with wf;
      try solve [ eapply satisfies_erased_terms; eauto; steps ].

    eapply reducibility_open_equivalent; eauto;
      repeat step || rewrite substitute_lookup in *;
      eauto using equivalent_sym with wf fv.

    rewrite (substitute_nothing5 trail); eauto with fv; eauto using equivalent_sym.
Qed.

Lemma untangle_singleton:
   forall Θ Γ T T' t,
     [ Θ; Γ ⊨ T = T' ] ->
     [ Θ; Γ ⊨ T_singleton T t = T_singleton T' t ].
Proof.
  unfold open_equivalent_types, equivalent_types;
    repeat step || simp_red || t_instantiate_sat3;
    eauto with eapply_any.
Qed.

Lemma untangle_open_equivalent_types:
  forall Γ T1 T2,
    untangle Γ T1 T2 ->
    [ Γ ⊨ T1 = T2 ].
Proof.
  induction 1; steps;
    eauto using open_equivalent_types_refl;
    eauto using untangle_freshen;
    eauto using open_npi;
    eauto using open_nexists_2;
    eauto using untangle_singleton;
    eauto using untangle_abstract;
    eauto using open_ncons.
Qed.
