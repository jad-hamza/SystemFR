
Fixpoint valid_pre_interpretation2 (P: tree -> Prop) (theta: list (nat * (tree -> tree -> tree -> Prop))) : Prop :=
  match theta with
  | nil => True
  | (_, RC) :: theta' =>
    valid_pre_interpretation2 P theta' /\
    forall a, P a -> reducibility_candidate2 (RC a)
  end.

Lemma valid_interpretation_equiv:
  forall P1 P2 ptheta,
    valid_pre_interpretation P1 ptheta ->
    (forall x, P1 x <-> P2 x) ->
    valid_pre_interpretation P2 ptheta.
Proof.
  induction ptheta; steps; eauto with eapply_any.
Qed.

Ltac t_valid_interpretation_equiv :=
  match goal with
  | H1: valid_pre_interpretation ?P1 ?ptheta |- valid_pre_interpretation _ ?ptheta => apply valid_interpretation_equiv with P1
  end.

Definition push_one (a: tree) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  map_values (fun rc => rc a) l.
Definition push_all (P: tree -> Prop) (l: list (nat * (tree -> tree -> Prop))): interpretation :=
  map_values (fun (rc: tree -> tree -> Prop) (v: tree) => (forall a, P a -> rc a v)) l.

Lemma valid_interpretation_one:
  forall a (P: tree -> Prop) theta,
    P a ->
    valid_pre_interpretation P theta ->
    valid_interpretation2 (push_one a theta).
Proof.
  induction theta; steps.
Qed.

Hint Resolve valid_interpretation_one: b_valid_interp.
Hint Extern 1 => eapply valid_interpretation_one; eauto: b_valid_interp.
