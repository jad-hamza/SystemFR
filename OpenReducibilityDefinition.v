Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.TermList.

Definition open_type (Θ: tvar_list) (Γ: context) T1 T2 : Prop :=
  forall ρ l1 l2,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l1 l2 ->
    support ρ = Θ ->
    [ ρ ⊨ substitute T1 l1 =:= substitute T2 l2 ].

Definition open_reducible (Θ: tvar_list) (Γ: context) t1 t2 T : Prop :=
  forall ρ l1 l2,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l1 l2 ->
    support ρ = Θ ->
    [ ρ ⊨ substitute t1 l1 ≡ substitute t2 l2 : substitute T l1 ].

Definition open_weak_subtype (Θ: tvar_list) (Γ: context) T1 T2 : Prop :=
  forall ρ l1 l2,
   valid_interpretation ρ ->
   satisfies (reducible_values ρ) Γ l1 l2 ->
   support ρ = Θ ->
   [ ρ ⊨ substitute T1 l1 <:? substitute T2 l2 ].

Definition open_strong_subtype (Θ: tvar_list) (Γ: context) T1 T2 : Prop :=
  forall ρ l1 l2,
   valid_interpretation ρ ->
   satisfies (reducible_values ρ) Γ l1 l2 ->
   support ρ = Θ ->
   [ ρ ⊨ substitute T1 l1 <: substitute T2 l2 ].

Definition open_equivalent (Θ: tvar_list) (Γ: context) t t' : Prop :=
  forall ρ l1 l2,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l1 l2 ->
    support ρ = Θ ->
    equivalent_terms (substitute t l1) (substitute t' l1).

Notation "'[' Θ ';' Γ '⊨' t1 '≡' t2 ':' T ']'" := (open_reducible Θ Γ t1 t2 T)
  (Θ at level 60, Γ at level 60, t1 at level 60, t2 at level 60, T at level 60).

Notation "'[' Θ ';' Γ '⊨' T1 '=:=' T2 ']'" := (open_type Θ Γ T1 T2)
  (Θ at level 60, Γ at level 60, T1 at level 60, T2 at level 60).

Notation "'[' Θ ';' Γ '⊨' T ']'" := (open_type Θ Γ T T)
  (Θ at level 60, Γ at level 60, T at level 60).

Notation "'[' Θ ';' Γ '⊨' t ':' T ']'" := (open_reducible Θ Γ t t T)
  (Θ at level 60, Γ at level 60, t at level 60).

Notation "'[' Θ ';' Γ '⊨' T1 '<:?' T2 ']'" := (open_weak_subtype Θ Γ T1 T2)
  (Θ at level 60, Γ at level 60, T1 at level 60).

Notation "'[' Θ ';' Γ '⊨' T1 '<:' T2 ']'" := (open_strong_subtype Θ Γ T1 T2)
  (Θ at level 60, Γ at level 60, T1 at level 60).

Notation "'[' Θ ';' Γ '⊨' t1 '≡' t2 ']'" := (open_equivalent Θ Γ t1 t2)
  (Θ at level 60, Γ at level 60, t1 at level 60, t2 at level 60).

Lemma open_reducible_same:
  forall Θ Γ t1 t2 T Θ' Γ' t1' t2' T',
    [ Θ; Γ ⊨ t1 ≡ t2 : T ] ->
    Θ = Θ' ->
    Γ = Γ' ->
    t1 = t1' ->
    t2 = t2' ->
    T = T' ->
    [ Θ'; Γ' ⊨ t1' ≡ t2' : T' ].
Proof.
  steps.
Qed.
