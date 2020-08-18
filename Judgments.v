Require Export SystemFR.OpenReducibilityDefinition.
Require Export SystemFR.TypeErasure.

Definition annotated_reducible Θ Γ t1 t2 T : Prop :=
  open_reducible Θ (erase_context Γ) (erase_term t1) (erase_term t2) (erase_type T).

Definition annotated_weak_subtype Θ Γ T1 T2 : Prop :=
  open_weak_subtype Θ (erase_context Γ) (erase_type T1) (erase_type T2).

Definition annotated_strong_subtype Θ Γ T1 T2 : Prop :=
  open_strong_subtype Θ (erase_context Γ) (erase_type T1) (erase_type T2).

Definition annotated_equivalent Θ Γ t1 t2 : Prop :=
  open_equivalent Θ (erase_context Γ) (erase_term t1) (erase_term t2).

Notation "'[[' Θ ';' Γ '⊨' t1 '=' t2 ':' T ']]'" := (annotated_reducible Θ Γ t1 t2 T)
  (at level 50, t1 at level 50, t2 at level 50).

Notation "'[[' Θ ';' Γ '⊨' t ':' T ']]'" := (annotated_reducible Θ Γ t t T)
  (at level 50, t at level 50).

Notation "'[[' Θ ';' Γ '⊨' T1 '<:?' T2 ']]'" := (annotated_weak_subtype Θ Γ T1 T2)
  (at level 50, T1 at level 50).

Notation "'[[' Θ ';' Γ '⊨' T1 '<:' T2 ']]'" := (annotated_strong_subtype Θ Γ T1 T2)
  (at level 50, T1 at level 50).

Notation "'[[' Θ ';' Γ '⊨' t1 '≡' t2 ']]'" := (annotated_equivalent Θ Γ t1 t2)
  (at level 50, t1 at level 50).
