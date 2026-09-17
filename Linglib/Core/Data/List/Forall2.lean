import Mathlib.Data.List.Forall2

/-! # Pointwise relations on lists: reflexivity, transitivity and antisymmetry

`List.Forall₂ R` inherits reflexivity, transitivity and antisymmetry from
`R`, as `List.SublistForall₂` does in mathlib. With `R := (· ≤ ·)` this is
the pointwise order on lists of equal length.

## Main results

* `List.Forall₂.trans`, `List.Forall₂.antisymm` — and the `Std.Refl`,
  `IsTrans`, `Std.Antisymm` instances
-/

namespace List

variable {α : Type*} {R : α → α → Prop}

theorem Forall₂.trans [IsTrans α R] {l₁ l₂ l₃ : List α} :
    Forall₂ R l₁ l₂ → Forall₂ R l₂ l₃ → Forall₂ R l₁ l₃
  | .nil, .nil => .nil
  | .cons h₁ t₁, .cons h₂ t₂ => .cons (_root_.trans h₁ h₂) (t₁.trans t₂)

theorem Forall₂.antisymm [Std.Antisymm R] {l₁ l₂ : List α} :
    Forall₂ R l₁ l₂ → Forall₂ R l₂ l₁ → l₁ = l₂
  | .nil, .nil => rfl
  | .cons h₁ t₁, .cons h₂ t₂ => by rw [_root_.antisymm h₁ h₂, t₁.antisymm t₂]

instance Forall₂.instRefl [Std.Refl R] : Std.Refl (Forall₂ R) := ⟨forall₂_refl⟩

instance Forall₂.instIsTrans [IsTrans α R] : IsTrans (List α) (Forall₂ R) :=
  ⟨fun _ _ _ ↦ Forall₂.trans⟩

instance Forall₂.instAntisymm [Std.Antisymm R] : Std.Antisymm (Forall₂ R) :=
  ⟨fun _ _ ↦ Forall₂.antisymm⟩

end List
