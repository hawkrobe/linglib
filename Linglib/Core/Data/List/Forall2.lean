/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Forall2
import Mathlib.Logic.Relation

/-!
# Composition, transitivity, and antisymmetry of `List.Forall₂`

`List.Forall₂ R` relates lists of equal length pointwise. It composes pointwise
(`List.forall₂_comp_iff`), so it inherits transitivity and antisymmetry from `R`, as
`List.SublistForall₂` does in `Mathlib/Data/List/Forall2.lean`; with `R := (· ≤ ·)` this is the
pointwise order on lists of equal length. [UPSTREAM] candidates for that file, beside
`List.SublistForall₂.is_refl` and `List.SublistForall₂.is_trans`.

## Main results

* `List.forall₂_comp_iff`: `Forall₂ (R ∘r S)` is the pointwise composite of `Forall₂ R` and
  `Forall₂ S`.
* `List.Forall₂.trans`, `List.Forall₂.antisymm`, and the `Std.Refl`, `IsTrans`, `Std.Antisymm`
  instances on `Forall₂ R`.
-/

namespace List

variable {α β γ : Type*} {R : α → α → Prop}

/-- `Forall₂` for a composite relation is the pointwise composite of the two `Forall₂`s. -/
theorem forall₂_comp_iff {R : α → β → Prop} {S : β → γ → Prop} {l₁ : List α} {l₃ : List γ} :
    Forall₂ (Relation.Comp R S) l₁ l₃ ↔ ∃ l₂, Forall₂ R l₁ l₂ ∧ Forall₂ S l₂ l₃ := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons hac _ ih =>
      obtain ⟨b, hab, hbc⟩ := hac
      obtain ⟨l₂, h₁, h₂⟩ := ih
      exact ⟨b :: l₂, .cons hab h₁, .cons hbc h₂⟩
  · rintro ⟨l₂, h₁, h₂⟩
    induction h₁ generalizing l₃ with
    | nil => cases h₂; exact .nil
    | cons hab _ ih =>
      cases h₂ with
      | cons hbc h₂' => exact .cons ⟨_, hab, hbc⟩ (ih h₂')

theorem Forall₂.trans [IsTrans α R] {l₁ l₂ l₃ : List α} (h₁ : Forall₂ R l₁ l₂)
    (h₂ : Forall₂ R l₂ l₃) : Forall₂ R l₁ l₃ :=
  (forall₂_comp_iff.2 ⟨l₂, h₁, h₂⟩).imp fun _ _ ⟨_, hab, hbc⟩ ↦ _root_.trans hab hbc

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
