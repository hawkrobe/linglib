/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Option.Basic

/-!
# Compatibility and agreement of partial values

Two relations on `Option α` viewed as partial specifications:
`Option.Compatible` holds when the two values do not disagree (if both
are `some`, they coincide), `Option.Agrees` when both are `some` of the
same value. `Agrees` is the positive-evidence strengthening of
`Compatible`: `none` is compatible with everything and agrees with
nothing.

[UPSTREAM] Mathlib candidate: no counterpart exists (`Option.Rel`
relates `none` only to `none`, so it is not compatibility).
-/

namespace Option

variable {α : Type*} {a b : Option α} {x y : α}

/-- Two partial values are compatible: if both are `some`, they
coincide. -/
def Compatible (a b : Option α) : Prop := ∀ x ∈ a, ∀ y ∈ b, x = y

/-- Two partial values agree: both are `some` of the same value. -/
def Agrees (a b : Option α) : Prop := ∃ x ∈ a, x ∈ b

@[simp] theorem compatible_none_left : (none : Option α).Compatible b :=
  fun x hx => absurd hx (by simp)

@[simp] theorem compatible_none_right : a.Compatible none :=
  fun _ _ y hy => absurd hy (by simp)

@[simp] theorem compatible_some_some :
    (some x).Compatible (some y) ↔ x = y := by
  simp [Compatible]

theorem compatible_iff : a.Compatible b ↔ a = none ∨ b = none ∨ a = b := by
  cases a <;> cases b <;> simp [Compatible]

theorem Compatible.symm (h : a.Compatible b) : b.Compatible a :=
  fun x hx y hy => (h y hy x hx).symm

@[simp] theorem not_agrees_none_left : ¬ (none : Option α).Agrees b := by
  simp [Agrees]

@[simp] theorem not_agrees_none_right : ¬ a.Agrees none := by
  simp [Agrees]

@[simp] theorem agrees_some_some : (some x).Agrees (some y) ↔ x = y := by
  simp [Agrees, eq_comm]

theorem agrees_iff : a.Agrees b ↔ a ≠ none ∧ a = b := by
  cases a <;> cases b <;> simp [eq_comm]

theorem Agrees.symm (h : a.Agrees b) : b.Agrees a :=
  let ⟨x, hx, hy⟩ := h
  ⟨x, hy, hx⟩

theorem Agrees.compatible (h : a.Agrees b) : a.Compatible b := by
  obtain ⟨x, hx, hy⟩ := h
  intro u hu v hv
  simp_all

instance [DecidableEq α] : Decidable (a.Compatible b) :=
  decidable_of_iff _ compatible_iff.symm

instance [DecidableEq α] : Decidable (a.Agrees b) :=
  decidable_of_iff _ agrees_iff.symm

end Option
