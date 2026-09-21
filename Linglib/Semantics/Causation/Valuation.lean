module

public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic

/-!
# Valuation: Pi-Typed Partial Variable Assignment

Replaces the old `Situation` (which fixed `Variable → Option Bool`).
A `Valuation α` is a Π-type partial valuation where each vertex `v`
has its own value type `α v`. The Pi pattern follows mathlib's
`Algebra/Group/Pi/Basic.lean` idiom for index-dependent value families.

`α := fun _ => Bool` recovers the legacy binary substrate.

A `DecidableValuation` aggregator typeclass bundles
`∀ v, DecidableEq (α v)` for use throughout the API.
-/

@[expose] public section

namespace Causation

/-- Partial valuation: each vertex `v` either has a value of type `α v`
    (encoded `some x`) or is undetermined (`none`). Generalizes the old
    `Situation` (which fixed `α := fun _ => Bool`).

    Defined as an `abbrev` for Π-type rather than a `structure`, so
    elaboration unifies `Valuation α` with `Π v, Option (α v)` directly. -/
abbrev Valuation {V : Type*} (α : V → Type*) := ∀ v : V, Option (α v)

/-- Per-vertex decidable equality. An `abbrev` (not a `class`) so it
    unfolds transparently to the bare `∀ v, DecidableEq (α v)` constraint
    typeclass search expects. Avoids the bundled-class antipattern. -/
abbrev DecidableValuation {V : Type*} (α : V → Type*) :=
  ∀ v, DecidableEq (α v)

namespace Valuation

variable {V : Type*} {α : V → Type*}

/-- The empty valuation: nothing is determined. -/
def empty : Valuation α := fun _ => none

instance : Inhabited (Valuation α) := ⟨empty⟩

/-- Get the value of a variable (if determined). -/
def get (s : Valuation α) (v : V) : Option (α v) := s v

/-- The variable has the given value in the valuation. -/
def hasValue (s : Valuation α) (v : V) (x : α v) : Prop := s.get v = some x

instance [DecidableValuation α] (s : Valuation α) (v : V) (x : α v) :
    Decidable (s.hasValue v x) :=
  inferInstanceAs (Decidable (_ = _))

/-- Extend a valuation with a new assignment. Overwrites if already set. -/
def extend [DecidableEq V] (s : Valuation α) (v : V) (x : α v) :
    Valuation α := fun w =>
  if h : w = v then some (h ▸ x) else s w

/-- Remove a variable from the valuation (set to undetermined). -/
def remove [DecidableEq V] (s : Valuation α) (v : V) : Valuation α := fun w =>
  if w = v then none else s w

/-- The information order: `s₁ ≤ s₂` iff every value determined in `s₁`
    is determined identically in `s₂`. -/
instance : PartialOrder (Valuation α) where
  le s₁ s₂ := ∀ v x, s₁.hasValue v x → s₂.hasValue v x
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ v x h := h₂ v x (h₁ v x h)
  le_antisymm s₁ s₂ h₁ h₂ := by
    funext v
    show s₁.get v = s₂.get v
    cases h : s₁.get v with
    | some x => exact (h₁ v x h).symm
    | none =>
        cases h' : s₂.get v with
        | none => rfl
        | some y =>
            have hy : s₁.get v = some y := h₂ v y h'
            rw [h] at hy
            simp at hy

/-- The information order unfolds to pointwise preservation of
    determined values. -/
theorem le_def {s₁ s₂ : Valuation α} :
    s₁ ≤ s₂ ↔ ∀ v x, s₁.hasValue v x → s₂.hasValue v x := Iff.rfl

@[simp] theorem extend_get_same [DecidableEq V]
    (s : Valuation α) (v : V) (x : α v) :
    (s.extend v x).get v = some x := by
  simp [extend, get]

theorem extend_get_ne [DecidableEq V]
    {s : Valuation α} {v w : V} {x : α v} (h : w ≠ v) :
    (s.extend v x).get w = s.get w := by
  simp [extend, get, h]

/-- Extending at an undetermined vertex only adds information. -/
theorem le_extend [DecidableEq V] {s : Valuation α}
    {v : V} (x : α v) (h : s.get v = none) : s ≤ s.extend v x := by
  intro w y hw
  by_cases hwv : w = v
  · subst hwv; rw [Valuation.hasValue, h] at hw; exact absurd hw (by simp)
  · rwa [Valuation.hasValue, extend_get_ne hwv]

@[simp] theorem empty_get (v : V) : (Valuation.empty (α := α)).get v = none := rfl

theorem hasValue_empty_iff (v : V) (x : α v) :
    ¬ (Valuation.empty (α := α)).hasValue v x := by
  simp [hasValue, get, empty]

end Valuation

end Causation
