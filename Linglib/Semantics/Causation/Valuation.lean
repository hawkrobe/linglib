module

public import Linglib.Core.Order.Flat
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Valuations: partial variable assignments

A `Valuation α` assigns each vertex `v` a value of type `α v` or leaves it undetermined, a
situation in the sense of [schulz-2011]. Valuations are ordered by information: `s₁ ≤ s₂` when
`s₂` determines, with the same value, every vertex `s₁` determines. This is the product of the
flat orders on the value types (`Core.Order.Flat`), carried on `Option`, the flat order's
decidable twin, so that valuations keep `DecidableEq` and constructor matching. Setting and
clearing a vertex are `Function.update`, whose simp lemmas evaluate them.

## Main declarations

* `Valuation`, `Valuation.empty`, `Valuation.hasValue`
* `Valuation.extend`, `Valuation.remove`: setting and clearing a vertex
* the information order, a `PartialOrder` with `⊥ = empty`, decidable over a finite vertex type

## References

* [schulz-2011]
-/

@[expose] public section

namespace Causation

/-- Partial valuation: each vertex `v` has a value of type `α v` (`some x`) or is undetermined
(`none`). -/
abbrev Valuation {V : Type*} (α : V → Type*) := ∀ v : V, Option (α v)

/-- Per-vertex decidable equality, the constraint the valuation API needs. -/
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

/-- Set a variable to a value, overwriting any value it had. -/
def extend [DecidableEq V] (s : Valuation α) (v : V) (x : α v) : Valuation α :=
  Function.update s v (some x)

/-- Leave a variable undetermined. -/
def remove [DecidableEq V] (s : Valuation α) (v : V) : Valuation α :=
  Function.update s v none

/-- The information order: the product of the flat orders on the value types. -/
instance : PartialOrder (Valuation α) := inferInstanceAs (PartialOrder (∀ v, Flat (α v)))

instance : OrderBot (Valuation α) := inferInstanceAs (OrderBot (∀ v, Flat (α v)))

instance [Fintype V] [DecidableValuation α] : DecidableLE (Valuation α) :=
  inferInstanceAs (DecidableLE (∀ v, Flat (α v)))

variable {s s₁ s₂ : Valuation α}

/-- `s₁ ≤ s₂` when every value determined in `s₁` is determined identically in `s₂`. -/
theorem le_def : s₁ ≤ s₂ ↔ ∀ v x, s₁.hasValue v x → s₂.hasValue v x := by
  show (∀ v, @LE.le (Flat (α v)) _ (s₁ v) (s₂ v)) ↔ _
  refine forall_congr' fun v ↦ ?_
  simp only [hasValue, get]
  cases s₁ v with
  | none => exact iff_of_true bot_le (by simp)
  | some x =>
    refine (Flat.coe_le_iff (a := x)).trans ⟨fun h y hy ↦ ?_, fun h ↦ h x rfl⟩
    cases hy
    exact h

@[simp] theorem extend_get_same [DecidableEq V] (s : Valuation α) (v : V) (x : α v) :
    (s.extend v x).get v = some x :=
  Function.update_self ..

theorem extend_get_ne [DecidableEq V] {v w : V} {x : α v} (h : w ≠ v) :
    (s.extend v x).get w = s.get w :=
  Function.update_of_ne h ..

/-- Setting an undetermined vertex only adds information. -/
theorem le_extend [DecidableEq V] {v : V} (x : α v) (h : s.get v = none) : s ≤ s.extend v x :=
  le_def.2 fun w y hw ↦ by
    by_cases hwv : w = v
    · subst hwv; exact absurd (h.symm.trans hw) (by simp)
    · rwa [hasValue, extend_get_ne hwv]

@[simp] theorem empty_get (v : V) : (Valuation.empty (α := α)).get v = none := rfl

theorem hasValue_empty_iff (v : V) (x : α v) :
    ¬ (Valuation.empty (α := α)).hasValue v x := by
  simp [hasValue, get, empty]

end Valuation

end Causation
