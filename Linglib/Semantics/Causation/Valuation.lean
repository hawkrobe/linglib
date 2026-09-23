module

public import Linglib.Core.Order.Flat
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Basic

/-!
# Valuations: partial variable assignments

A `Valuation α` assigns each vertex `v` a value of type `α v` or leaves it undetermined, a
situation in the sense of [schulz-2011]. A valuation is a function into the flat domains of the
value types (`Core.Order.Flat`), so it is ordered by information: `s₁ ≤ s₂` when `s₂` determines,
with the same value, every vertex `s₁` determines. `Flat` is `Option` under another name, which
keeps constructor matching and `DecidableEq` while keeping `Option`'s own order off valuations.
Setting and clearing a vertex are `Function.update`, whose simp lemmas evaluate them.

## Main declarations

* `Valuation`, `Valuation.empty`, `Valuation.hasValue`
* `Valuation.extend`, `Valuation.remove`: setting and clearing a vertex
* `Valuation.le_def`: the information order, the product order on `∀ v, Flat (α v)`
* `Valuation.fintype`: finiteness, for decision procedures that quantify over valuations

## References

* [schulz-2011]
-/

@[expose] public section

namespace Causation

/-- Partial valuation: each vertex `v` has a value of type `α v` (`some x`) or is undetermined
(`none`). -/
abbrev Valuation {V : Type*} (α : V → Type*) := ∀ v : V, Flat (α v)

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

/-- Valuations over finite vertex and value types are finitely many. Not an instance: a
`Fintype` instance on `Flat` would change how `decide` evaluates every flat-valued function, so a
decision procedure that quantifies over valuations installs this one locally. -/
@[reducible] def fintype [Fintype V] [DecidableEq V] [∀ v, Fintype (α v)] :
    Fintype (Valuation α) :=
  inferInstanceAs (Fintype (∀ v, Option (α v)))

variable {s s₁ s₂ : Valuation α}

/-- `s₁ ≤ s₂` when every value determined in `s₁` is determined identically in `s₂`. -/
theorem le_def : s₁ ≤ s₂ ↔ ∀ v x, s₁.hasValue v x → s₂.hasValue v x := by
  refine Pi.le_def.trans (forall_congr' fun v ↦ ?_)
  simp only [hasValue, get]
  cases s₁ v with
  | bot => exact iff_of_true bot_le fun _ h ↦ by cases h
  | coe x =>
    refine Flat.coe_le_iff.trans ⟨fun h y hy ↦ ?_, fun h ↦ h x rfl⟩
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
