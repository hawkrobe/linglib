import Mathlib.Data.Option.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-!
# Valuation: Pi-Typed Partial Variable Assignment (V2)

Replaces the old `Situation` (which fixed `Variable → Option Bool`).
A `Valuation α` is a Π-type partial valuation where each vertex `v`
has its own value type `α v`. The Pi pattern follows mathlib's
`Algebra/Group/Pi/Basic.lean` idiom for index-dependent value families.

`α := fun _ => Bool` recovers the legacy binary substrate.

A `DecidableValuation` aggregator typeclass bundles
`∀ v, DecidableEq (α v)` for use throughout the API.
-/

namespace Core.Causal.V2

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

/-- Information ordering: every value defined in `s₁` matches in `s₂`. -/
def le [DecidableValuation α] (s₁ s₂ : Valuation α) : Prop :=
  ∀ v x, s₁.hasValue v x → s₂.hasValue v x

/-- Count of undetermined vertices over a finite list. Termination
    measure for the forward-development fixpoint (mirrors the old
    `Monotonicity.lean` measure but generalized over `α`). -/
def undeterminedCount (s : Valuation α) (l : List V) : ℕ :=
  l.countP (fun v => (s.get v).isNone)

@[simp] theorem extend_get_same [DecidableEq V]
    (s : Valuation α) (v : V) (x : α v) :
    (s.extend v x).get v = some x := by
  simp [extend, get]

theorem extend_get_ne [DecidableEq V]
    {s : Valuation α} {v w : V} {x : α v} (h : w ≠ v) :
    (s.extend v x).get w = s.get w := by
  simp [extend, get, h]

@[simp] theorem empty_get (v : V) : (Valuation.empty (α := α)).get v = none := rfl

theorem hasValue_empty_iff (v : V) (x : α v) :
    ¬ (Valuation.empty (α := α)).hasValue v x := by
  simp [hasValue, get, empty]

end Valuation

end Core.Causal.V2
