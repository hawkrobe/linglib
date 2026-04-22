import Mathlib.Data.ENNReal.Operations

/-!
# Graded Propositions

ENNReal-valued graded propositions: a world (or entity) maps to a
probability degree in `ℝ≥0∞`. Mirrors mathlib's universal use of
`ℝ≥0∞` for probability values (`PMF`, `OuterMeasure`, `Measure`,
`ProbabilityTheory.cond`); the `[0,1]` bound is a *theorem* on
specific propositions, not a type-level constraint, just as
`PMF.coe_le_one` rather than typing PMF entries as `unitInterval`.

Cast to `ℝ` via `ENNReal.toReal` at boundaries with ℝ-valued
infrastructure (e.g. RSA scoring).
-/

namespace Core.GradedProposition

open scoped ENNReal

/-- A graded proposition: probability degree at each world. -/
abbrev GProp (W : Type*) := W → ℝ≥0∞

/-- A graded predicate: probability degree at each entity. -/
abbrev GPred (E : Type*) := E → ℝ≥0∞

variable {W : Type*}

/-- Graded negation: `(¬p) w = 1 - p w`. ENNReal subtraction truncates
at 0, so `neg` is total on `GProp W`; involutivity holds on the [0,1]
fragment via `ENNReal.sub_sub_cancel` (mathlib lemma). -/
def neg (p : GProp W) : GProp W := fun w => 1 - p w

/-- Lift a Boolean proposition. -/
def ofBool (p : W → Bool) : GProp W := fun w => if p w then 1 else 0

end Core.GradedProposition
