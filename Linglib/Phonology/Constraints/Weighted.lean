/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Constraints.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Weighted constraints and harmony

A `WeightedConstraint` is a named constraint plus a real weight, and the
**harmony** of a candidate is the negated weighted sum of its violations,
`H(c) = -Σⱼ wⱼ · Cⱼ(c)` [smolensky-legendre-2006].

## Main definitions

* `WeightedConstraint C` — a `NamedConstraint C` plus a real `weight`.
* `harmonyScore` — the harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)` (real-valued).
* `harmonyDominates` — the strict harmony order on candidates (pullback of `<`).
-/

namespace Constraints

/-! ### Weighted constraints -/

/-- A weighted constraint over candidates of type `C`. -/
structure WeightedConstraint (C : Type*) extends NamedConstraint C where
  /-- Constraint weight; higher is more important. -/
  weight : ℝ

variable {C : Type*} (cs : List (WeightedConstraint C)) (c a b : C)

/-! ### Harmony -/

/-- Harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)`: the negated weighted sum of violations
    ([smolensky-legendre-2006]); higher is more grammatical. -/
def harmonyScore : ℝ := -(cs.map fun con => con.weight * (con.eval c : ℝ)).sum

/-- `harmonyScore` as a negated `List.sum` (unfolding lemma for rewriting). -/
theorem harmonyScore_eq_neg_sum :
    harmonyScore cs c = -(cs.map fun con => con.weight * (con.eval c : ℝ)).sum := rfl

/-- `a` outranks `b` in harmony: `H(a) > H(b)`, the pullback of `<` along
    `harmonyScore`. No `Decidable` instance — `ℝ` comparison does not reduce. -/
def harmonyDominates : Prop := harmonyScore cs b < harmonyScore cs a

end Constraints
