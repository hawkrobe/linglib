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

The Harmonic Grammar layer over `Constraints.NamedConstraint`: a
`WeightedConstraint` is a named constraint plus a rational weight, and the
**harmony** of a candidate is the negated weighted sum of its violations,
`H(c) = -Σⱼ wⱼ · Cⱼ(c)` [smolensky-legendre-2006].

## Main definitions

* `WeightedConstraint C` — a `NamedConstraint C` plus a rational `weight`.
* `harmonyScore` — the harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)` (real-valued).
* `harmonyDominates` — the strict harmony order on candidates (pullback of `<`).
-/

namespace Constraints

/-! ### Weighted constraints -/

/-- A weighted constraint over candidates of type `C`. -/
structure WeightedConstraint (C : Type*) extends NamedConstraint C where
  /-- Constraint weight (higher = more important). -/
  weight : ℚ

variable {C : Type*} (cs : List (WeightedConstraint C)) (c a b : C)

/-! ### Harmony -/

/-- Harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)` ([smolensky-legendre-2006]): higher is more
    grammatical. Real-valued for the `softmax` / `predict` API; weights are the
    exact rationals cast pointwise into `ℝ`. -/
def harmonyScore : ℝ := -(cs.map fun con => (con.weight : ℝ) * con.eval c).sum

/-- `harmonyScore` as a negated `List.sum` — exposes the sum for `push_cast`
    to the rational weighted-violation machinery. -/
theorem harmonyScore_eq_neg_sum :
    harmonyScore cs c = -(cs.map fun con => (con.weight : ℝ) * con.eval c).sum := rfl

/-- `harmonyScore` is the real cast of the *rational* weighted sum — the bridge
    for exact (ℚ) weighted-violation reasoning (`OTLimit`, `Separability`). -/
theorem harmonyScore_eq_cast :
    harmonyScore cs c = -((cs.map fun con => con.weight * (con.eval c : ℚ)).sum : ℝ) := by
  simp only [harmonyScore, neg_inj]
  induction cs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

/-- `a` outranks `b` in harmony, `H(a) > H(b)` — the pullback of `<` along
    `harmonyScore`. Discharged by `norm_num` after unfolding; there is no
    `Decidable` instance (`ℝ` comparison does not reduce). -/
def harmonyDominates : Prop := harmonyScore cs b < harmonyScore cs a

end Constraints
