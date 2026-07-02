/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Constraints

A constraint is a **violation-counting function** `C → ℕ`
([prince-smolensky-1993]). There is no stored "name" and no stored
faithfulness/markedness tag: a constraint *is* its evaluation function.

The faithfulness/markedness distinction is a **structural property**, derived —
not stipulated — over a correspondence carrier (`OptimalityTheory.Correspondence`):
*markedness* factors through the output; *faithfulness* vanishes on the identity
candidate. A bare `C → ℕ` over an opaque candidate type has no family, by design.

## Main definitions

* `Constraint C` — a violation-counting function `C → ℕ`.
* `Constraint.binary` — the indicator constraint of a decidable predicate.
* `Constraint.comap` — pull a constraint back along a candidate map.
* `CON C n` — a grammar's constraint set: an indexed family of `n` constraints.
* `weightedViolations` / `harmonyScore` — the Harmonic-Grammar weighted sum
  `Σⱼ wⱼ · Cⱼ(c)` and its negation `H(c) = -Σⱼ wⱼ · Cⱼ(c)` ([smolensky-legendre-2006]).
-/

namespace Constraints

/-- An OT / Harmonic-Grammar **constraint**: a violation-counting function on
candidates ([prince-smolensky-1993]). The faithfulness/markedness family is a
*structural* property (see `OptimalityTheory.Correspondence`), not a stored tag;
a constraint over an opaque candidate type has no family. -/
abbrev Constraint (C : Type*) := C → ℕ

variable {C D : Type*}

/-- The **binary** constraint of a decidable predicate: `1` when `P c`, else `0`.
The shared shape of every binary markedness/faithfulness constraint — the
faith/mark reading is recovered structurally, not from the constructor. -/
def Constraint.binary (P : C → Prop) [DecidablePred P] : Constraint C :=
  fun c => if P c then 1 else 0

@[simp] theorem Constraint.binary_apply (P : C → Prop) [DecidablePred P] (c : C) :
    Constraint.binary P c = if P c then 1 else 0 := rfl

/-- A binary constraint never assigns more than one violation. -/
theorem Constraint.binary_le_one (P : C → Prop) [DecidablePred P] (c : C) :
    Constraint.binary P c ≤ 1 := by
  simp only [Constraint.binary]; split <;> omega

/-- Pull a constraint back along `f : C → D`: evaluate the `D`-constraint on the
image. Lets a specific carrier reuse a constraint defined on a more general one. -/
def Constraint.comap (f : C → D) (con : Constraint D) : Constraint C := con ∘ f

@[simp] theorem Constraint.comap_apply (f : C → D) (con : Constraint D) (c : C) :
    Constraint.comap f con c = con (f c) := rfl

/-- A grammar's **constraint set** `CON`: an indexed family of `n` constraints over
candidates `C` ([prince-smolensky-1993]'s *CON*). A `CON` sends each candidate to a
`ViolationProfile n` (`buildViolationProfile`, in `Constraints.Profile`); an **OT** grammar then
ranks the coordinates (a `Ranking n`), a **Harmonic Grammar** weights them (a
`Fin n → ℝ` vector). Both feed the framework-neutral `Core.Optimization.ConstraintSystem`
through different decoders (lexicographic argmin vs. softmax). -/
abbrev CON (C : Type*) (n : ℕ) := Fin n → Constraint C

/-! ### Harmony (Harmonic Grammar)

A Harmonic Grammar weights each constraint in `CON` by a real number; the
**harmony** of a candidate is the negated weighted sum of its violations,
`H(c) = -Σⱼ wⱼ · Cⱼ(c)` ([smolensky-legendre-2006]) — a real linear functional of
the candidate's raw violation vector. The weight vector `w : Fin n → ℝ` is the
*grammar's* parameter (the HG twin of an OT `Ranking n`); both act on one `CON`. -/

variable {n : ℕ}

/-- The **weighted violation sum** `Σⱼ wⱼ · Cⱼ(c)` of a raw violation vector under
weight vector `w`: a real linear functional of the counts. The positive part of
harmony (`harmonyScore = -weightedViolations …`); weight-monotonicity and the
HG→OT exponential-separation results are stated on this. -/
def weightedViolations (w : Fin n → ℝ) (v : Fin n → ℕ) : ℝ :=
  ∑ j, w j * (v j : ℝ)

/-- Harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)` ([smolensky-legendre-2006]): the negated
weighted sum of a candidate's violations under the grammar's weight vector `w`;
higher is more grammatical. The HG reading of a constraint set `con` weighted by
`w` — the twin of *ranking* `con` in OT. -/
def harmonyScore (con : CON C n) (w : Fin n → ℝ) (c : C) : ℝ :=
  -weightedViolations w (fun j => con j c)

/-- `harmonyScore` as a negated `Finset.sum` (unfolding lemma for rewriting). -/
theorem harmonyScore_eq_neg_sum (con : CON C n) (w : Fin n → ℝ) (c : C) :
    harmonyScore con w c = -∑ j, w j * (con j c : ℝ) := rfl

/-- `a` outranks `b` in harmony: `H(a) > H(b)`, the pullback of `>` along
`harmonyScore con w` (`Order.Preimage`); inherits `IsStrictOrder` from ℝ's `>`. -/
def harmonyDominates (con : CON C n) (w : Fin n → ℝ) : C → C → Prop :=
  harmonyScore con w ⁻¹'o (· > ·)

@[simp] theorem harmonyDominates_iff (con : CON C n) (w : Fin n → ℝ) (a b : C) :
    harmonyDominates con w a b ↔ harmonyScore con w b < harmonyScore con w a := Iff.rfl

end Constraints
