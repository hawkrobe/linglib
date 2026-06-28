/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Real.Basic

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
* `Constraint.Weighted C` — a constraint paired with a real weight (Harmonic Grammar).
* `harmonyScore` — the harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)` ([smolensky-legendre-2006]).
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

/-! ### Weighted constraints and harmony

Harmonic Grammar weights each constraint by a real number; the **harmony** of a
candidate is the negated weighted sum of its violations,
`H(c) = -Σⱼ wⱼ · Cⱼ(c)` ([smolensky-legendre-2006]). -/

/-- A **weighted** constraint: a `Constraint` paired with a real weight (higher is
more important). The Harmonic-Grammar counterpart of a bare `Constraint`.

PROVISIONAL: a weight is the *grammar's* parameter — a weighting of `CON` — not
part of what a constraint is (the same reason `name`/`family` left the constraint).
This pair will give way to a CON-level weight vector `Fin n → ℝ`, with harmony as a
linear functional `-⟪w, violations⟫` — the HG twin of `CON + Ranking` — once the
`CON` object lands. TODO(CON): relocate the weight off the constraint. -/
structure Constraint.Weighted (C : Type*) where
  /-- The underlying violation-counting constraint. -/
  con : Constraint C
  /-- Constraint weight; higher is more important. -/
  weight : ℝ

/-- Harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)`: the negated weighted sum of violations
([smolensky-legendre-2006]); higher is more grammatical. -/
def harmonyScore (cs : List (Constraint.Weighted C)) (c : C) : ℝ :=
  -(cs.map fun wc => wc.weight * (wc.con c : ℝ)).sum

/-- `harmonyScore` as a negated `List.sum` (unfolding lemma for rewriting). -/
theorem harmonyScore_eq_neg_sum (cs : List (Constraint.Weighted C)) (c : C) :
    harmonyScore cs c = -(cs.map fun wc => wc.weight * (wc.con c : ℝ)).sum := rfl

/-- `a` outranks `b` in harmony: `H(a) > H(b)`, the pullback of `<` along
`harmonyScore`. No `Decidable` instance — `ℝ` comparison does not reduce. -/
def harmonyDominates (cs : List (Constraint.Weighted C)) (a b : C) : Prop :=
  harmonyScore cs b < harmonyScore cs a

end Constraints
