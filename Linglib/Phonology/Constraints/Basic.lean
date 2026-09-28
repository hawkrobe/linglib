/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Constraints.Defs
public import Linglib.Phonology.Subregular.ForbiddenPairs

/-!
# Forbidden-pair markedness constraints

Constructors for the framework-neutral `Constraint C = C → ℕ` of Optimality Theory
([prince-smolensky-1993]) and Harmonic Grammar whose content goes beyond a single predicate.

**Binary constraints are just `Constraint.binary P`** (`Defs`): MAX, DEP, IDENT,
ALIGN, \*STRUC differ only in the predicate you pass and the `def` name you give —
post-`family`-deletion they are the *same* function, so there is no `mkMax`/`mkDep`/…
The faithfulness/markedness family is recovered structurally
(`OptimalityTheory.Correspondence`), not from a constructor. Contextual
faithfulness ([coetzee-pater-2011]) is `Constraint.binary (fun c => deleted c ∧ ctx c)`.

This file provides the **gradient forbidden-pair** constraints on strings, which carry genuine
adjacency logic: `Constraint.forbidPairs R` and its identity and non-identity instances, the OCP
([goldsmith-1976], [mccarthy-1986]) and AGREE. A constraint on candidates of another type, or on
a tier, is not a separate constructor but the `Constraint.comap` of a string constraint along the
candidate's string or along erasure of the off-tier symbols ([heinz-rawal-tanner-2011]).

## References

* [A. Prince and P. Smolensky, *Optimality Theory: Constraint Interaction in Generative
  Grammar* (1993)][prince-smolensky-1993]
* [A. W. Coetzee and J. Pater, *The Place of Variation in Phonological Theory*
  (2011)][coetzee-pater-2011]
* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [J. J. McCarthy, *OCP Effects: Gemination and Antigemination* (1986)][mccarthy-1986]
* [J. Heinz, C. Rawal and H. G. Tanner, *Tier-based Strictly Local Constraints for Phonology*
  (2011)][heinz-rawal-tanner-2011]
* [I. Berent, *Three arguments for abstraction in phonology* (2026)][berent-2026]
-/

@[expose] public section

namespace Constraints

-- `countAdjacent` is alphabet-generic list combinatorics living in `Subregular`;
-- open it file-locally (don't relay a Core name through `Constraints`).
open Subregular (countAdjacent)

variable {α β : Type*}

/-- The forbidden-pair constraint on strings, with one violation for each adjacent pair `(a, b)`
satisfying `R a b`. -/
def Constraint.forbidPairs (R : α → α → Prop) [DecidableRel R] : Constraint (List α) :=
  countAdjacent R

/-- The OCP ([goldsmith-1976], [mccarthy-1986]), the forbidden-pair constraint against adjacent
identical elements, polymorphic over the feature type ([berent-2026]). -/
def Constraint.ocp [DecidableEq α] : Constraint (List α) := Constraint.forbidPairs (· = ·)

/-- AGREE, the forbidden-pair constraint against adjacent distinct elements and the dual of
`Constraint.ocp`. -/
def Constraint.agree [DecidableEq α] : Constraint (List α) := Constraint.forbidPairs (· ≠ ·)

namespace Constraint

theorem ocp_cons_self [DecidableEq α] (a : α) (w : List α) :
    ocp (a :: a :: w) = 1 + ocp (a :: w) := by
  simp [ocp, forbidPairs, countAdjacent]

theorem ocp_cons_of_ne [DecidableEq α] {a b : α} (h : a ≠ b) (w : List α) :
    ocp (a :: b :: w) = ocp (b :: w) := by
  simp [ocp, forbidPairs, countAdjacent, h]

/-- The OCP is invariant under an injective relabelling of the elements. -/
theorem ocp_map [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (w : List α) : ocp (w.map f) = ocp w :=
  Subregular.countAdjacent_map (· = ·) (S := (· = ·)) (fun _ _ ↦ hf.eq_iff) w

end Constraint

end Constraints
