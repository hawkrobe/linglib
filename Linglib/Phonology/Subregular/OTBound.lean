/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenPairs
public import Linglib.Core.Computability.NonRegular.AnBn

/-!
# OT–Subregular Bridge: Bound and Counterexample

A `Constraint`'s zero set `{ w | c w = 0 }` sometimes lands in a subregular class (TSL₂, SP₂,
…) and sometimes does not. This file makes the bound visible.

1. The forbidden-pair constraint on any tier has a TSL₂ zero set ([heinz-rawal-tanner-2011];
   `Constraint.zeroSet_comap_filter_forbidPairs`, with its OCP and AGREE instances).
2. Some `Constraint (List AB)` has the classical non-regular zero set `{ aⁿ bⁿ | n ≥ 0 }`
   (`exists_namedConstraint_zeroSet_not_isRegular`), so the bridge cannot be stated as "every
   constraint has a subregular zero set". Only the forbidden-pair constraints
   (`Constraint.forbidPairs`, `Constraint.ocp`, `Constraint.agree`) inherit it.

Non-regularity is the Myhill–Nerode argument of `Core/Computability/NonRegular/AnBn.lean`:
distinct prefixes `aⁿ` give distinct left quotients of `{ aⁿ bⁿ }`, so the range of
`leftQuotient` is infinite.

Phonologically the takeaway is negative: `Constraint`s are too expressive to be classified by
subregular complexity alone, and a subregular guarantee on a constraint set needs the
schema-specific constructors, since an arbitrary violation count admits supraregular zero sets. The
positive bridges are in `OptimalityTheory/Constraint/ForbiddenPairs.lean`, `OCP.lean` and
`Agree.lean`.

## References

* [J. Heinz, C. Rawal and H. G. Tanner, *Tier-based Strictly Local Constraints for Phonology*
  (2011)][heinz-rawal-tanner-2011]
-/

@[expose] public section

namespace Subregular.OTBound

open OptimalityTheory

/-! ### A supraregular constraint -/

/-- The constraint violated once by every unbalanced candidate. It is an arbitrary violation
count, not an instance of the forbidden-pair schema, whose zero set is always a TSL₂ language
(`Constraint.zeroSet_comap_filter_forbidPairs`). -/
def supraregularConstraint : Constraint (List AB) :=
  (fun w => if IsBalanced w then 0 else 1)

@[simp] lemma supraregularConstraint_eval (w : List AB) :
    supraregularConstraint w = if IsBalanced w then 0 else 1 := rfl

/-- The zero-set of `supraregularConstraint` is exactly `balancedAB` —
the classical non-regular `{ aⁿ bⁿ }`. -/
theorem supraregularConstraint_zeroSet :
    supraregularConstraint.zeroSet = balancedAB := by
  ext w
  show supraregularConstraint w = 0 ↔ IsBalanced w
  rw [supraregularConstraint_eval]
  by_cases h : IsBalanced w <;> simp [h]

/-- Some `Constraint` has a non-regular zero set, so the OT-to-subregular bridge needs the
schema-specific constructors. The witness counts one violation off `{ aⁿ bⁿ }`. -/
theorem exists_namedConstraint_zeroSet_not_isRegular :
    ∃ c : Constraint (List AB), ¬ c.zeroSet.IsRegular := by
  refine ⟨supraregularConstraint, ?_⟩
  rw [supraregularConstraint_zeroSet]
  exact balancedAB_not_isRegular

end Subregular.OTBound
