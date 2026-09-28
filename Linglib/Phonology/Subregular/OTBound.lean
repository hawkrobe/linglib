/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.ForbidPairs
public import Linglib.Core.Computability.NonRegular.AnBn

/-!
# OT–Subregular Bridge: Bound and Counterexample

A `Constraint`'s zero set `{ w | c w = 0 }` sometimes lands in a subregular class (TSL₂, SP₂,
…) and sometimes does not. This file makes the bound visible.

1. Every `mkForbidPairsOnTier` constraint has a TSL₂ zero set ([heinz-rawal-tanner-2011];
   `mkForbidPairsOnTier_zeroSet_eq`), the `Language α` form of
   `mkForbidPairsOnTier_zero_iff_in_language`, which composes with mathlib's
   `Language.IsRegular`.
2. Some `Constraint (List AB)` has the classical non-regular zero set `{ aⁿ bⁿ | n ≥ 0 }`
   (`exists_namedConstraint_zeroSet_not_isRegular`), so the bridge cannot be stated as "every
   constraint has a subregular zero set". Only the schema-specific constructors
   (`mkForbidPairsOnTier`, `mkOCPOnTier`, `mkAgreeOnTier`) inherit it.

Non-regularity is the Myhill–Nerode argument of `Core/Computability/NonRegular/AnBn.lean`:
distinct prefixes `aⁿ` give distinct left quotients of `{ aⁿ bⁿ }`, so the range of
`leftQuotient` is infinite.

Phonologically the takeaway is negative: `Constraint`s are too expressive to be classified by
subregular complexity alone, and a subregular guarantee on a constraint set needs the
schema-specific constructors, since an arbitrary violation count admits supraregular zero sets.
The positive bridges are in `ForbidPairs.lean`, `OCP.lean` and `Agree.lean`.

## References

* [J. Heinz, C. Rawal and H. G. Tanner, *Tier-based Strictly Local Constraints for Phonology*
  (2011)][heinz-rawal-tanner-2011]
-/

@[expose] public section

namespace Subregular.OTBound

open Constraints OptimalityTheory

variable {α : Type}

/-- The zero set of a forbidden-pair markedness constraint is the language of the corresponding
TSL₂ grammar, `mkForbidPairsOnTier_zero_iff_in_language` with `extract := id` in `Language α`
form. -/
theorem mkForbidPairsOnTier_zeroSet_eq
    (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] :
    (mkForbidPairsOnTier R p (id : List α → List α)).zeroSet =
      (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language := by
  ext w
  exact mkForbidPairsOnTier_zero_iff_in_language R p id w

/-! ### A supraregular constraint -/

/-- The constraint violated once by every unbalanced candidate. It is an arbitrary violation
count, not an instance of the forbidden-pair schema, whose zero set is always a TSL₂ language
(`mkForbidPairsOnTier_zeroSet_eq`). -/
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
