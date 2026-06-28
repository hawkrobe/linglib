/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.ForbidPairs
import Linglib.Core.Computability.NonRegular.AnBn

/-!
# OT–Subregular Bridge: Bound and Counterexample

A `Constraint`'s zero-set — `{ w | c w = 0 }` — sometimes lands
in a subregular class (TSL_2, SP_2, …) and sometimes does not. This file
makes the bound visible:

1. **Existing bridges, in zero-set form**: every `mkForbidPairsOnTier`
   constraint has a TSL_2 zero-set (`mkForbidPairsOnTier_zeroSet_eq`).
   Restatement of `mkForbidPairsOnTier_zero_iff_in_lang` in `Language α`
   form so it composes with mathlib's `Language.IsRegular`.

2. **Supraregular counterexample**: there is a `Constraint (List AB)`
   whose zero-set is the classical non-regular language `{ aⁿ bⁿ | n ≥ 0 }`
   (`exists_namedConstraint_zeroSet_not_isRegular`). Shows the bridge
   cannot be stated as "every Constraint has a subregular zero-set"
   — only constraints in specific schema classes (forbidden-pair on
   tier, OCP on tier, agree on tier, …) inherit the bridge.

The argument for non-regularity uses mathlib's
`Language.IsRegular.finite_range_leftQuotient`: distinct prefixes `aⁿ`
give distinct left quotients of `{ aⁿ bⁿ }`, so the range of
`leftQuotient` is infinite, contradicting regularity. This is the
classical Myhill–Nerode argument [nerode-1958] [myhill-1957].

Phonologically the takeaway is *negative*: `Constraint`s are too
expressive to be classified by subregular complexity alone. Phonologists
who want a subregular guarantee on their constraint set must restrict to
one of the schema-specific constructors with a known bridge —
`mkForbidPairsOnTier`, `mkOCPOnTier`, `mkAgreeOnTier`,
`mkForbidSingletonOnTier`. The `mkMarkGrad` escape hatch (arbitrary
violation count) admits supraregular constraints.

This file is the OT-side dual of the existing class-specific bridges in
`Phonology/Subregular/ForbidPairs.lean`, `OCP.lean`, `Agree.lean`. The
positive bridges show *which* constraint constructors land inside
TSL_2; this file shows *that* the OT vocabulary is broader than the
subregular hierarchy.
-/

-- ============================================================================
-- § 1. (Constraint zero-set API moved to Phonology/Constraint/OT/Basic.lean
--       in PR-7d to make it visible to non-phonology consumers.)
-- ============================================================================

namespace Subregular.OTBound

open OptimalityTheory
open Constraints OptimalityTheory

-- ============================================================================
-- § 2. Existing bridges, restated in zero-set form
-- ============================================================================

variable {α : Type}

/-- **Zero-set bridge** (forbidden-pair on tier): the zero-set of a
forbidden-pair markedness constraint *is* the language of the
corresponding TSL_2 grammar. Restatement of
`mkForbidPairsOnTier_zero_iff_in_lang` (with `extract := id`) in
`Language α` form so downstream regularity arguments can use the
zero-set side directly. -/
theorem mkForbidPairsOnTier_zeroSet_eq
    (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] :
    (mkForbidPairsOnTier R (TierProjection.byClass p) (id : List α → List α)).zeroSet =
      (TSLGrammar.ofForbiddenPairs R p).lang := by
  ext w
  exact mkForbidPairsOnTier_zero_iff_in_lang R p id w

-- ============================================================================
-- § 3. Supraregular counterexample: `{ aⁿ bⁿ | n ≥ 0 }`
-- ============================================================================
-- The non-regular witness language `balancedAB` (= `{ aⁿbⁿ | n ≥ 0 }`)
-- and the Myhill–Nerode non-regularity argument live in
-- `Core/Computability/NonRegular/AnBn.lean` (PR-11). This file consumes
-- `IsBalanced`, `balancedAB`, and `balancedAB_not_isRegular` from there.

-- ============================================================================
-- § 4. Headline existence theorem
-- ============================================================================

/-- The supraregular `Constraint`: violates iff the candidate is not
balanced. Built via `mkMarkGrad` (the escape-hatch constructor that
admits arbitrary `Nat`-valued violation counts) — *not* via any of the
schema constructors with a TSL_k/SP_k/BTC bridge. -/
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

/-- **Headline**: there exists a `Constraint` whose zero-set is not
regular. The OT→subregular bridge cannot be stated as "every
Constraint has a subregular zero-set" — class-specific schema
restrictions are necessary. The witness is built via the
`mkMarkGrad` escape hatch with a `{ aⁿ bⁿ }`-membership predicate as
the violation count. -/
theorem exists_namedConstraint_zeroSet_not_isRegular :
    ∃ c : Constraint (List AB), ¬ c.zeroSet.IsRegular := by
  refine ⟨supraregularConstraint, ?_⟩
  rw [supraregularConstraint_zeroSet]
  exact balancedAB_not_isRegular

end Subregular.OTBound
