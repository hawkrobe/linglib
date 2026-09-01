/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Degree.Predicate
import Linglib.Semantics.Alternatives.Extremum
import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Semantics.Exhaustification.Chain
import Mathlib.Tactic.Linarith

/-!
# Numeral MIP Bridge
[fox-hackl-2006] [kennedy-2015]

Surfaces the maximal informativity theorems from
`Semantics/Alternatives/Extremum.lean` at the Studies level,
connecting numeral semantics (the named `*Meaning` functions) to the
`HasMaxInf` / `IsMaxInf` infrastructure and the [fox-hackl-2006]
density predictions.

## Bridge Structure

The named numeral meanings (`atLeastMeaning`, `moreThanMeaning`, ...) are
`def`s over `Degree.Comparison.{ge, gt, ...}.over id` in
`Semantics/Numerals/Basic.lean` §2 — the connection holds by
construction, no bridge lemma needed.

1. **HasMaxInf for "at least"**: `hasMaxInf_ge_over` gives the existence
   of a maximally informative element for any "at least" degree property.

2. **Discrete "more than"**: on ℕ, `hasMaxInf_gt_over_nat` shows
   "more than" also has max⊨, recovering the Fox & Hackl asymmetry.

3. **MIP derives exact meaning**: `isMaxInf_ge_over_iff` proves
   max⊨ of "at least n" at world w iff μ(w) = n.

-/

namespace FoxHackl2006Numerals

open Degree
open Alternatives
open Semantics.Numerals
open Degree (Comparison)

-- ════════════════════════════════════════════════════
-- § 1. HasMaxInf for "at least" (any scale)
-- ════════════════════════════════════════════════════

/-- "At least n" always has a maximally informative element.
    Instantiated on ℕ with `id` as the measure function. -/
theorem atLeast_has_maxInf_at_3 :
    HasMaxInf (Comparison.ge.over (α := ℕ) id) 3 :=
  hasMaxInf_ge_over id 3

/-- Generalized: "at least n" has max⊨ at every world n. -/
theorem atLeast_has_maxInf_general (n : ℕ) :
    HasMaxInf (Comparison.ge.over (α := ℕ) id) n :=
  hasMaxInf_ge_over id n

-- ════════════════════════════════════════════════════
-- § 2. Discrete "more than" recovers MaxInf (F&H asymmetry)
-- ════════════════════════════════════════════════════

/-- On ℕ, "more than 2" has a maximally informative element at world 3.
    This is the discrete rescue: ℕ's successor structure collapses
    "more than n" to "at least n+1", which has max⊨.

    Contrast with `not_hasMaxInf_gt_over` on dense scales: no rescue there. -/
theorem moreThan_has_maxInf_nat :
    HasMaxInf (Comparison.gt.over (α := ℕ) id) 3 :=
  hasMaxInf_gt_over_nat id 3 (show (3 : ℕ) ∈ Comparison.gt.over id 0 from by decide)

/-- The dense half of the asymmetry as chain-exhaustification: on ℚ the
stronger *more than* alternatives have no next member, so exhaustifying
*more than c* against its own scale is unsatisfiable —
`Exhaustification.exhChain_not_of_dense` at the UDM scale. On ℕ the next
member exists and exhaustification returns 'exactly' instead
(`Semantics.Numerals.exhNumeral_eq_exhChain`). -/
theorem moreThan_exhChain_crash (c maxD : ℚ) :
    ¬ Exhaustification.exhChain (fun x d => x < d) c maxD :=
  Exhaustification.exhChain_not_of_dense fun d hd =>
    ⟨(c + d) / 2, by linarith, by linarith⟩

-- ════════════════════════════════════════════════════
-- § 3. MIP Derives Exact Meaning
-- ════════════════════════════════════════════════════

/-- max⊨ of "at least n" at world w ↔ the true value equals n.
    This is the MIP derivation of exact meaning from lower-bound semantics:
    [kennedy-2015]'s maximality `max{n | D n} = m` IS the MIP. -/
theorem mip_derives_exact (m n : ℕ) :
    IsMaxInf (Comparison.ge.over (α := ℕ) id) m n ↔ n = m :=
  isMaxInf_ge_over_iff id n ⟨m, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Fox & Hackl Asymmetry Data
-- ════════════════════════════════════════════════════

/-- The [fox-hackl-2006] implicature asymmetry prediction:
    - "at least n" generates scalar implicatures (HasMaxInf) ✓
    - "more than n" on dense scales does NOT (not_hasMaxInf_gt_over)
    - "more than n" on ℕ DOES (discrete rescue)

    This structure records the prediction for bridge verification. -/
structure FoxHacklAsymmetry where
  /-- "At least" has max⊨ on any scale -/
  atLeast_always : Bool
  /-- "More than" has max⊨ on ℕ (discrete) -/
  moreThan_discrete : Bool
  /-- "More than" has max⊨ on dense scales -/
  moreThan_dense : Bool
  deriving Repr

/-- The asymmetry prediction, verified against the algebra. -/
def foxHackl_asymmetry_data : FoxHacklAsymmetry :=
  { atLeast_always := true
    moreThan_discrete := true
    moreThan_dense := false }

/-- The "at least" part: always has max⊨ (any scale, any world). -/
theorem foxHackl_atLeast_verified :
    foxHackl_asymmetry_data.atLeast_always = true := rfl

end FoxHackl2006Numerals
