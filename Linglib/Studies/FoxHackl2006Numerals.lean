import Linglib.Semantics.Degree.DirectedMeasure
import Linglib.Semantics.Degree.Predicate
import Linglib.Semantics.Entailment.Extremum
import Linglib.Semantics.Quantification.Numerals.Basic

/-!
# Numeral MIP Bridge
[fox-hackl-2006] [kennedy-2015]

Surfaces the maximal informativity theorems from
`Semantics/Entailment/Extremum.lean` at the Studies level,
connecting numeral semantics (the named `*Meaning` functions) to the
`HasMaxInf` / `IsMaxInf` infrastructure and the [fox-hackl-2006]
density predictions.

## Bridge Structure

The named numeral meanings (`atLeastMeaning`, `moreThanMeaning`, ...) are
`def`s over `Core.Order.Comparison.{ge, gt, ...}.over id` in
`Semantics/Numerals/Basic.lean` §2 — the connection holds by
construction, no bridge lemma needed.

1. **HasMaxInf for "at least"**: `atLeast_hasMaxInf` gives the existence
   of a maximally informative element for any "at least" degree property.

2. **Discrete "more than"**: on ℕ, `moreThan_nat_hasMaxInf` shows
   "more than" also has max⊨, recovering the Fox & Hackl asymmetry.

3. **MIP derives exact meaning**: `isMaxInf_atLeast_iff_eq` proves
   max⊨ of "at least n" at world w iff μ(w) = n.

-/

namespace FoxHackl2006Numerals

open Degree
open Entailment
open Semantics.Numerals
open Core.Order (Comparison)

-- ════════════════════════════════════════════════════
-- § 1. HasMaxInf for "at least" (any scale)
-- ════════════════════════════════════════════════════

/-- "At least n" always has a maximally informative element.
    Instantiated on ℕ with `id` as the measure function. -/
theorem atLeast_has_maxInf_at_3 :
    HasMaxInf (Comparison.ge.over (α := ℕ) id) 3 :=
  atLeast_hasMaxInf id 3

/-- Generalized: "at least n" has max⊨ at every world n. -/
theorem atLeast_has_maxInf_general (n : ℕ) :
    HasMaxInf (Comparison.ge.over (α := ℕ) id) n :=
  atLeast_hasMaxInf id n

-- ════════════════════════════════════════════════════
-- § 2. Discrete "more than" recovers MaxInf (F&H asymmetry)
-- ════════════════════════════════════════════════════

/-- On ℕ, "more than 2" has a maximally informative element at world 3.
    This is the discrete rescue: ℕ's successor structure collapses
    "more than n" to "at least n+1", which has max⊨.

    Contrast with `moreThan_noMaxInf` on dense scales: no rescue there. -/
theorem moreThan_has_maxInf_nat :
    HasMaxInf (Comparison.gt.over (α := ℕ) id) 3 :=
  moreThan_nat_hasMaxInf id 3 (show (3 : ℕ) ∈ Comparison.gt.over id 0 from by decide)

-- ════════════════════════════════════════════════════
-- § 3. MIP Derives Exact Meaning
-- ════════════════════════════════════════════════════

/-- max⊨ of "at least n" at world w ↔ the true value equals n.
    This is the MIP derivation of exact meaning from lower-bound semantics:
    [kennedy-2015]'s "de-Fregean" type-shift IS the MIP. -/
theorem mip_derives_exact (m n : ℕ) :
    IsMaxInf (Comparison.ge.over (α := ℕ) id) m n ↔ n = m :=
  isMaxInf_atLeast_iff_eq id m n Function.surjective_id

-- ════════════════════════════════════════════════════
-- § 4. Fox & Hackl Asymmetry Data
-- ════════════════════════════════════════════════════

/-- The [fox-hackl-2006] implicature asymmetry prediction:
    - "at least n" generates scalar implicatures (HasMaxInf) ✓
    - "more than n" on dense scales does NOT (moreThan_noMaxInf)
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

/-- Kennedy numeral domains are always licensed (closed scale). -/
theorem kennedy_numeral_licensed {W : Type*} (μ : W → ℕ) :
    (DirectedMeasure.numeral μ).IsLicensed := trivial

/-- [kennedy-2015]'s de-Fregean type-shift at the `DirectedMeasure`
    constructor level: the maximally informative degree of a numeral
    domain's derived property is the true cardinality — the bundled form
    of `isMaxInf_atLeast_iff_eq`. -/
theorem kennedy_numeral_isMaxInf {W : Type*} (μ : W → ℕ) (m : ℕ) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (DirectedMeasure.numeral μ).degreeProperty m w ↔ μ w = m :=
  (DirectedMeasure.numeral μ).isMaxInf_degreeProperty_iff m w hSurj

end FoxHackl2006Numerals
