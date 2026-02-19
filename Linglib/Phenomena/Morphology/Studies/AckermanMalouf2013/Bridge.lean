import Linglib.Phenomena.Morphology.Typology
import Linglib.Theories.Morphology.WP.LCEC

/-!
# Ackerman & Malouf (2013): Bridge Theorems @cite{ackerman-malouf-2013}

Verification theorems connecting the cross-linguistic typological data
to the LCEC predictions. Each theorem proves that a language's reported
I-complexity falls below the LCEC threshold.

## Structure

- §1: Per-language LCEC verification (all 10 languages)
- §2: E-complexity / I-complexity dissociation
- §3: Mazatec case study (observed vs. random baseline)

## References

- Ackerman, F. & Malouf, R. (2013). Morphological Organization: The Low
  Conditional Entropy Conjecture. *Language* 89(3), 429–464.
- Carstairs-McCarthy, A. (2010). The Evolution of Morphology. OUP.
-/

namespace Phenomena.Morphology.AckermanMalouf2013

open Phenomena.Morphology.Typology

-- ============================================================================
-- §1. Per-language LCEC Verification
-- ============================================================================

/-! Each language's reported I-complexity is below the 1-bit threshold.
    These are "per-datum verification theorems" in linglib's sense:
    changing a language's avgCondEntropy breaks exactly the corresponding
    theorem. -/

theorem fur_lcec : fur.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem ngiti_lcec : ngiti.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem nuer_lcec : nuer.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem kwerba_lcec : kwerba.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem chinantec_lcec : chinantec.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem mazatec_lcec : mazatec.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem finnish_lcec : finnish.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem german_lcec : german.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem russian_lcec : russian.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem spanish_lcec : spanish.avgCondEntropy ≤ lcecThreshold := by native_decide

/-- All 10 languages satisfy the LCEC. -/
theorem all_satisfy_lcec :
    ∀ l ∈ ackermanMalouf2013, l.avgCondEntropy ≤ lcecThreshold := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals native_decide

-- ============================================================================
-- §2. E-complexity / I-complexity Dissociation
-- ============================================================================

/-! The LCEC's key prediction: E-complexity and I-complexity are dissociated.
    A language can have enormous E-complexity but low I-complexity. -/

/-- Mazatec has maximal E-complexity in the sample (109 classes). -/
theorem mazatec_max_eComplexity :
    ∀ l ∈ ackermanMalouf2013, l.numClasses ≤ mazatec.numClasses := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [mazatec, fur, ngiti, nuer, kwerba, chinantec, finnish, german, russian, spanish]

/-- Mazatec's I-complexity is still below 1 bit despite 109 classes. -/
theorem mazatec_high_e_low_i :
    mazatec.numClasses = 109 ∧ mazatec.avgCondEntropy ≤ 1 :=
  ⟨rfl, by native_decide⟩

/-- Kwerba has minimal E-complexity (2 classes) but its I-complexity
    is *not* the lowest — German (7 classes) has lower I-complexity.
    This shows E-complexity doesn't predict I-complexity in either direction. -/
theorem eComplexity_doesnt_predict_iComplexity :
    kwerba.numClasses < german.numClasses ∧
    german.avgCondEntropy < kwerba.avgCondEntropy :=
  ⟨by simp [kwerba, german], by native_decide⟩

/-- Spanish has only 3 classes but 57 cells — yet its I-complexity is
    the lowest in the sample (0.003 bits). More cells with fewer classes
    means more implicative structure. -/
theorem spanish_minimal_iComplexity :
    ∀ l ∈ ackermanMalouf2013, spanish.avgCondEntropy ≤ l.avgCondEntropy := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals native_decide

-- ============================================================================
-- §3. Mazatec Case Study: Observed vs. Random Baseline
-- ============================================================================

/-! The Mazatec case study (§4 of the paper) demonstrates that the observed
    I-complexity is far below what random assignment of inflection-class
    patterns would produce. -/

/-- Mazatec's observed I-complexity is far below the random baseline.
    Observed: 0.709 bits. Random permutation baseline: ~5.25 bits.
    The observed value is less than 14% of the random baseline. -/
theorem mazatec_well_below_random :
    mazatec.avgCondEntropy < mazatecRandomBaseline := by native_decide

/-- The ratio of observed to random I-complexity is less than 1/7.
    (0.709 / 5.25 ≈ 0.135, i.e., ~13.5% of random) -/
theorem mazatec_ratio_to_random :
    mazatec.avgCondEntropy * 7 < mazatecRandomBaseline := by native_decide

/-- Mazatec has nonzero I-complexity: it violates Carstairs-McCarthy's
    (2010) synonymy avoidance but satisfies the LCEC. This witnesses
    that the LCEC is strictly weaker than synonymy avoidance. -/
theorem mazatec_violates_synonymyAvoidance :
    mazatec.avgCondEntropy > 0 := by native_decide

end Phenomena.Morphology.AckermanMalouf2013
