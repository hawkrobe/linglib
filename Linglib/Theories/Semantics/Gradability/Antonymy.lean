import Linglib.Theories.Semantics.Gradability.Theory
import Linglib.Theories.Semantics.Degree.Core

/-!
# Antonymy: Contradictory vs. Contrary Negation
@cite{krifka-2007b} @cite{cruse-1986} @cite{horn-1989}

Two models of gradable adjective antonymy and their formal properties.

**Contradictory model** (single threshold θ): happy and unhappy partition the
scale. `contradictoryNeg d θ = !positiveMeaning d θ` — double negation
eliminates and "not unhappy" = "happy".

**Contrary model** (two thresholds θ_neg < θ_pos): happy and unhappy leave a
gap. `notContraryNegMeaning d tp ≠ positiveMeaning' d tp` in the gap region.
Double negation does NOT eliminate.

@cite{krifka-2007b} argues that antonyms are *literally* contradictory (single
θ) and the gap emerges through pragmatic strengthening (M-principle). The
contrary model captures the *effective* semantics after strengthening. Both
models are formalized here; the pragmatic derivation connecting them is in
`Phenomena/Negation/Studies/Krifka2007.lean`.

The core operations (`contradictoryNeg`, `contraryNeg`, `inGapRegion`,
`ThresholdPair`, `positiveMeaning'`, `contraryNegMeaning`, `notContraryNegMeaning`)
are defined in `Adjective.Theory`.
-/

set_option autoImplicit false

namespace Semantics.Gradability.Antonymy

open Core.Scale (Degree Threshold Threshold.toNat)
open Semantics.Gradability (ThresholdPair contradictoryNeg
  positiveMeaning' contraryNegMeaning notContraryNegMeaning inGapRegion)
open Semantics.Degree (positiveMeaning antonymMeaning)

-- ════════════════════════════════════════════════════
-- § 1. Contradictory Negation: Involutory (DNE holds)
-- ════════════════════════════════════════════════════

/-- Contradictory negation is the Boolean complement of positive meaning.
    Both compute threshold comparisons: `d ≤ ↑θ` vs `↑θ < d`. -/
theorem contradictory_is_complement {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    contradictoryNeg d θ = !positiveMeaning d θ := by
  simp only [contradictoryNeg, antonymMeaning, positiveMeaning]
  cases h : decide ((θ : Degree max) < d) <;> simp_all

/-- Double contradictory negation eliminates: "not [not happy]" = "happy".

    @cite{krifka-2007b}: this is the LITERAL semantics. If antonyms are
    contradictory, then "not unhappy" and "happy" are synonymous —
    the puzzle that motivates pragmatic strengthening. -/
theorem contradictory_dne {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    !contradictoryNeg d θ = positiveMeaning d θ := by
  rw [contradictory_is_complement]; simp

/-- Under contradictory semantics, the scale is exhaustively partitioned:
    every degree is either positive or in the antonym region, with no gap. -/
theorem contradictory_exhaustive {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    positiveMeaning d θ = true ∨ contradictoryNeg d θ = true := by
  simp only [positiveMeaning, contradictoryNeg, antonymMeaning, decide_eq_true_eq]
  by_cases h : (θ : Degree max) < d
  · exact Or.inl h
  · push_neg at h; exact Or.inr h

-- ════════════════════════════════════════════════════
-- § 2. Contrary Negation: Gap (DNE fails)
-- ════════════════════════════════════════════════════

/-- The gap region is exactly "not unhappy" ∧ "not happy": degrees that escape
    the contrary negative without reaching the positive threshold. -/
theorem gap_eq_not_neg_and_not_pos {max : Nat}
    (d : Degree max) (tp : ThresholdPair max) :
    inGapRegion d tp = (notContraryNegMeaning d tp && !positiveMeaning' d tp) := by
  simp only [inGapRegion, notContraryNegMeaning, positiveMeaning']
  cases h1 : decide ((tp.neg : Degree max) ≤ d) <;>
  cases h2 : decide ((tp.pos : Degree max) < d) <;>
  simp_all [not_lt, not_le]

/-- When the gap is strict (θ_neg < θ_pos), there exists a degree that is
    "not unhappy" but NOT "happy" — double negation through contrary fails.
    Witness: the negative threshold itself (as a degree). -/
theorem contrary_gap_exists {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Degree max) < (tp.pos : Degree max)) :
    ∃ d : Degree max, notContraryNegMeaning d tp = true
                     ∧ positiveMeaning' d tp = false := by
  refine ⟨↑tp.neg, ?_, ?_⟩
  · simp [notContraryNegMeaning]
  · simp only [positiveMeaning', decide_eq_false_iff_not, not_lt]
    exact le_of_lt h

/-- The gap region is nonempty when θ_neg < θ_pos. -/
theorem gap_nonempty {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Degree max) < (tp.pos : Degree max)) :
    ∃ d : Degree max, inGapRegion d tp = true := by
  obtain ⟨d, h1, h2⟩ := contrary_gap_exists tp h
  exact ⟨d, by rw [gap_eq_not_neg_and_not_pos]; simp [h1, h2]⟩

end Semantics.Gradability.Antonymy
