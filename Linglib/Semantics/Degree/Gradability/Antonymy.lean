import Linglib.Semantics.Degree.Gradability.Basic
import Linglib.Semantics.Degree.Basic

/-!
# Antonymy: Contradictory vs. Contrary Negation
[krifka-2007b] [cruse-1986] [horn-1989]

Two models of gradable adjective antonymy and their formal properties.

**Contradictory model** (single threshold θ): happy and unhappy partition the
scale. `contradictoryNeg d θ = !positiveMeaning d θ` — double negation
eliminates and "not unhappy" = "happy".

**Contrary model** (two thresholds θ_neg < θ_pos): happy and unhappy leave a
gap. `notContraryNegMeaning d tp ≠ positiveMeaning' d tp` in the gap region.
Double negation does NOT eliminate.

[krifka-2007b] argues that antonyms are *literally* contradictory (single
θ) and the gap emerges through pragmatic strengthening (M-principle). The
contrary model captures the *effective* semantics after strengthening. Both
models are formalized here; the pragmatic derivation connecting them is in
`Studies/Krifka2007.lean`.

The core operations (`contradictoryNeg`, `contraryNeg`, `inGapRegion`,
`ThresholdPair`, `positiveMeaning'`, `contraryNegMeaning`, `notContraryNegMeaning`)
are defined in `Adjective.Theory`.
-/

set_option autoImplicit false

namespace Semantics.Gradability.Antonymy

open Degree (Degree Threshold Threshold.toNat)
open Semantics.Gradability (ThresholdPair contradictoryNeg
  positiveMeaning' contraryNegMeaning notContraryNegMeaning inGapRegion)
open Degree (positiveMeaning antonymMeaning)

-- ════════════════════════════════════════════════════
-- § 1. Contradictory Negation: Involutory (DNE holds)
-- ════════════════════════════════════════════════════

/-- Contradictory negation is the propositional complement of positive meaning.
    Both compute threshold comparisons: `d ≤ ↑θ` vs `↑θ < d`. -/
@[simp] theorem contradictory_is_complement {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    contradictoryNeg d θ ↔ ¬ positiveMeaning d θ := by
  simp only [contradictoryNeg, antonymMeaning, positiveMeaning, not_lt]

/-- Double contradictory negation eliminates: "not [not happy]" = "happy".

    [krifka-2007b]: this is the LITERAL semantics. If antonyms are
    contradictory, then "not unhappy" and "happy" are synonymous —
    the puzzle that motivates pragmatic strengthening. -/
theorem contradictory_dne {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    ¬ contradictoryNeg d θ ↔ positiveMeaning d θ := by
  rw [contradictory_is_complement, not_not]

/-- Under contradictory semantics, the scale is exhaustively partitioned:
    every degree is either positive or in the antonym region, with no gap. -/
theorem contradictory_exhaustive {max : Nat}
    (d : Degree max) (θ : Threshold max) :
    positiveMeaning d θ ∨ contradictoryNeg d θ := by
  by_cases h : positiveMeaning d θ
  · exact Or.inl h
  · exact Or.inr ((contradictory_is_complement d θ).mpr h)

-- ════════════════════════════════════════════════════
-- § 2. Contrary Negation: Gap (DNE fails)
-- ════════════════════════════════════════════════════

/-- The gap region is exactly "not unhappy" ∧ "not happy": degrees that escape
    the contrary negative without reaching the positive threshold. -/
@[simp] theorem gap_iff_not_neg_and_not_pos {max : Nat}
    (d : Degree max) (tp : ThresholdPair max) :
    inGapRegion d tp ↔ notContraryNegMeaning d tp ∧ ¬ positiveMeaning' d tp := by
  simp only [inGapRegion, notContraryNegMeaning, positiveMeaning',
             Degree.positiveMeaning, not_lt]

/-- When the gap is strict (θ_neg < θ_pos), there exists a degree that is
    "not unhappy" but NOT "happy" — double negation through contrary fails.
    Witness: the negative threshold itself (as a degree). -/
theorem contrary_gap_exists {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Degree max) < (tp.pos : Degree max)) :
    ∃ d : Degree max, notContraryNegMeaning d tp ∧ ¬ positiveMeaning' d tp := by
  refine ⟨↑tp.neg, le_refl _, ?_⟩
  simp only [positiveMeaning', Degree.positiveMeaning, not_lt]
  exact le_of_lt h

/-- The gap region is nonempty when θ_neg < θ_pos. -/
theorem gap_nonempty {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Degree max) < (tp.pos : Degree max)) :
    ∃ d : Degree max, inGapRegion d tp := by
  obtain ⟨d, h1, h2⟩ := contrary_gap_exists tp h
  exact ⟨d, (gap_iff_not_neg_and_not_pos d tp).mpr ⟨h1, h2⟩⟩

end Semantics.Gradability.Antonymy
