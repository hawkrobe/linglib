import Linglib.Phenomena.Comparison.Comparative.Data
import Linglib.Phenomena.Comparison.Comparative.Differential
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Core.Scales.Scale

/-!
# Kennedy Framework on Comparative Data
@cite{kennedy-2007} @cite{kennedy-mcnally-2005}

Bridge connecting @cite{kennedy-2007}'s measure function approach to the
comparative construction data in `Phenomena/Comparison/Comparative/`.

## Key Bridges

1. **Morphological distribution**: Kennedy's ⟦-er⟧ and ⟦more⟧ are the
   same degree morpheme (comparative DegP head) with different
   spell-out — the framework is morphology-neutral.

2. **Scale structure predictions**: Kennedy's Interpretive Economy
   predicts that open-scale comparatives use contextual standards
   while closed-scale comparatives use endpoint standards.

3. **Measure phrase licensing**: Kennedy's approach naturally accounts
   for measure phrase differentials ("3 inches taller") because the
   degree argument IS a measure.

-/

namespace Phenomena.Comparison.Comparative.KennedyBridge

open Semantics.Degree
open Core.Scale (Boundedness)

-- ════════════════════════════════════════════════════
-- § 1. Interpretive Economy Predictions
-- ════════════════════════════════════════════════════

/-- Open-scale adjectives (Kennedy's "relative"; Class A here) use contextual standards. -/
theorem open_scale_contextual :
    interpretiveEconomy .open_ = .contextual := rfl

/-- Closed-scale adjectives (Kennedy's "absolute"; Class B here) use endpoint standards. -/
theorem closed_scale_endpoint :
    interpretiveEconomy .closed = .maxEndpoint := rfl

/-- Lower-bounded adjectives use minimum endpoint. -/
theorem lower_bounded_minEndpoint :
    interpretiveEconomy .lowerBounded = .minEndpoint := rfl

-- ════════════════════════════════════════════════════
-- § 3. Measure Phrase Licensing
-- ════════════════════════════════════════════════════

/-- Kennedy's approach predicts measure phrases are licensed when the
    degree type has subtraction (ratio/interval scale). The comparative
    data `measurePhraseExamples` reflects this: height (ratio) ✓,
    beauty (open, no conventional unit) ✗.

    This is a type-theoretic prediction: `differentialComparative`
    requires `ℚ` (with subtraction), not just an ordered type. -/
theorem measure_phrases_require_subtraction :
    ∀ d ∈ Phenomena.Comparison.Comparative.Differential.measurePhraseExamples,
      d.acceptable = true → d.scaleType = "ratio (height)" ∨
                             d.scaleType = "interval (temperature)" := by
  intro d hd hacc
  simp [Phenomena.Comparison.Comparative.Differential.measurePhraseExamples,
        Phenomena.Comparison.Comparative.Differential.MeasurePhraseComparativeDatum.acceptable,
        Phenomena.Comparison.Comparative.Differential.MeasurePhraseComparativeDatum.scaleType] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp_all

end Phenomena.Comparison.Comparative.KennedyBridge
