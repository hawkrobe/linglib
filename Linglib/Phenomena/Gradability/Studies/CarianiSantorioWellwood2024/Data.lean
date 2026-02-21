/-!
# Cariani, Santorio & Wellwood (2024): Empirical Data

@cite{cariani-santorio-wellwood-2024}

Theory-neutral empirical data on confidence reports from CSW (2024).
These are judgments and entailment patterns that any theory of gradable
attitude adjectives should account for.

## References

- Cariani, F., Santorio, P. & Wellwood, A. (2024). Confidence reports.
  Semantics & Pragmatics 17(14): 1-40.
-/

namespace Phenomena.Gradability.CarianiSantorioWellwood2024

-- ════════════════════════════════════════════════════
-- § 1. Certain/Confident Entailment Pattern (CSW §5.2)
-- ════════════════════════════════════════════════════

/-- CSW (65)-(66): Asymmetric entailment between `certain` and `confident`.

    (65a) "Ann is confident that p, but she isn't certain that p." ✓
    (65b) "Ann is certain that p, but she isn't confident that p." #

    (66a) "Bob has confidence, but not certainty, that p." ✓
    (66b) "Bob has certainty, but not confidence, that p." #

    The pattern: `certain` asymmetrically entails `confident`.
    Both adjectival and nominal forms show the same pattern. -/
structure ConfidenceCertaintyEntailment where
  /-- (65a)/(66a) felicitous: one can have confidence without certainty -/
  confident_without_certain : Bool
  /-- (65b)/(66b) infelicitous: one cannot have certainty without confidence -/
  certain_without_confident : Bool

def csw_entailment : ConfidenceCertaintyEntailment where
  confident_without_certain := true
  certain_without_confident := false

-- ════════════════════════════════════════════════════
-- § 2. Conjunction Fallacy Compatibility (CSW §4.6)
-- ════════════════════════════════════════════════════

/-- CSW (52): Conjunction fallacy — consistent to be confident of a
    conjunction without being confident of a conjunct.

    (52a) "John is not confident that Linda is a bank teller."
    (52b) "John is confident that Linda is a feminist bank teller."

    These can be true together. The confidence ordering need not
    respect logical conjunction (unlike probability functions). -/
structure ConjunctionFallacyDatum where
  /-- Can (52a) and (52b) be true simultaneously? -/
  consistent : Bool

def csw_conjunction_fallacy : ConjunctionFallacyDatum where
  consistent := true

-- ════════════════════════════════════════════════════
-- § 3. Transitivity of Comparative Confidence (CSW §4.6)
-- ════════════════════════════════════════════════════

/-- CSW (57): Comparative confidence is transitive — violating it is
    contradictory.

    "Aidan is more confident that it will rain than that it will snow,
     and more confident that it will be windy than that it will rain.
     #But he's not more confident that it will be windy than that it
     will snow."

    Contrast with (52): the conjunction fallacy is consistent, but
    transitivity violation is contradictory. -/
structure TransitivityDatum where
  /-- Is (57) contradictory? -/
  contradictory : Bool

def csw_transitivity : TransitivityDatum where
  contradictory := true

-- ════════════════════════════════════════════════════
-- § 4. Comparative Equivalence Across Scale-Mates (CSW §5.2)
-- ════════════════════════════════════════════════════

/-- CSW (72): Comparative forms of scale-mates are truth-conditionally
    equivalent.

    (72a) "A is more confident that p than that q."
    (72b) "A is more certain that p than that q."

    These sound approximately equivalent because the comparative discards
    the contrast point and uses only the shared background ordering. -/
structure ComparativeEquivalenceDatum where
  /-- Are (72a) and (72b) approximately equivalent? -/
  equivalent : Bool

def csw_comparative_equivalence : ComparativeEquivalenceDatum where
  equivalent := true

-- ════════════════════════════════════════════════════
-- § 5. Conditional Confidence (CSW §5.1)
-- ════════════════════════════════════════════════════

/-- CSW (61): Conditional confidence — one can self-ascribe conditional
    confidence in p without being unconditionally confident of p.

    (61a) "If Lisa is in town, I am confident that she is at the lab."
    (61b) "I am confident that if Lisa is in town she is at the lab."

    These sound roughly equivalent. The conditional antecedent can
    restrict the background ordering (via a modal base or information
    state parameter). -/
structure ConditionalConfidenceDatum where
  /-- Are (61a) and (61b) roughly equivalent? -/
  roughly_equivalent : Bool

def csw_conditional_confidence : ConditionalConfidenceDatum where
  roughly_equivalent := true

end Phenomena.Gradability.CarianiSantorioWellwood2024
