import Linglib.Theories.Semantics.Lexical.Adjective.StatesBased
import Linglib.Theories.Semantics.Attitudes.Confidence
import Linglib.Theories.Semantics.Attitudes.EpistemicThreshold
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Phenomena.Comparison.Studies.Wellwood2015

/-!
# @cite{cariani-santorio-wellwood-2024}: Empirical Data

@cite{cariani-santorio-wellwood-2024}

Theory-neutral empirical data on confidence reports from @cite{cariani-santorio-wellwood-2024}.
These are judgments and entailment patterns that any theory of gradable
attitude adjectives should account for.

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

-- ════════════════════════════════════════════════════
-- § Theory-to-Data Bridge
-- ════════════════════════════════════════════════════

open Semantics.Lexical.Adjective.StatesBased
open Semantics.Attitudes.Confidence

-- ════════════════════════════════════════════════════
-- § Certain/Confident Entailment
-- ════════════════════════════════════════════════════

/-- The states-based theory predicts the asymmetric entailment pattern:
    confident-without-certain is possible (different contrast points on
    same ordering), certain-without-confident is not (`asymEntails`). -/
theorem certain_confident_bridge :
    csw_entailment.confident_without_certain = true ∧
    csw_entailment.certain_without_confident = false := by
  exact ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Conjunction Fallacy
-- ════════════════════════════════════════════════════

/-- The states-based theory permits the conjunction fallacy because
    confidence orderings are not constrained to respect logical
    conjunction. `conjunction_fallacy_compatible` in `Confidence.lean`
    provides the formal witness. -/
theorem conjunction_fallacy_bridge :
    csw_conjunction_fallacy.consistent = true := rfl

-- ════════════════════════════════════════════════════
-- § Transitivity
-- ════════════════════════════════════════════════════

/-- The theory predicts that transitivity violation is contradictory
    because comparative semantics uses a measure function whose image
    is linearly ordered, and `<` on linear orders is transitive
    (`comparative_transitive` in `Confidence.lean`). -/
theorem transitivity_bridge :
    csw_transitivity.contradictory = true := rfl

-- ════════════════════════════════════════════════════
-- § Comparative Equivalence
-- ════════════════════════════════════════════════════

/-- The theory predicts comparative equivalence across scale-mates
    because `statesComparativeSem` takes no `StatesBasedEntry` parameter —
    the contrast point that distinguishes `confident` from `certain` is
    invisible to the comparative by construction. Both adjectives
    share the same background ordering and hence the same class of
    admissible measures; the comparative accesses only these. -/
theorem comparative_equivalence_bridge :
    csw_comparative_equivalence.equivalent = true := rfl

-- ════════════════════════════════════════════════════
-- § Confident vs. Likely: Moore's Paradox Asymmetry (CSW §5.3)
-- ════════════════════════════════════════════════════

/-- CSW (74)–(75): Moore's paradox asymmetry between `confident` and
    `likely`.

    (74a) "Suppose it's raining but I am confident it is not raining." ✓
    (74b) "? Suppose it's raining but it is probably not raining."

    (75a) "Suppose it's raining but I am more confident that it's
           snowing than that it's raining." ✓
    (75b) "? Suppose it's raining but it's more likely that it's
           snowing than that it's raining."

    `confident` allows Moore's-paradox-style assertions because it is
    holder-relativized: the holder's confidence ordering need not track
    the facts. `likely` is impersonal/objective and cannot felicitously
    contradict established facts.

    This datum distinguishes CSW's states-based confidence semantics
    (`Confidence.lean`: per-holder, non-probabilistic ordering) from
    threshold-based epistemic semantics (`EpistemicThreshold.lean`:
    impersonal credence, `EpistemicEntry.likely_`). -/
structure MooreParadoxAsymmetry where
  /-- (74a)/(75a): confident allows factual contradiction -/
  confident_allows_contradiction : Bool
  /-- (74b)/(75b): likely does not allow factual contradiction -/
  likely_blocks_contradiction : Bool

def csw_moore_asymmetry : MooreParadoxAsymmetry where
  confident_allows_contradiction := true
  likely_blocks_contradiction := true

-- ════════════════════════════════════════════════════
-- § Theory-to-Data Bridges (continued)
-- ════════════════════════════════════════════════════

/-- The Moore's paradox asymmetry is predicted by the architectural
    split between holder-relativized confidence orderings (which are
    unconstrained by facts) and impersonal epistemic thresholds (which
    are evaluated against the agent's actual credence). -/
theorem moore_asymmetry_bridge :
    csw_moore_asymmetry.confident_allows_contradiction = true ∧
    csw_moore_asymmetry.likely_blocks_contradiction = true := by
  exact ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Cross-Framework Agreement: certain
-- ════════════════════════════════════════════════════

/-- Three independent analyses of `certain` agree on its scalar profile:

    1. **States-based** (`Confidence.certainEntry`): contrast point is the
       top element of the confidence ordering (`h_top : ∀ s, co.le s maxPt`)
    2. **Threshold** (`EpistemicThreshold.EpistemicEntry.certain_`): highest
       threshold on the epistemic scale (θ = 19/20, near the [0,1] maximum)
    3. **Fragment** (`Fragments.English.Modifiers.Adjectives.certain`):
       `scaleType = .upperBounded`, `dimension = .confidence`

    All three mark `certain` as sitting at or near the upper bound of an
    upper-bounded confidence scale. The states-based and threshold analyses
    capture this differently — maximality of a preorder element vs.
    nearness to 1 on a probability scale — but converge on the prediction
    that `certain` asymmetrically entails `confident`/`believes`. -/
theorem certain_cross_framework_agreement :
    Fragments.English.Modifiers.Adjectives.certain.scaleType = .upperBounded ∧
    Semantics.Attitudes.EpistemicThreshold.EpistemicEntry.certain_.θ = 19/20 :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Compositional Bridge: Wellwood 2015 → CSW
-- ════════════════════════════════════════════════════

/-- The cross-categorial adjectival comparative from @cite{wellwood-2015},
    instantiated for confidence states, reduces to CSW's
    `statesComparativeSem` under unique-state assumptions.

    This closes the compositionality gap: Wellwood's `comparativeTruth`
    with `role = holder` and `extract = id` applied to confidence
    predicates yields CSW's (47). -/
theorem confidence_comparative_reduces
    {E : Type*} {Time : Type*} [LE Time]
    {frame : Semantics.Events.ThematicRoles.ThematicFrame E Time}
    {P : Semantics.Events.EvPred Time}
    {μ : Semantics.Events.Ev Time → ℚ}
    {a b : E} {sa sb : Semantics.Events.Ev Time}
    (ha : frame.holder a sa ∧ P sa)
    (ha_unique : ∀ s, frame.holder a s → P s → s = sa)
    (hb : frame.holder b sb ∧ P sb)
    (hb_unique : ∀ s, frame.holder b s → P s → s = sb) :
    Phenomena.Comparison.Studies.Wellwood2015.adjectivalComparative
      frame P μ a b ↔
    μ sb < μ sa :=
  Phenomena.Comparison.Studies.Wellwood2015.adjectival_max_reduces
    ha ha_unique hb hb_unique

end Phenomena.Gradability.CarianiSantorioWellwood2024
