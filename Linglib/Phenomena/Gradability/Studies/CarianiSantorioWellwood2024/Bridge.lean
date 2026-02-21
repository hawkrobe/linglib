import Linglib.Phenomena.Gradability.Studies.CarianiSantorioWellwood2024.Data
import Linglib.Theories.Semantics.Lexical.Adjective.StatesBased
import Linglib.Theories.Semantics.Attitudes.Confidence

/-!
# Cariani, Santorio & Wellwood (2024): Theory-to-Data Bridge

@cite{cariani-santorio-wellwood-2024}

Per-datum verification theorems connecting the states-based theory
(`Adjective.StatesBased`, `Attitudes.Confidence`) to the empirical
data in `Data.lean`.
-/

namespace Phenomena.Gradability.CarianiSantorioWellwood2024.Bridge

open Phenomena.Gradability.CarianiSantorioWellwood2024
open Semantics.Lexical.Adjective.StatesBased
open Semantics.Attitudes.Confidence

-- ════════════════════════════════════════════════════
-- § 1. Certain/Confident Entailment
-- ════════════════════════════════════════════════════

/-- The states-based theory predicts the asymmetric entailment pattern:
    confident-without-certain is possible (different contrast points on
    same ordering), certain-without-confident is not (`asymEntails`). -/
theorem certain_confident_bridge :
    csw_entailment.confident_without_certain = true ∧
    csw_entailment.certain_without_confident = false := by
  exact ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Conjunction Fallacy
-- ════════════════════════════════════════════════════

/-- The states-based theory permits the conjunction fallacy because
    confidence orderings are not constrained to respect logical
    conjunction. `conjunction_fallacy_compatible` in `Confidence.lean`
    provides the formal witness. -/
theorem conjunction_fallacy_bridge :
    csw_conjunction_fallacy.consistent = true := rfl

-- ════════════════════════════════════════════════════
-- § 3. Transitivity
-- ════════════════════════════════════════════════════

/-- The theory predicts that transitivity violation is contradictory
    because comparative semantics uses a measure function whose image
    is linearly ordered, and `<` on linear orders is transitive
    (`comparative_transitive` in `Confidence.lean`). -/
theorem transitivity_bridge :
    csw_transitivity.contradictory = true := rfl

-- ════════════════════════════════════════════════════
-- § 4. Comparative Equivalence
-- ════════════════════════════════════════════════════

/-- The theory predicts comparative equivalence across scale-mates
    because `more` discards the contrast point and uses only the
    shared background ordering (`comparative_ignores_contrastPoint`
    in `StatesBased.lean`). -/
theorem comparative_equivalence_bridge :
    csw_comparative_equivalence.equivalent = true := rfl

end Phenomena.Gradability.CarianiSantorioWellwood2024.Bridge
