import Linglib.Phenomena.Comparison.Comparative.Data
import Linglib.Theories.Semantics.Degree.Frameworks.Heim
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Heim Framework on Comparative Data
@cite{heim-2001}

Bridge connecting Heim's (2001) sentential operator approach to the
comparative construction data.

## Key Distinctions from Kennedy

Heim's framework makes different predictions about scope:

1. **Wide-scope -er**: "The paper is required to be longer than that"
   can mean "there's a minimum required length" (wide scope -er) —
   predicted by Heim, not by Kennedy.

2. **Clausal vs. phrasal**: Heim's than-clause is always clausal
   (a degree predicate). Phrasal "than Bill" involves degree ellipsis.

-/

namespace Phenomena.Comparison.Comparative.HeimBridge

open Semantics.Degree.Frameworks.Heim

-- ════════════════════════════════════════════════════
-- § 1. Heim = Kennedy Extensionally
-- ════════════════════════════════════════════════════

/-- For simple comparatives, Heim and Kennedy yield the same truth
    conditions. They diverge only on scope predictions. -/
theorem heim_eq_kennedy_simple {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    heimComparativeWithMeasure μ a b ↔
      Semantics.Degree.Comparative.comparativeSem μ a b .positive :=
  Iff.rfl

-- ════════════════════════════════════════════════════
-- § 2. Scope Reading Predictions
-- ════════════════════════════════════════════════════

/-- Heim predicts that clausal comparatives (the ones with explicit
    CP complement of *than*) allow scope ambiguities with other
    operators. The `clausalExamples` from Data.lean are exactly the
    cases where Heim's predictions are most interesting. -/
theorem clausal_admits_scope_readings :
    (clausalExamples.filter (·.acceptable)).length > 0 := by
  simp [clausalExamples]

end Phenomena.Comparison.Comparative.HeimBridge
