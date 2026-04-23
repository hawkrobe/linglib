import Linglib.Theories.Syntax.DependencyGrammar.Coreference
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Paradigms.AcceptabilityJudgment

open Paradigms.AcceptabilityJudgment

/-!
# Dependency Grammar d-command binding → Coreference Phenomena

Connects the Dependency Grammar coreference analysis (d-command based binding,
from @cite{hudson-1990}) to the empirical coreference data in
`Phenomena.Anaphora.Coreference`.

Proves that the DG analysis captures all reflexive coreference patterns,
complementary distribution, and pronominal disjoint reference.
-/

namespace Hudson1990

open DepGrammar.Coreference
open DepGrammar.Nominal
open Phenomena.Anaphora.Coreference

-- ============================================================================
-- Capturing the Phenomena Data
-- ============================================================================

/-- Check all pairs in a PhenomenonData -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  capturesPhenomenonData grammaticalForCoreference phenom

-- ============================================================================
-- Theorems - Dependency Grammar Captures Imported Phenomena
-- ============================================================================

/-- Dependency Grammar captures reflexiveCoreferenceData -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData = true := by
  decide

/-- Dependency Grammar captures complementaryDistributionData -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  decide

/-- Dependency Grammar captures pronominalDisjointReferenceData -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
  decide

/-- Check each pair individually for reflexiveCoreferenceData -/
theorem reflexive_pairs_captured :
    -- Pair 1: john sees himself ✓ vs himself sees john ✗
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [himself, sees, john] = false) ∧
    -- Pair 2: mary sees herself ✓ vs herself sees mary ✗
    (grammaticalForCoreference [mary, sees, herself] = true ∧
     grammaticalForCoreference [herself, sees, mary] = false) ∧
    -- Pair 3: they see themselves ✓ vs themselves see them ✗
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [themselves, see, them] = false) ∧
    -- Pair 4: agreement - john sees himself ✓ vs john sees herself ✗
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [john, sees, herself] = false) ∧
    -- Pair 5: agreement - they see themselves ✓ vs they see himself ✗
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [they, see, himself] = false) := by
  decide

/-- DG d-command captures the parseable reciprocal pair: plural antecedent
    required, singular antecedent blocked. -/
theorem reciprocal_plural_antecedent :
    grammaticalForCoreference [they, see, eachOther] = true ∧
    grammaticalForCoreference [john, sees, eachOther] = false := by
  decide

end Hudson1990
