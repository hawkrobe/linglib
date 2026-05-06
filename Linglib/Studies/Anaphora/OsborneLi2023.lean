import Linglib.Theories.Syntax.DependencyGrammar.CRDC
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Paradigms.AcceptabilityJudgment

open Paradigms.AcceptabilityJudgment

/-!
# CRDC (Conjunct Referential Dependency Constraint) → Coreference Phenomena

Connects @cite{osborne-li-2023} valency-based binding theory (CRDC) to the
empirical coreference data in `Phenomena.Anaphora.Coreference`.

Proves that the CRDC analysis captures all reflexive coreference patterns,
complementary distribution, and pronominal disjoint reference.
-/

namespace OsborneLi2023

open DepGrammar.CRDC
open DepGrammar.Nominal
open Phenomena.Anaphora.Coreference

-- ============================================================================
-- Capturing Phenomena Data
-- ============================================================================

/-- Check all pairs in a PhenomenonData -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  capturesPhenomenonData grammaticalForCoreference phenom

-- ============================================================================
-- Theorems - CRDC Captures Coreference Phenomena
-- ============================================================================

/-- CRDC captures reflexiveCoreferenceData -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData = true := by
  decide

/-- CRDC captures complementaryDistributionData -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  decide

/-- CRDC captures pronominalDisjointReferenceData -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
  decide

/-- Detailed verification of each reflexive pair -/
theorem reflexive_pairs_captured :
    -- Pair 1: john sees himself vs himself sees john
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [himself, sees, john] = false) ∧
    -- Pair 2: mary sees herself vs herself sees mary
    (grammaticalForCoreference [mary, sees, herself] = true ∧
     grammaticalForCoreference [herself, sees, mary] = false) ∧
    -- Pair 3: they see themselves vs themselves see them
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [themselves, see, them] = false) ∧
    -- Pair 4: agreement - john sees himself vs john sees herself
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [john, sees, herself] = false) ∧
    -- Pair 5: agreement - they see themselves vs they see himself
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [they, see, himself] = false) := by
  decide

/-- CRDC captures the parseable reciprocal pair: plural antecedent
    required, singular antecedent blocked. -/
theorem reciprocal_plural_antecedent :
    grammaticalForCoreference [they, see, eachOther] = true ∧
    grammaticalForCoreference [john, sees, eachOther] = false := by
  decide

end OsborneLi2023
