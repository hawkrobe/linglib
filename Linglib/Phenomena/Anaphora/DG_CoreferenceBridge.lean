import Linglib.Theories.Syntax.DependencyGrammar.Coreference
import Linglib.Phenomena.Anaphora.Coreference

/-!
# Bridge: Dependency Grammar d-command binding → Coreference Phenomena

Connects the Dependency Grammar coreference analysis (d-command based binding,
from Hudson 1990) to the empirical coreference data in
`Phenomena.Anaphora.Coreference`.

Proves that the DG analysis captures all reflexive coreference patterns,
complementary distribution, and pronominal disjoint reference.
-/

namespace DepGrammar.Coreference.Bridge

open DepGrammar.Coreference
open DepGrammar.Nominal

-- ============================================================================
-- Tests - Matching Phenomena/Anaphora/Coreference data
-- ============================================================================

-- reflexiveCoreferenceData pairs:
-- Pair 1: john sees himself ✓ vs himself sees john ✗
#eval reflexiveLicensedInSentence [john, sees, himself]     -- true ✓
#eval grammaticalForCoreference [himself, sees, john]       -- false ✓

-- Pair 2: mary sees herself ✓ vs herself sees mary ✗
#eval reflexiveLicensedInSentence [mary, sees, herself]     -- true ✓
#eval grammaticalForCoreference [herself, sees, mary]       -- false ✓

-- Pair 3: they see themselves ✓ vs themselves see them ✗
#eval reflexiveLicensedInSentence [they, see, themselves]   -- true ✓
#eval grammaticalForCoreference [themselves, see, them]     -- false ✓

-- Pair 4: john sees himself ✓ vs john sees herself ✗ (gender)
#eval reflexiveLicensedInSentence [john, sees, himself]     -- true ✓
#eval reflexiveLicensedInSentence [john, sees, herself]     -- false ✓

-- Pair 5: they see themselves ✓ vs they see himself ✗ (number)
#eval reflexiveLicensedInSentence [they, see, themselves]   -- true ✓
#eval reflexiveLicensedInSentence [they, see, himself]      -- false ✓

-- pronominalDisjointReferenceData pairs:
-- Pronouns resist local coreference
#eval pronounCoreferenceBlocked [john, sees, him]           -- true ✓
#eval pronounCoreferenceBlocked [mary, sees, her]           -- true ✓

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
  native_decide

/-- Dependency Grammar captures complementaryDistributionData -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  native_decide

/-- Dependency Grammar captures pronominalDisjointReferenceData -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
  native_decide

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
  native_decide

end DepGrammar.Coreference.Bridge
