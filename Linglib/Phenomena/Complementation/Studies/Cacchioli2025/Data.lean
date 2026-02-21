import Linglib.Core.Word

/-!
# Cacchioli (2025) — Empirical Data @cite{cacchioli-2025}

Pure empirical data from Cacchioli (2025) "The Syntax of Clausal Prefixes
in Tigrinya." No theory imports — this file contains only observed patterns,
grammaticality judgments, and co-occurrence restrictions.

## Key observations

1. **Four prefixes**: zɨ-, kɨ-, kəmzi-, ʔay-...-n
2. **Complementary distribution**: No two prefixes co-occur
3. **Verb class selection**: The matrix verb determines which prefix appears
4. **Fixed linear order**: Prefix always precedes the verbal complex
5. **Agreement asymmetry**: kɨ- and ʔay-...-n take agreement; zɨ- and kəmzi- don't

## References

- Cacchioli, S. (2025). The Syntax of Clausal Prefixes in Tigrinya.
  PhD dissertation.
-/

namespace Phenomena.Complementation.Cacchioli2025.Data

-- ============================================================================
-- Section A: Prefix inventory
-- ============================================================================

/-- The four clausal prefixes attested in Tigrinya. -/
inductive TigrinyaPrefix where
  | zi      -- zɨ-: relativizer / general subordinator
  | ki      -- kɨ-: subjunctive / irrealis
  | kemzi   -- kəmzi-: factive complementizer
  | ay_n    -- ʔay-...-n: negative circumfix
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Section B: Co-occurrence restrictions
-- ============================================================================

/-- A grammaticality judgment for a prefix combination.
    `true` = grammatical, `false` = ungrammatical. -/
structure CooccurrenceJudgment where
  prefix1 : TigrinyaPrefix
  prefix2 : TigrinyaPrefix
  grammatical : Bool
  example_ : String := ""
  deriving Repr, BEq

/-- No two prefixes can co-occur (complementary distribution). -/
def cooccurrenceData : List CooccurrenceJudgment := [
  ⟨.zi,    .ki,    false, "*zɨ-kɨ-mäs'ə"⟩,
  ⟨.zi,    .kemzi, false, "*zɨ-kəmzi-mäs'ə"⟩,
  ⟨.zi,    .ay_n,  false, "*zɨ-ʔay-mäs'ə-n"⟩,
  ⟨.ki,    .kemzi, false, "*kɨ-kəmzi-mäs'ə"⟩,
  ⟨.ki,    .ay_n,  false, "*kɨ-ʔay-mäs'ə-n"⟩,
  ⟨.kemzi, .ay_n,  false, "*kəmzi-ʔay-mäs'ə-n"⟩
]

/-- All prefix combinations are ungrammatical (complementary distribution). -/
theorem all_cooccurrences_ungrammatical :
    cooccurrenceData.all (·.grammatical == false) = true := by native_decide

-- ============================================================================
-- Section C: Verb class → prefix selection
-- ============================================================================

/-- A selection datum: a matrix verb selects a particular prefix. -/
structure SelectionDatum where
  verb : String
  verbGloss : String
  verbClass : String
  selectedPrefix : TigrinyaPrefix
  example_ : String
  grammatical : Bool := true
  deriving Repr, BEq

/-- Verb class selection data from Cacchioli (2025). -/
def selectionData : List SelectionDatum := [
  -- Knowledge verbs → kəmzi- (factive)
  { verb := "fälätä", verbGloss := "know", verbClass := "knowledge",
    selectedPrefix := .kemzi,
    example_ := "fälätä kəmzi-mäs'ə = knew that (he) came" },
  -- Commentative verbs → kəmzi- (factive)
  { verb := "ħazinä", verbGloss := "be.sad", verbClass := "commentative",
    selectedPrefix := .kemzi,
    example_ := "ħazinä kəmzi-kädä = was.sad that (he) went" },
  -- Desiderative verbs → kɨ- (subjunctive)
  { verb := "dälayä", verbGloss := "want", verbClass := "desiderative",
    selectedPrefix := .ki,
    example_ := "dälayä kɨ-mäs'ə = wanted to come" },
  -- Manipulative verbs → kɨ- (subjunctive)
  { verb := "ʔazazä", verbGloss := "order", verbClass := "manipulative",
    selectedPrefix := .ki,
    example_ := "ʔazazä kɨ-kädä = ordered to go" },
  -- Relative clauses → zɨ- (relativizer)
  { verb := "(head noun)", verbGloss := "REL", verbClass := "relative",
    selectedPrefix := .zi,
    example_ := "sәb'ay zɨ-mäs'ə = person who came" }
]

-- ============================================================================
-- Section D: Agreement asymmetry
-- ============================================================================

/-- Agreement data: which prefixes take agreement suffixes. -/
structure AgreementDatum where
  prefix_ : TigrinyaPrefix
  takesAgreement : Bool
  deriving Repr, BEq

def agreementData : List AgreementDatum := [
  ⟨.zi,    false⟩,  -- zɨ-mäs'ə (no agreement)
  ⟨.ki,    true⟩,   -- kɨ-mäs'ə-*ka* (with 2msg agreement)
  ⟨.kemzi, false⟩,  -- kəmzi-mäs'ə (no agreement)
  ⟨.ay_n,  true⟩    -- ʔay-mäs'ə-*n* (with neg agreement)
]

end Phenomena.Complementation.Cacchioli2025.Data
