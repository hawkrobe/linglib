/-!
# Comparative Constructions: Empirical Data
@cite{bhatt-takahashi-2011} @cite{bresnan-1973} @cite{kennedy-1999} @cite{lechner-2004}

Basic empirical data on comparative constructions — phrasal vs. clausal
standards, morphological variation, and acceptability patterns.

## Key Empirical Generalizations

1. **Phrasal vs. clausal *than*-clauses** are not freely interchangeable:
   measure phrase differentials require phrasal standards in English.
2. **Synthetic vs. analytic** comparatives distribute by syllable count
   in English but vary cross-linguistically.
3. **Subcomparatives** ("longer than the desk is wide") require clausal
   standards and are restricted in many languages.

-/

namespace Phenomena.Comparison.Comparative

-- ════════════════════════════════════════════════════
-- § 1. Comparative Judgment Data
-- ════════════════════════════════════════════════════

/-- An acceptability judgment for a comparative construction. -/
structure ComparativeJudgment where
  /-- The example sentence -/
  sentence : String
  /-- Whether the sentence is acceptable -/
  acceptable : Bool
  /-- Phrasal or clausal standard? -/
  standardType : String
  /-- Notes on the reading or restriction -/
  note : String := ""
  deriving Repr

/-- Phrasal comparatives — DP complement of *than*. -/
def phrasalExamples : List ComparativeJudgment :=
  [ { sentence := "Kim is taller than Lee"
    , acceptable := true
    , standardType := "phrasal" }
  , { sentence := "Kim bought more books than Lee"
    , acceptable := true
    , standardType := "phrasal"
    , note := "nominal comparative" }
  , { sentence := "Kim ran faster than Lee"
    , acceptable := true
    , standardType := "phrasal"
    , note := "adverbial comparative" }
  ]

/-- Clausal comparatives — CP complement of *than*. -/
def clausalExamples : List ComparativeJudgment :=
  [ { sentence := "Kim is taller than Lee is"
    , acceptable := true
    , standardType := "clausal" }
  , { sentence := "Kim is taller than Lee is wide"
    , acceptable := true
    , standardType := "clausal"
    , note := "subcomparative — different dimension" }
  , { sentence := "Kim bought more books than Lee bought records"
    , acceptable := true
    , standardType := "clausal"
    , note := "nominal subcomparative" }
  ]

-- ════════════════════════════════════════════════════
-- § 2. Morphological Distribution
-- ════════════════════════════════════════════════════

/-- Synthetic vs. analytic comparative distribution in English.
    The generalization: monosyllabic adjectives prefer synthetic (-er),
    polysyllabic prefer analytic (more), disyllabic varies. -/
structure MorphDistributionDatum where
  adjective : String
  syllables : Nat
  syntheticOk : Bool   -- "-er" form acceptable?
  analyticOk : Bool    -- "more" form acceptable?
  deriving Repr

def morphDistribution : List MorphDistributionDatum :=
  [ { adjective := "tall", syllables := 1, syntheticOk := true, analyticOk := false }
  , { adjective := "smart", syllables := 1, syntheticOk := true, analyticOk := false }
  , { adjective := "happy", syllables := 2, syntheticOk := true, analyticOk := true }
  , { adjective := "clever", syllables := 2, syntheticOk := true, analyticOk := true }
  , { adjective := "beautiful", syllables := 3, syntheticOk := false, analyticOk := true }
  , { adjective := "expensive", syllables := 3, syntheticOk := false, analyticOk := true }
  ]

-- ════════════════════════════════════════════════════
-- § 3. Comparative Deletion
-- ════════════════════════════════════════════════════

/-- Comparative deletion data: the standard of comparison may be
    implicitly recovered from context (Kennedy 1999, §2).

    "Kim is taller" — standard = contextually supplied comparison class.
    This connects to the evaluative/positive reading of bare gradable
    adjectives (Gradability/). -/
structure ComparativeDeletionDatum where
  sentence : String
  /-- Is the standard explicitly present? -/
  explicitStandard : Bool
  /-- Available readings -/
  readings : List String
  deriving Repr

def deletionExamples : List ComparativeDeletionDatum :=
  [ { sentence := "Kim is taller"
    , explicitStandard := false
    , readings := ["comparative to contextual standard"] }
  , { sentence := "Kim is taller than Lee"
    , explicitStandard := true
    , readings := ["comparative to Lee"] }
  ]

end Phenomena.Comparison.Comparative
