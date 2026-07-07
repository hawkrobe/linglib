import Linglib.Semantics.Degree.Clausal
import Linglib.Semantics.Degree.Discrete

/-!
# Kennedy 1999: Projecting the Adjective
[kennedy-1999] [bresnan-1973] [bhatt-pancheva-2004] [kennedy-2007] [lechner-2004] [rett-2020] [schwarzschild-2008]

[kennedy-1999] "Projecting the Adjective" (dissertation, UC Santa Cruz;
published 1999, Garland). The foundational argument that gradable adjectives
denote **measure functions** (Entity → Degree), with degree morphemes (-er,
as, -est, too, enough) as functional heads of a DegP projection that bind
the degree argument.

## Core Contributions

1. **Adjectives as measure functions**: ⟦tall⟧ = λx. height(x), not
   λd.λx. height(x) ≥ d. The relational type ⟨d,⟨e,t⟩⟩ is derived by
   combining with degree morphology, not lexical.

2. **Extent functions**: pos-ext and neg-ext partition the scale into degrees
   an entity "has" and "lacks". Negative adjectives access the *negative*
   extent of the same scale as their positive counterpart.

3. **Cross-polar anomaly**: "Kim is as tall as Lee is short" is anomalous
   because the equative tries to compare a positive extent with a negative
   extent — structurally incompatible (proved always-false in
   `crossExtent_always_false`).

4. **Antonymy biconditional**: "BK is longer than The Idiot iff The Idiot is
   shorter than BK" is DERIVED from extent complementarity, not stipulated
   as a lexical property (proved in `Degree.antonymy_biconditional`).

5. **DegP projection**: Degree morphemes head their own syntactic phrase.
   This has been refined by [heim-2001] (sentential operator approach)
   and subsequent work. The core insight — that degree binding is syntactic,
   not lexical — is consensus.

6. **Comparative subdeletion**: "The table is longer than it is wide"
   requires clausal standards and cross-dimensional commensurability.

## What Is Current vs. Historical

The measure function denotation and extent functions (§ 1–4) are current
consensus — they underlie all subsequent degree-semantic work including
[kennedy-2007] and [schwarzschild-2008].

The specific DegP syntax (§ 5) has been refined: [heim-2001]'s
sentential operator approach is now co-standard, and the two make
different scope predictions. This study file records both the data and
the 1999-era analysis.

## Additional Data

This file also collects comparison construction data from
[bresnan-1973] (phrasal/clausal comparatives, morphological
distribution), [bhatt-pancheva-2004] and [lechner-2004]
(subcomparatives), and [kennedy-2007] and [rett-2020]
(equative constructions).

-/

namespace Kennedy1999

open Degree (comparativeSem equativeSem
  comparative_iff_Iic_ssubset comparative_iff_Ioi_ssubset
  equativeSem_iff_Iic_subset)

/-! ### Extents (Ch. 3)

Kennedy's positive/negative extents are `Set.Iic (μ x)` / `Set.Ioi (μ x)`.
Boundary convention: eqs (30)–(31) define POSδ and NEGδ both with `≤`
(a cover; eqs (52)–(53) state their join-complementarity); we use strict
`Ioi` for the negative extent, a strict partition. The antonymy
biconditional (eq (54)) is convention-independent;
`crossExtent_always_false` is convention-specific, and models the
lattice-algebraic shadow of the paper's own *sortal* cross-polar anomaly
argument (§3.1.7), not the sortal analysis itself. -/

/-- Antonymy biconditional (eq (54)): "A is taller than B" iff "B is
    shorter than A", derived from extent algebra. -/
theorem antonymy_biconditional {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    Set.Iic (μ b) ⊂ Set.Iic (μ a) ↔ Set.Ioi (μ a) ⊂ Set.Ioi (μ b) := by
  rw [Set.Iic_ssubset_Iic, Set.Ioi_ssubset_Ioi_iff]

/-- Weak-inclusion antonymy: the Galois-antitone face of eq (54). -/
theorem extent_galois_antitone {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    Set.Iic (μ a) ⊆ Set.Iic (μ b) ↔ Set.Ioi (μ b) ⊆ Set.Ioi (μ a) := by
  rw [Set.Iic_subset_Iic, Set.Ioi_subset_Ioi_iff]

/-- Cross-polar inclusion: one entity's positive extent inside another's
    negative extent — the LF a cross-polar equative would assign. -/
abbrev crossExtentInclusion {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  Set.Iic (μ a) ⊆ Set.Ioi (μ b)

/-- Cross-polar non-inclusion (convention-specific; see the section note). -/
theorem crossExtent_always_false {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) : ¬ crossExtentInclusion μ a b :=
  fun h => absurd (h (min_le_left (μ a) (μ b))) (not_lt.mpr (min_le_right _ _))

/-! ### Cross-Polar Anomaly Data -/

/-- A cross-polar anomaly judgment. -/
structure CrossPolarDatum where
  sentence : String
  acceptable : Bool
  /-- Does this compare same-polarity or cross-polarity extents? -/
  samePolarity : Bool
  /-- Is this an equative ("as...as") or comparative ("-er...than")? -/
  isEquative : Bool
  note : String := ""
  deriving Repr

/-- Cross-polar anomaly data from [kennedy-1999]. -/
def crossPolarData : List CrossPolarDatum :=
  [ { sentence := "Kim is as tall as Lee"
    , acceptable := true, samePolarity := true, isEquative := true
    , note := "same polarity: pos-ext(height, Kim) ⊇ pos-ext(height, Lee)" }
  , { sentence := "Kim is as short as Lee"
    , acceptable := true, samePolarity := true, isEquative := true
    , note := "same polarity: neg-ext(height, Kim) ⊇ neg-ext(height, Lee)" }
  , { sentence := "??Kim is as tall as Lee is short"
    , acceptable := false, samePolarity := false, isEquative := true
    , note := "cross-polar: pos-ext(height, Kim) vs neg-ext(height, Lee)" }
  , { sentence := "??Kim is as short as Lee is tall"
    , acceptable := false, samePolarity := false, isEquative := true
    , note := "cross-polar: neg-ext(height, Kim) vs pos-ext(height, Lee)" }
  , { sentence := "??Kim is taller than Lee is short"
    , acceptable := false, samePolarity := false, isEquative := false
    , note := "cross-polar anomaly: direct antonyms on same dimension ([buring-2007] §1, ex. 1b)" }
  ]

/-- Cross-polar = unacceptable for both equatives and comparatives
    when the adjectives are direct antonyms on the same dimension.
    [buring-2007] shows this holds uniformly (§1, ex. 1). -/
theorem crossPolar_iff_unacceptable :
    ∀ d ∈ crossPolarData,
      (d.acceptable = false ↔ d.samePolarity = false) := by
  intro d hd
  simp [crossPolarData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp_all

-- ════════════════════════════════════════════════════
-- § 2. Cross-Polar Anomaly: Theory Bridge
-- ════════════════════════════════════════════════════

/-- The cross-polar anomaly is predicted by extent function algebra:
    cross-extent inclusion is always false on any linear order.
    This is the formal content behind the unacceptability of
    "Kim is as tall as Lee is short". -/
theorem crossPolar_predicted {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (kim lee : Entity) :
    ¬ crossExtentInclusion μ kim lee :=
  crossExtent_always_false μ kim lee

-- ════════════════════════════════════════════════════
-- § 3. Equative = Extent Inclusion
-- ════════════════════════════════════════════════════

/-- Same-polarity equatives are well-defined: "as tall as" checks
    that the standard's positive extent is included in the subject's.
    This reduces to μ(subject) ≥ μ(standard). -/
theorem samePolar_equative_welldefined {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    equativeSem μ a b .positive ↔ Set.Iic (μ b) ⊆ Set.Iic (μ a) :=
  equativeSem_iff_Iic_subset μ a b

-- ════════════════════════════════════════════════════
-- § 4. Comparative = Strict Extent Inclusion
-- ════════════════════════════════════════════════════

/-- "A is taller than B" iff B's positive extent is strictly contained
    in A's. Bridges the consensus comparative to the algebraic
    `Set.Iic_ssubset_Iic`. -/
theorem comparative_extent_bridge {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ Set.Iic (μ b) ⊂ Set.Iic (μ a) :=
  comparative_iff_Iic_ssubset μ a b

-- ════════════════════════════════════════════════════
-- § 5. Antonymy Biconditional
-- ════════════════════════════════════════════════════

/-- **Central theorem of [kennedy-1999] Ch. 3**: antonymy
    equivalence is DERIVED from the complementarity of positive and
    negative extents, not stipulated as a lexical property.

    "BK is longer than The Idiot" iff "The Idiot is shorter than BK"

    Formally: posExt(b) ⊂ posExt(a) ↔ negExt(a) ⊂ negExt(b).
    The positive comparative and the negative comparative have the
    same truth conditions because positive and negative extents are
    complementary projections of the same scale point. -/
theorem antonymy_derived {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ Set.Ioi (μ a) ⊂ Set.Ioi (μ b) :=
  comparative_iff_Ioi_ssubset μ a b

/-- The antonymy biconditional also holds for equatives:
    "A is as tall as B" iff "B is as short as A" — extent inclusion
    in one polarity implies extent inclusion in the other
    (`extent_galois_antitone`). -/
theorem equative_antonymy_extent {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    equativeSem μ a b .positive ↔ Set.Ioi (μ a) ⊆ Set.Ioi (μ b) := by
  rw [equativeSem_iff_Iic_subset, extent_galois_antitone]

-- ════════════════════════════════════════════════════
-- § 6. Historical: DegP Projection
-- ════════════════════════════════════════════════════

/-- [kennedy-1999]'s DegP projection: degree morphemes are
    functional heads taking AdjP as complement.

    `[DegP [Deg° -er, as, -est, too, enough] [AdjP tall]]`

    This specific syntactic structure was refined by [heim-2001],
    who treats -er as a sentential operator rather than a DegP head.
    Both agree that degree binding is syntactic.

    Note: the degree head inventory matches `Degree.DegPType`
    from `Degree/Defs.lean`, which is the current consensus enumeration.
    This historical structure records Kennedy's specific proposal that
    these heads project a full DegP phrase. -/
structure HistoricalDegP where
  head : Degree.DegPType
  adjective : String
  deriving Repr

/-- Example DegP constructions from [kennedy-1999]. -/
def exampleDegPs : List HistoricalDegP :=
  [ { head := .comparative, adjective := "tall" }   -- "taller"
  , { head := .equative, adjective := "tall" }       -- "as tall"
  , { head := .superlative, adjective := "tall" }    -- "tallest"
  , { head := .excessive, adjective := "expensive" } -- "too expensive"
  , { head := .sufficiency, adjective := "old" }     -- "old enough"
  ]

-- ════════════════════════════════════════════════════
-- § 7. Measure Phrase Distribution
-- ════════════════════════════════════════════════════

/-- [kennedy-1999] §3.1.8 observes that measure phrases are acceptable
    with positive adjectives but not negative ones:

    (69) "My Cadillac is 8 feet long."     ✓
    (70) "#My Fiat is 5 feet short."       ✗

    Kennedy's explanation: measure phrases denote bounded extents. On scales
    with a minimum, positive extents are bounded (anchored at ⊥), but negative
    extents are not (they extend to ∞). So the ordering relation between a
    measure phrase (bounded extent) and a negative extent is undefined. -/
structure MeasurePhraseDatum where
  sentence : String
  acceptable : Bool
  isPositiveAdj : Bool
  deriving Repr

def measurePhraseData : List MeasurePhraseDatum :=
  [ { sentence := "My Cadillac is 8 feet long", acceptable := true, isPositiveAdj := true }
  , { sentence := "#My Fiat is 5 feet short", acceptable := false, isPositiveAdj := false }
  , { sentence := "The kitchen is 50 degrees warmer than the basement"
    , acceptable := true, isPositiveAdj := true }
  , { sentence := "#Mr. Reich is 5 feet short", acceptable := false, isPositiveAdj := false }
  ]

/-- Measure phrases are acceptable with positive adjectives only. -/
theorem measurePhrase_positive_only :
    ∀ d ∈ measurePhraseData, (d.acceptable = true ↔ d.isPositiveAdj = true) := by
  intro d hd
  simp [measurePhraseData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp_all

-- ════════════════════════════════════════════════════
-- § 8. Comparative Construction Data
-- ════════════════════════════════════════════════════

/-- An acceptability judgment for a comparative construction.
    [bresnan-1973] [kennedy-1999] [lechner-2004] -/
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

/-- Bare comparative data: the standard of comparison may be
    implicitly recovered from context.

    "Kim is taller" — standard = contextually supplied comparison class.
    This connects to the evaluative/positive reading of bare gradable
    adjectives (Gradability/).

    Note: "bare comparative" = comparative without an explicit standard.
    This is NOT "comparative deletion" in [bresnan-1973]'s sense
    (= identity-based deletion of a clause constituent from the
    than-clause). -/
structure BareComparativeDatum where
  sentence : String
  /-- Is the standard explicitly present? -/
  explicitStandard : Bool
  /-- Available readings -/
  readings : List String
  deriving Repr

def bareComparativeExamples : List BareComparativeDatum :=
  [ { sentence := "Kim is taller"
    , explicitStandard := false
    , readings := ["comparative to contextual standard"] }
  , { sentence := "Kim is taller than Lee"
    , explicitStandard := true
    , readings := ["comparative to Lee"] }
  ]

-- ════════════════════════════════════════════════════
-- § 9. Subcomparative Data
-- ════════════════════════════════════════════════════

/-- A subcomparative judgment.
    [bhatt-pancheva-2004] [kennedy-1999] [lechner-2004] [schwarzschild-2008] -/
structure SubcomparativeDatum where
  sentence : String
  acceptable : Bool
  /-- The matrix predicate (e.g., "long") -/
  matrixPredicate : String
  /-- The embedded predicate (e.g., "wide") -/
  embeddedPredicate : String
  /-- Are the dimensions commensurable? -/
  commensurable : Bool
  deriving Repr

def subcomparativeExamples : List SubcomparativeDatum :=
  [ { sentence := "The table is longer than the desk is wide"
    , acceptable := true
    , matrixPredicate := "long", embeddedPredicate := "wide"
    , commensurable := true }
  , { sentence := "The building is taller than the field is wide"
    , acceptable := true
    , matrixPredicate := "tall", embeddedPredicate := "wide"
    , commensurable := true }
  , { sentence := "??The soup is hotter than the dress is expensive"
    , acceptable := false
    , matrixPredicate := "hot", embeddedPredicate := "expensive"
    , commensurable := false }
  , { sentence := "More students passed than professors failed"
    , acceptable := true
    , matrixPredicate := "many (students)", embeddedPredicate := "many (professors)"
    , commensurable := true }
  ]

/-- Cross-linguistic variation in subcomparative availability.
    [bhatt-pancheva-2004] -/
structure SubcomparativeTypologyDatum where
  language : String
  available : Bool
  note : String := ""
  deriving Repr

def subcomparativeTypology : List SubcomparativeTypologyDatum :=
  [ { language := "English", available := true }
  , { language := "German", available := true }
  , { language := "French", available := true }
  , { language := "Japanese", available := false
    , note := "No clausal comparatives of this type" }
  , { language := "Mandarin", available := false
    , note := "Exceed-type comparatives don't support subcomparatives" }
  ]

-- ════════════════════════════════════════════════════
-- § 10. Equative Construction Data
-- ════════════════════════════════════════════════════

/-- An equative judgment.
    [kennedy-2007] [rett-2020] -/
structure EquativeJudgment where
  sentence : String
  acceptable : Bool
  /-- "at_least" or "exactly" -/
  availableReadings : List String
  note : String := ""
  deriving Repr

def equativeExamples : List EquativeJudgment :=
  [ { sentence := "Kim is as tall as Lee"
    , acceptable := true
    , availableReadings := ["at_least", "exactly"] }
  , { sentence := "Kim is as tall as Lee, if not taller"
    , acceptable := true
    , availableReadings := ["at_least"]
    , note := "'if not taller' cancels the exactly implicature" }
  , { sentence := "Kim is not as tall as Lee"
    , acceptable := true
    , availableReadings := ["strict_less"]
    , note := "negated equative = strict inequality" }
  , { sentence := "Kim ran as fast as Lee"
    , acceptable := true
    , availableReadings := ["at_least", "exactly"]
    , note := "adverbial equative" }
  ]

/-- Equative encoding strategy. [rett-2020] -/
inductive EquativeStrategy where
  | parameterMarker  -- "as...as" (English, German)
  | reach            -- "tall reaching/to X" (many West African languages)
  | similative       -- "tall like X" (French "aussi...que", many languages)
  | exceed           -- "not exceed X in height" (Mandarin, Japanese)
  deriving DecidableEq, Repr

/-- Cross-linguistic equative strategy datum. -/
structure EquativeTypologyDatum where
  language : String
  strategy : EquativeStrategy
  exampleForm : String
  deriving Repr

def equativeTypology : List EquativeTypologyDatum :=
  [ { language := "English", strategy := .parameterMarker
    , exampleForm := "as tall as" }
  , { language := "German", strategy := .parameterMarker
    , exampleForm := "so groß wie" }
  , { language := "French", strategy := .similative
    , exampleForm := "aussi grand que" }
  , { language := "Mandarin", strategy := .exceed
    , exampleForm := "跟...一样高 (gēn...yíyàng gāo)" }
  , { language := "Japanese", strategy := .exceed
    , exampleForm := "...と同じぐらい高い (...to onaji gurai takai)" }
  ]

end Kennedy1999
