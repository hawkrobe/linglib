import Linglib.Core.WALS.Features.F110A
import Linglib.Core.WALS.Features.F111A
import Linglib.Theories.Semantics.Causation.Morphological

/-!
# Cross-Linguistic Causative Typology
@cite{song-1996}

Song's typology of causative constructions, orthogonal to the
force-dynamic builder classification. This module classifies how
causative meaning is **expressed** (morphosyntactic packaging), while
`Causative` classifies what causative meaning **is** (force-dynamic
mechanism).

## Key Typology (§5.1-5.3)

| Type | Structure | Implicative? | Example |
|------|-----------|-------------|---------|
| COMPACT | Vcause ⊕ Veffect fused | Yes | English *kill*, Turkish *-dür* |
| AND | Two clauses, sequential | Yes | Vata *le* |
| PURP | Two clauses, purposive | No | Korean *-ke ha-* |

The COMPACT type subsumes both lexical causatives (English *kill*) and
morphological causatives (Turkish *-dür*, Japanese *-ase*, French *faire*).

## Cognitive Structure (§5.3)

All causative events involve: GOAL → EVENT → RESULT

- AND type highlights: EVENT + RESULT (factual sequencing)
- PURP type highlights: GOAL + EVENT (purposive, non-implicative)
- COMPACT type: entire sequence collapsed into single predicate

-/

namespace Phenomena.Causation.Typology

/-- Morphosyntactic type of causative construction.

    This is orthogonal to the force-dynamic builder: a `.make` builder
    can be realized as COMPACT (English *make*), AND, or PURP depending
    on the language.

    - `compact`: Cause and effect fused into a single predicate.
      Includes lexical (*kill*) and morphological (*-dür*, *-ase*) causatives.
    - `and_`: Two clauses joined sequentially. Effect clause is factual.
    - `purp`: Two clauses, with purposive semantics. Effect clause is
      non-implicative (not entailed to have occurred). -/
inductive CausativeConstructionType where
  /-- Cause + effect fused (lexical: *kill*; morphological: Turkish *-dür*) -/
  | compact
  /-- Two clauses, sequential (Vata *le*; effect is factual) -/
  | and_
  /-- Two clauses, purposive (Korean *-ke ha-*; effect not entailed) -/
  | purp
  deriving DecidableEq, Repr

/-- Whether a causative construction type is implicative.

    Implicative = the cause clause entails the effect clause.

    - COMPACT: Yes — *kill* entails death occurred
    - AND: Yes — sequential structure implies effect is factual
    - PURP: No — purposive structure leaves effect open -/
def CausativeConstructionType.isImplicative : CausativeConstructionType → Bool
  | .compact => true
  | .and_ => true
  | .purp => false

/-- Morphosyntactic realization of the causative morpheme.

    Within COMPACT causatives, the causal element can be realized as:
    - A bound morpheme (Turkish *-dür*, Japanese *-ase*)
    - A free morpheme forming a tight unit (French *faire*)
    - A lexical fusion with no separable morpheme (English *kill*) -/
inductive CausativeMorphology where
  /-- Bound morpheme (affix): Turkish *-dür*, Japanese *-(s)ase* -/
  | suffix
  /-- Free morpheme forming tight unit: French *faire* -/
  | freeMorpheme
  /-- No separable morpheme: English *kill* (lexical causative) -/
  | lexical
  deriving DecidableEq, Repr

/-- A cross-linguistic causative construction datum. -/
structure CausativeConstructionDatum where
  /-- Language name -/
  language : String
  /-- Surface form or morpheme -/
  form : String
  /-- Construction type in Song's typology -/
  constructionType : CausativeConstructionType
  /-- Morphological realization (for compact types) -/
  morphology : Option CausativeMorphology := none
  /-- Gloss / translation -/
  gloss : String := ""
  deriving Repr, BEq

/-! ## Cross-linguistic data -/

/-- English *kill* — lexical COMPACT causative (kill = cause-to-die) -/
def englishKill : CausativeConstructionDatum :=
  { language := "English"
  , form := "kill"
  , constructionType := .compact
  , morphology := some .lexical
  , gloss := "cause to die (lexical)" }

/-- Turkish *-dür* — morphological COMPACT causative suffix -/
def turkishDur : CausativeConstructionDatum :=
  { language := "Turkish"
  , form := "-dür"
  , constructionType := .compact
  , morphology := some .suffix
  , gloss := "öl-dür 'die-CAUS = kill'" }

/-- Japanese *-(s)ase* — morphological COMPACT causative suffix -/
def japaneseAse : CausativeConstructionDatum :=
  { language := "Japanese"
  , form := "-(s)ase"
  , constructionType := .compact
  , morphology := some .suffix
  , gloss := "ik-ase 'go-CAUS = make go'" }

/-- French *faire* — COMPACT causative with free morpheme -/
def frenchFaire : CausativeConstructionDatum :=
  { language := "French"
  , form := "faire"
  , constructionType := .compact
  , morphology := some .freeMorpheme
  , gloss := "faire lire 'make read'" }

/-- Korean *-ke ha-* — PURP-type causative (non-implicative) -/
def koreanKeHa : CausativeConstructionDatum :=
  { language := "Korean"
  , form := "-ke ha-"
  , constructionType := .purp
  , gloss := "wus-ke ha- 'smile-PURP do = cause to smile'" }

/-- Vata *le* — AND-type causative (sequential, implicative) -/
def vataLe : CausativeConstructionDatum :=
  { language := "Vata"
  , form := "le"
  , constructionType := .and_
  , gloss := "le ... 'and' (overt coordinator)" }

def allData : List CausativeConstructionDatum :=
  [englishKill, turkishDur, japaneseAse, frenchFaire, koreanKeHa, vataLe]

/-! ## Implicativity theorems -/

/-- COMPACT causatives are implicative. -/
theorem compact_is_implicative :
    CausativeConstructionType.compact.isImplicative = true := rfl

/-- AND-type causatives are implicative. -/
theorem and_is_implicative :
    CausativeConstructionType.and_.isImplicative = true := rfl

/-- PURP-type causatives are NOT implicative. -/
theorem purp_not_implicative :
    CausativeConstructionType.purp.isImplicative = false := rfl

/-- Per-datum verification: each datum's implicativity matches its type. -/
theorem englishKill_implicative :
    englishKill.constructionType.isImplicative = true := rfl
theorem turkishDur_implicative :
    turkishDur.constructionType.isImplicative = true := rfl
theorem japaneseAse_implicative :
    japaneseAse.constructionType.isImplicative = true := rfl
theorem frenchFaire_implicative :
    frenchFaire.constructionType.isImplicative = true := rfl
theorem koreanKeHa_not_implicative :
    koreanKeHa.constructionType.isImplicative = false := rfl
theorem vataLe_implicative :
    vataLe.constructionType.isImplicative = true := rfl

-- ============================================================================
-- WALS Abbreviations
-- ============================================================================

private abbrev ch110 := Core.WALS.F110A.allData
private abbrev ch111 := Core.WALS.F111A.allData

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

/-- Map WALS 110A periphrastic causative type to Song's construction type.

    - `sequentialOnly` → AND (two clauses, sequential, implicative)
    - `purposiveOnly` → PURP (two clauses, purposive, non-implicative)
    - `both` → no single mapping (language has both) -/
private def fromWALS110A : Core.WALS.F110A.PeriphrasticCausativeType →
    Option CausativeConstructionType
  | .sequentialOnly => some .and_
  | .purposiveOnly => some .purp
  | .both => none

/-- Map WALS 111A nonperiphrastic causative type to whether the language
    has COMPACT causatives.

    - `morphologicalOnly` → has morphological (suffix) compact causatives
    - `compoundOnly` → has compound compact causatives
    - `both` → has both morphological and compound
    - `neither` → no nonperiphrastic causatives

    Returns `some true` if the language has any nonperiphrastic causatives,
    `some false` if it has neither, and the morphology type when determinable. -/
private def fromWALS111A_hasCompact : Core.WALS.F111A.NonperiphrCausativeType → Bool
  | .neither => false
  | .morphologicalOnly => true
  | .compoundOnly => true
  | .both => true

/-- Map WALS 111A to a `CausativeMorphology` when a unique mapping exists.

    - `morphologicalOnly` → `.suffix` (bound morpheme)
    - `compoundOnly` → `.freeMorpheme` (compound = free morpheme in tight unit)
    - `both`, `neither` → no unique mapping -/
private def fromWALS111A_morphology :
    Core.WALS.F111A.NonperiphrCausativeType → Option CausativeMorphology
  | .morphologicalOnly => some .suffix
  | .compoundOnly => some .freeMorpheme
  | .neither => none
  | .both => none

-- ============================================================================
-- WALS Grounding: Ch 110A (Periphrastic Causatives)
-- Languages in both our data and the F110A sample: English, Turkish, Korean
-- ============================================================================

/-- English periphrastic causatives are sequential (AND-type) per WALS 110A. -/
theorem english_ch110 :
    (Core.WALS.F110A.lookup "eng").map (λ dp => fromWALS110A dp.value) =
      some (some CausativeConstructionType.and_) := by
  native_decide

/-- Turkish periphrastic causatives are purposive (PURP-type) per WALS 110A. -/
theorem turkish_ch110 :
    (Core.WALS.F110A.lookup "tur").map (λ dp => fromWALS110A dp.value) =
      some (some CausativeConstructionType.purp) := by
  native_decide

/-- Korean periphrastic causatives are purposive (PURP-type) per WALS 110A,
    consistent with the `-ke ha-` construction being PURP in Song's typology. -/
theorem korean_ch110 :
    (Core.WALS.F110A.lookup "kor").map (λ dp => fromWALS110A dp.value) =
      some (some CausativeConstructionType.purp) := by
  native_decide

/-- Korean's WALS 110A classification matches our datum's construction type. -/
theorem korean_ch110_matches_datum :
    (Core.WALS.F110A.lookup "kor").map (λ dp => fromWALS110A dp.value) =
      some (some koreanKeHa.constructionType) := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 111A (Nonperiphrastic Causatives)
-- Languages in both our data and the F111A sample:
--   English, Turkish, Japanese, French, Korean
-- ============================================================================

/-- English has nonperiphrastic (compact) causatives per WALS 111A. -/
theorem english_ch111 :
    (Core.WALS.F111A.lookup "eng").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- English nonperiphrastic causatives are morphological per WALS 111A
    (corresponding to lexical causatives like *kill*). -/
theorem english_ch111_morphology :
    (Core.WALS.F111A.lookup "eng").map (λ dp => fromWALS111A_morphology dp.value) =
      some (some CausativeMorphology.suffix) := by
  native_decide

/-- Turkish has nonperiphrastic (compact) causatives per WALS 111A. -/
theorem turkish_ch111 :
    (Core.WALS.F111A.lookup "tur").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Turkish nonperiphrastic causatives are morphological (suffix `-dür`) per WALS 111A,
    matching our datum. -/
theorem turkish_ch111_morphology :
    (Core.WALS.F111A.lookup "tur").map (λ dp => fromWALS111A_morphology dp.value) =
      some turkishDur.morphology := by
  native_decide

/-- Japanese has nonperiphrastic (compact) causatives per WALS 111A. -/
theorem japanese_ch111 :
    (Core.WALS.F111A.lookup "jpn").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Japanese nonperiphrastic causatives are morphological (suffix `-(s)ase`) per WALS 111A,
    matching our datum. -/
theorem japanese_ch111_morphology :
    (Core.WALS.F111A.lookup "jpn").map (λ dp => fromWALS111A_morphology dp.value) =
      some japaneseAse.morphology := by
  native_decide

/-- French has nonperiphrastic (compact) causatives per WALS 111A.
    WALS classifies French as `both` (morphological and compound). -/
theorem french_ch111 :
    (Core.WALS.F111A.lookup "fre").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Korean has nonperiphrastic (compact) causatives per WALS 111A,
    in addition to the periphrastic `-ke ha-` construction. -/
theorem korean_ch111 :
    (Core.WALS.F111A.lookup "kor").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Korean nonperiphrastic causatives are morphological per WALS 111A. -/
theorem korean_ch111_morphology :
    (Core.WALS.F111A.lookup "kor").map (λ dp => fromWALS111A_morphology dp.value) =
      some (some CausativeMorphology.suffix) := by
  native_decide

-- ============================================================================
-- WALS Distribution Theorems
-- ============================================================================

/-- WALS 110A total: 118 languages with periphrastic causative data. -/
theorem ch110_total : ch110.length = 118 := by native_decide

/-- WALS 111A total: 310 languages with nonperiphrastic causative data. -/
theorem ch111_total : ch111.length = 310 := by native_decide

/-- WALS 110A: 35 languages have sequential-only periphrastic causatives. -/
theorem ch110_sequentialOnly :
    (ch110.filter (·.value == .sequentialOnly)).length = 35 := by native_decide

/-- WALS 110A: 68 languages have purposive-only periphrastic causatives. -/
theorem ch110_purposiveOnly :
    (ch110.filter (·.value == .purposiveOnly)).length = 68 := by native_decide

/-- WALS 110A: 15 languages have both sequential and purposive. -/
theorem ch110_both :
    (ch110.filter (·.value == .both)).length = 15 := by native_decide

/-- WALS 111A: 254 languages have morphological-only nonperiphrastic causatives. -/
theorem ch111_morphologicalOnly :
    (ch111.filter (·.value == .morphologicalOnly)).length = 254 := by native_decide

/-- WALS 111A: 9 languages have compound-only nonperiphrastic causatives. -/
theorem ch111_compoundOnly :
    (ch111.filter (·.value == .compoundOnly)).length = 9 := by native_decide

/-- WALS 111A: 24 languages have both morphological and compound. -/
theorem ch111_both :
    (ch111.filter (·.value == .both)).length = 24 := by native_decide

/-- WALS 111A: 23 languages have neither morphological nor compound. -/
theorem ch111_neither :
    (ch111.filter (·.value == .neither)).length = 23 := by native_decide

/-- Purposive periphrastic causatives (PURP-type) are the dominant pattern
    cross-linguistically, outnumbering sequential (AND-type) roughly 2:1. -/
theorem purp_dominates_and :
    (ch110.filter (·.value == .purposiveOnly)).length >
    (ch110.filter (·.value == .sequentialOnly)).length := by native_decide

/-- Morphological causatives overwhelmingly dominate nonperiphrastic strategies:
    254 out of 310 languages (82%) have morphological-only. -/
theorem morphological_dominates :
    (ch111.filter (·.value == .morphologicalOnly)).length * 100 / ch111.length ≥ 81 := by
  native_decide

-- ============================================================================
-- Bridge: Song's Typology ↔ Comrie's Complexity Scale
-- ============================================================================

open Semantics.Causation.Morphological (CausativeComplexity)

/-- Song's construction types map to @cite{comrie-1989}'s complexity scale.

    COMPACT subsumes both lexical and morphological causatives — the
    distinction within compact types is about morphological realization,
    not about the compact-vs-analytic dimension. AND and PURP are both
    multi-clause (periphrastic) in Comrie's sense.

    The mapping is many-to-one: Song's finer-grained typology distinguishes
    AND from PURP by implicativity, while Comrie groups them together as
    "analytic." -/
def CausativeConstructionType.toComplexity :
    CausativeConstructionType → CausativeComplexity
  | .compact => .morphological
  | .and_    => .periphrastic
  | .purp    => .periphrastic

/-- All non-compact (multi-clause) types are periphrastic. -/
theorem multiclause_is_periphrastic (t : CausativeConstructionType) :
    t ≠ .compact → t.toComplexity = CausativeComplexity.periphrastic := by
  cases t <;> simp [CausativeConstructionType.toComplexity]

/-- Compact causatives are at most morphological — never periphrastic. -/
theorem compact_not_periphrastic :
    CausativeConstructionType.compact.toComplexity ≠
      CausativeComplexity.periphrastic := by
  simp [CausativeConstructionType.toComplexity]

end Phenomena.Causation.Typology
