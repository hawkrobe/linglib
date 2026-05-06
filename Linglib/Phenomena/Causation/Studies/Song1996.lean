import Linglib.Data.WALS.Features.F110A
import Linglib.Data.WALS.Features.F111A
import Linglib.Theories.Semantics.Causation.Morphological

/-!
# Song 1996: Causative Construction Typology
@cite{song-1996}

@cite{song-1996}'s typology of causative constructions, classifying how
causative meaning is **expressed** (morphosyntactic packaging). Three
types: COMPACT (English *kill*, Turkish *-dür*), AND (Vata *le*),
PURP (Korean *-ke ha-*).

This file owns Song's typology + 6 per-language datums + WALS Ch 110A/111A
grounding theorems + the Comrie-Song complexity bridge. The orthogonal
Pylkkänen 2008 Voice-bundling × selection typology lives at
`Phenomena/ArgumentStructure/Studies/Pylkkanen2008.lean` §13 (Pylkkänen's
substrate; not subsumed by Song's). Comrie 1989's compact/morphological/
periphrastic complexity scale lives at
`Theories/Semantics/Causation/Morphological.CausativeComplexity` (the
substrate Song's `toComplexity` projects into).

This file replaces a previous 41-LOC `Studies/Song1996.lean` that was an
editorial-bridge anti-pattern (HahnDegenFutrell ↔ Causation Typology).
The Causation/Typology.lean file (542 LOC) was simultaneously dissolved
and renamed here.

## Cross-paper context (deferred)

Song's COMPACT/AND/PURP three-way is **defensible but coarse**, and
the file-level typology should be read against:

- @cite{dixon-2000-causatives}: nine semantic parameters × three formal types
  (lexical/morphological/periphrastic). Dixon's parameters cut across Song's
  COMPACT (e.g., directness, naturalness, volition) and arguably reduce
  Song's three-way to a special case of his finer parameter space.
- @cite{shibatani-pardeshi-2002}: a **causative continuum** (direct → sociative
  → indirect) where the SOCIATIVE middle category (joint-action causation:
  Japanese *-(s)ase* in its assistive reading; Marathi sociative; dedicated
  Bantu/Korean/Tamil sociative morphology) is missing from Song's tripartite
  partition. Song collapses sociative into PURP or COMPACT depending on
  language, losing a robust typological generalization.
- @cite{wood-marantz-2017}, @cite{cuervo-2014}: generative-side updates of
  Pylkkänen 2008's Voice-bundling × selection typology — see
  `Pylkkanen2008.lean` §13.

The internal `CausativeMorphology` enum (suffix / freeMorpheme / lexical)
within COMPACT is closer to current field consensus than Song's COMPACT/AND/
PURP partition itself — the file documents the typology Song proposed,
not the typology the field has converged on.

## Key Typology (Song §5.1-5.3 — UNVERIFIED location refs)

| Type | Structure | Implicative? | Example |
|------|-----------|-------------|---------|
| COMPACT | Vcause ⊕ Veffect fused | Yes | English *kill*, Turkish *-dür* |
| AND | Two clauses, sequential | Yes | Vata *le* |
| PURP | Two clauses, purposive | No | Korean *-ke ha-* |

The COMPACT type subsumes both lexical causatives (English *kill*) and
morphological causatives (Turkish *-dür*, Japanese *-ase*, French *faire*).
-/

namespace Phenomena.Causation.Studies.Song1996

/-- Morphosyntactic type of causative construction (Song 1996).

    Orthogonal to the force-dynamic builder: a `.make` builder
    can be realized as COMPACT (English *make*), AND, or PURP depending
    on the language.

    - `compact`: Cause and effect fused into a single predicate.
      Includes lexical (*kill*) and morphological (*-dür*, *-ase*).
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
    - A lexical fusion with no separable morpheme (English *kill*)

    Note: `CausativeMorphology.lexical` (no separable morpheme) and
    `Theories/Semantics/Causation/Morphological.CausativeComplexity.lexical`
    (most-compact end of Comrie's complexity scale) share the constructor
    name `lexical` but are NOT semantically equivalent. The first is a
    morpheme-shape claim; the second is a construction-complexity claim.
    English *kill* satisfies both, but the inferential content differs:
    one says "no separable causal morpheme", the other says "construction
    is at the most-compact end of Comrie's continuum". -/
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

/-- French *faire* — COMPACT causative with free morpheme.
    NB: this is the empirically disputed boundary case — Song calls
    French *faire* a free-morpheme COMPACT, while Comrie 1989 / Folli &
    Harley 2005 analyse French *faire-V* as periphrastic (two words,
    analytic). The `toComplexity` bridge below maps it to
    `morphological`, lossily collapsing the disagreement. -/
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

-- ============================================================================
-- WALS Abbreviations
-- ============================================================================

private abbrev ch110 := Data.WALS.F110A.allData
private abbrev ch111 := Data.WALS.F111A.allData

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

/-- Map WALS 110A periphrastic causative type to Song's construction type.

    - `sequentialOnly` → AND (two clauses, sequential, implicative)
    - `purposiveOnly` → PURP (two clauses, purposive, non-implicative)
    - `both` → no single mapping (language has both) -/
private def fromWALS110A : Data.WALS.F110A.PeriphrasticCausativeType →
    Option CausativeConstructionType
  | .sequentialOnly => some .and_
  | .purposiveOnly => some .purp
  | .both => none

/-- Map WALS 111A nonperiphrastic causative type to whether the language
    has COMPACT causatives. -/
private def fromWALS111A_hasCompact : Data.WALS.F111A.NonperiphrCausativeType → Bool
  | .neither => false
  | .morphologicalOnly => true
  | .compoundOnly => true
  | .both => true

/-- Map WALS 111A to a `CausativeMorphology` when a unique mapping exists.

    - `morphologicalOnly` → `.suffix` (bound morpheme)
    - `compoundOnly` → `.freeMorpheme` (compound = free morpheme in tight unit)
    - `both`, `neither` → no unique mapping -/
private def fromWALS111A_morphology :
    Data.WALS.F111A.NonperiphrCausativeType → Option CausativeMorphology
  | .morphologicalOnly => some .suffix
  | .compoundOnly => some .freeMorpheme
  | .neither => none
  | .both => none

-- ============================================================================
-- WALS Grounding: Ch 110A (Periphrastic Causatives)
-- ============================================================================

/-- English periphrastic causatives are sequential (AND-type) per WALS 110A. -/
theorem english_ch110 :
    (Data.WALS.F110A.lookup "eng").map (λ dp => fromWALS110A dp.value) =
      some (some CausativeConstructionType.and_) := by
  native_decide

/-- Turkish periphrastic causatives are purposive (PURP-type) per WALS 110A. -/
theorem turkish_ch110 :
    (Data.WALS.F110A.lookup "tur").map (λ dp => fromWALS110A dp.value) =
      some (some CausativeConstructionType.purp) := by
  native_decide

/-- Korean periphrastic causatives are purposive (PURP-type) per WALS 110A,
    consistent with the `-ke ha-` construction being PURP in Song's typology. -/
theorem korean_ch110 :
    (Data.WALS.F110A.lookup "kor").map (λ dp => fromWALS110A dp.value) =
      some (some CausativeConstructionType.purp) := by
  native_decide

/-- Korean's WALS 110A classification matches our datum's construction type. -/
theorem korean_ch110_matches_datum :
    (Data.WALS.F110A.lookup "kor").map (λ dp => fromWALS110A dp.value) =
      some (some koreanKeHa.constructionType) := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 111A (Nonperiphrastic Causatives)
-- ============================================================================

/-- English has nonperiphrastic (compact) causatives per WALS 111A. -/
theorem english_ch111 :
    (Data.WALS.F111A.lookup "eng").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- English nonperiphrastic causatives are morphological per WALS 111A
    (corresponding to lexical causatives like *kill*). -/
theorem english_ch111_morphology :
    (Data.WALS.F111A.lookup "eng").map (λ dp => fromWALS111A_morphology dp.value) =
      some (some CausativeMorphology.suffix) := by
  native_decide

/-- Turkish has nonperiphrastic (compact) causatives per WALS 111A. -/
theorem turkish_ch111 :
    (Data.WALS.F111A.lookup "tur").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Turkish nonperiphrastic causatives are morphological (suffix `-dür`) per WALS 111A,
    matching our datum. -/
theorem turkish_ch111_morphology :
    (Data.WALS.F111A.lookup "tur").map (λ dp => fromWALS111A_morphology dp.value) =
      some turkishDur.morphology := by
  native_decide

/-- Japanese has nonperiphrastic (compact) causatives per WALS 111A. -/
theorem japanese_ch111 :
    (Data.WALS.F111A.lookup "jpn").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Japanese nonperiphrastic causatives are morphological (suffix `-(s)ase`) per WALS 111A,
    matching our datum. -/
theorem japanese_ch111_morphology :
    (Data.WALS.F111A.lookup "jpn").map (λ dp => fromWALS111A_morphology dp.value) =
      some japaneseAse.morphology := by
  native_decide

/-- French has nonperiphrastic (compact) causatives per WALS 111A.
    WALS classifies French as `both` (morphological and compound). -/
theorem french_ch111 :
    (Data.WALS.F111A.lookup "fre").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Korean has nonperiphrastic (compact) causatives per WALS 111A,
    in addition to the periphrastic `-ke ha-` construction. -/
theorem korean_ch111 :
    (Data.WALS.F111A.lookup "kor").map (λ dp => fromWALS111A_hasCompact dp.value) =
      some true := by
  native_decide

/-- Korean nonperiphrastic causatives are morphological per WALS 111A. -/
theorem korean_ch111_morphology :
    (Data.WALS.F111A.lookup "kor").map (λ dp => fromWALS111A_morphology dp.value) =
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

    The mapping is many-to-one and **lossy** at the COMPACT/freeMorpheme
    boundary: French *faire-V* is `compact + freeMorpheme` in Song's
    typology but `periphrastic` (analytic, two-word) in Comrie's. We
    collapse this disagreement by mapping COMPACT → morphological
    uniformly; the cost is invisibility for the *faire* case.

    See @cite{folli-harley-2005} for the syntactic-structure dispute
    over French *faire-infinitive* vs *faire-par* that this collapse
    obscures. -/
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

/-- Both multi-clause Song types map to Comrie's `periphrastic`.
    Relocated here from `Phenomena/Case/Studies/Comrie1989.lean` per the
    chronology-discipline rule (Comrie 1989 cannot cite Song 1996; the
    cross-paper bridge belongs in the later paper's study file). -/
theorem song_multiclause_both_periphrastic :
    CausativeConstructionType.and_.toComplexity = CausativeComplexity.periphrastic ∧
    CausativeConstructionType.purp.toComplexity = CausativeComplexity.periphrastic :=
  ⟨rfl, rfl⟩

end Phenomena.Causation.Studies.Song1996
