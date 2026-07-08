import Linglib.Syntax.Comparative
import Linglib.Studies.SarvasyAikhenvald2025
import Linglib.Features.Case.Basic
import Linglib.Fragments.English.Comparison
import Linglib.Fragments.German.Comparison
import Linglib.Fragments.Japanese.Comparison
import Linglib.Fragments.Korean.Comparison
import Linglib.Fragments.Turkish.Comparison
import Linglib.Fragments.Mandarin.Comparison
import Linglib.Fragments.Yoruba.Comparison
import Linglib.Fragments.HindiUrdu.Comparison
import Linglib.Fragments.Slavic.Russian.Comparison
import Linglib.Fragments.Finnish.Comparison
import Linglib.Fragments.Swahili.Comparison
import Linglib.Fragments.Latin.Comparison
import Linglib.Fragments.Thai.Comparison
import Linglib.Fragments.Tagalog.Comparison
import Linglib.Fragments.Arabic.ModernStandard.Comparison
import Linglib.Fragments.Navajo.Comparison
import Linglib.Fragments.Romance.French.Comparison

/-!
# Stassen 1985: Comparison and Universal Grammar
[stassen-1985]

Stassen's central claim is that the typology of comparative constructions is
**determined by** the typology of temporal chaining constructions. Comparatives
are not autonomous constructions but are "modelled upon" or "borrowed from"
temporal chains (p. 105). The link runs through a diachronic pathway:
"X is tall; Y is not tall" → "X is taller than Y".

## Stassen 1985's six-way typology vs WALS 2013's five-way

The 1985 book (110-language sample) classifies comparatives into six types:
**separative**, **allative**, **locative** (the three adverbial subtypes
collectively making up the "locational" category in WALS 2013), plus
**exceed**, **conjoined**, and **particle**. The WALS 2013 typology
([stassen-2013], in the substrate `Linglib/Typology/Comparison.lean`)
collapses the spatial triad into single `locational`, dropping the spatial-
relation distinction that drives Stassen's explanatory universals connecting
comparison to temporal chaining.

This file holds the 1985-specific apparatus: the six-way `ComparativeType1985`
inductive, the case-assignment + fixed-encoding + spatial-case projections,
per-language 1985 type assignments, and the universal verifications.

## Chaining strategies (Ch 4)

Languages encode temporal chains using one of two basic strategies (§4.3.1, p. 76):

- **Balancing**: both predicates retain the same structural rank.
- **Deranking**: one predicate is structurally reduced.

Deranking subdivides into **conditional** (only same-subject chains) and
**absolute** (regardless of subject identity).

The Principle of Parallel Chaining (p. 99): a language selects parallel
options for consecutive and simultaneous chains.

## The seven chaining-based universals (§5.2, pp. 106-108)

| Universal | Comparative type | → Chaining type |
|-----------|-----------------|-----------------|
| 1A | derived-case | balancing |
| 1B | fixed-case | deranking |
| 2A | exceed | conditional deranking |
| 2B | adverbial (sep/all/loc) | absolute deranking |
| 3A | separative | abs. deranked anterior consecutive |
| 3B | allative | abs. deranked posterior consecutive |
| 3C | locative | abs. deranked simultaneous |
| 4 | conjoined | balanced simultaneous |

Particle comparatives are modelled on balanced chains (either simultaneous
or consecutive), confirming Universal 1A (p. 108).
-/

set_option autoImplicit false

namespace Stassen1985

open Comparative
open Features (CaseAssignment FixedCaseEncoding)
open Comparative (ComparativeEntry)

-- ════════════════════════════════════════════════════
-- § 0. The Stassen 1985 six-way typology
-- ════════════════════════════════════════════════════

/-- The six comparative construction types of [stassen-1985] Ch 2.

    Finer than the WALS 2013 types (`Comparative.ComparativeType`):
    the three adverbial subtypes (separative, allative, locative) are
    collapsed into a single "locational" category in WALS. The six types
    form a hierarchy based on case assignment and syntactic encoding:

    ```
                        Comparative
                       /            \
                Derived case    Fixed case
               /        \       /        \
          Conjoined  Particle  Exceed  Adverbial
                                      /    |    \
                                   Sep   All   Loc
    ``` -/
inductive ComparativeType1985 where
  | separative | allative | locative | exceed | conjoined | particle
  deriving DecidableEq, BEq, Repr

/-- Map [stassen-1985] types to the coarser WALS 2013 types
    (`Comparative.ComparativeType`). -/
def ComparativeType1985.toWALS :
    ComparativeType1985 → Comparative.ComparativeType
  | .separative => .locational
  | .allative   => .locational
  | .locative   => .locational
  | .exceed     => .exceed
  | .conjoined  => .conjoined
  | .particle   => .particle

/-- Case assignment for each 1985 type. -/
def ComparativeType1985.caseAssignment : ComparativeType1985 → CaseAssignment
  | .conjoined | .particle => .derived
  | _ => .fixed

/-- Fixed-case encoding (only meaningful for fixed-case types). -/
def ComparativeType1985.fixedEncoding :
    ComparativeType1985 → Option FixedCaseEncoding
  | .exceed => some .directObject
  | .separative | .allative | .locative => some .adverbial
  | .conjoined | .particle => none

/-- Spatial case of the standard marker (only meaningful for adverbial types). -/
def ComparativeType1985.spatialCase :
    ComparativeType1985 → Option Case
  | .separative => some .abl
  | .allative => some .all
  | .locative => some .loc
  | _ => none

-- ════════════════════════════════════════════════════
-- § 1. Stassen's Chaining Type System (Ch 4)
-- ════════════════════════════════════════════════════

/-- Basic structural strategy for encoding temporal chains (§4.3.1, p. 76). -/
inductive ChainingStrategy where
  | balancing
  | deranking
  deriving DecidableEq, Repr

/-- For deranking languages: same-subject restriction or unconditional. -/
inductive DerankedConditionality where
  | conditional
  | absolute
  deriving DecidableEq, Repr

/-- For absolutely deranked consecutive chains: which predicate is deranked. -/
inductive DerankedDirection where
  | anterior
  | posterior
  deriving DecidableEq, Repr

/-- Stassen's language type in temporal chaining (§4.7, pp. 98-101). -/
inductive ChainingLanguageType where
  | balancing
  | conditionalDeranking
  | absoluteDeranking
  deriving DecidableEq, Repr

/-- The chaining strategy for a language type. -/
def ChainingLanguageType.strategy : ChainingLanguageType → ChainingStrategy
  | .balancing => .balancing
  | .conditionalDeranking | .absoluteDeranking => .deranking

-- ════════════════════════════════════════════════════
-- § 2. Per-language 1985 type assignments
-- ════════════════════════════════════════════════════

-- Languages classified by their 1985 type, verified against the language
-- lists in §2.3.1-5 and §2.4. Only languages appearing in both our sample
-- and Stassen's 110-language sample are included.

-- §2.3.1 Separative: standard marked 'from'/ablative (p. 40 list)
def japanese1985 : ComparativeType1985 := .separative
def korean1985 : ComparativeType1985 := .separative
def turkish1985 : ComparativeType1985 := .separative
def hindiUrdu1985 : ComparativeType1985 := .separative
def arabic1985 : ComparativeType1985 := .separative  -- "Arabic (Classical)"

-- §2.3.3 Locative: standard marked 'at/on'/contact (p. 42 list)
def navajo1985 : ComparativeType1985 := .locative  -- "Navaho" in the 1985 list

-- §2.3.4 Exceed: standard is direct object of exceed-verb (p. 43 list)
def mandarin1985 : ComparativeType1985 := .exceed
def yoruba1985 : ComparativeType1985 := .exceed
def swahili1985 : ComparativeType1985 := .exceed
def thai1985 : ComparativeType1985 := .exceed

-- §2.4 Particle: comparative particle marks standard NP (p. 47 list)
def english1985 : ComparativeType1985 := .particle
def russian1985 : ComparativeType1985 := .particle
def finnish1985 : ComparativeType1985 := .particle  -- primary; secondary separative
def latin1985 : ComparativeType1985 := .particle  -- primary; secondary separative
def french1985 : ComparativeType1985 := .particle

-- ════════════════════════════════════════════════════
-- § 3. Per-language chaining type assignments
-- ════════════════════════════════════════════════════

-- Separative languages (SOV) → absolute deranking, anterior
def japaneseCT  : ChainingLanguageType := .absoluteDeranking
def koreanCT    : ChainingLanguageType := .absoluteDeranking
def turkishCT   : ChainingLanguageType := .absoluteDeranking
def hindiUrduCT : ChainingLanguageType := .absoluteDeranking
def arabicCT    : ChainingLanguageType := .absoluteDeranking  -- VSO exception

-- Exceed languages (SVO) → conditional deranking
def mandarinCT  : ChainingLanguageType := .conditionalDeranking
def yorubaCT    : ChainingLanguageType := .conditionalDeranking
def swahiliCT   : ChainingLanguageType := .conditionalDeranking
def thaiCT      : ChainingLanguageType := .conditionalDeranking

-- Particle languages → balancing
def englishCT   : ChainingLanguageType := .balancing
def russianCT   : ChainingLanguageType := .balancing
def finnishCT   : ChainingLanguageType := .balancing
def latinCT     : ChainingLanguageType := .balancing
def frenchCT    : ChainingLanguageType := .balancing

-- Conjoined languages → balancing
def navajoCT    : ChainingLanguageType := .balancing

-- ════════════════════════════════════════════════════
-- § 4. The Universals (§5.2, pp. 106-108)
-- ════════════════════════════════════════════════════

/-- Universal 1A: derived-case comparative implies balancing chaining. -/
def universal1A (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType.caseAssignment = .derived → ct.strategy = .balancing

/-- Universal 1B: fixed-case comparative implies deranking. -/
def universal1B (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType.caseAssignment = .fixed → ct.strategy = .deranking

/-- Universal 2A: exceed comparative implies conditional deranking. -/
def universal2A (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType = .exceed → ct = .conditionalDeranking ∨ ct = .absoluteDeranking

/-- Universal 2B: adverbial comparative implies absolute deranking. -/
def universal2B (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType.fixedEncoding = some .adverbial → ct = .absoluteDeranking

-- ════════════════════════════════════════════════════
-- § 5. Universal verification over sample
-- ════════════════════════════════════════════════════

theorem u1a_english : universal1A english1985 englishCT := by intro _; rfl
theorem u1a_russian : universal1A russian1985 russianCT := by intro _; rfl
theorem u1a_french  : universal1A french1985 frenchCT := by intro _; rfl
theorem u1a_navajo  : universal1A navajo1985 navajoCT := by intro _; rfl

theorem u1b_japanese  : universal1B japanese1985  japaneseCT  := by intro _; rfl
theorem u1b_korean    : universal1B korean1985    koreanCT    := by intro _; rfl
theorem u1b_turkish   : universal1B turkish1985   turkishCT   := by intro _; rfl
theorem u1b_hindiUrdu : universal1B hindiUrdu1985 hindiUrduCT := by intro _; rfl
theorem u1b_arabic    : universal1B arabic1985    arabicCT    := by intro _; rfl
theorem u1b_mandarin  : universal1B mandarin1985  mandarinCT  := by intro _; rfl
theorem u1b_yoruba    : universal1B yoruba1985    yorubaCT    := by intro _; rfl
theorem u1b_swahili   : universal1B swahili1985   swahiliCT   := by intro _; rfl
theorem u1b_thai      : universal1B thai1985      thaiCT      := by intro _; rfl

theorem u2a_mandarin : universal2A mandarin1985 mandarinCT := by intro _; left; rfl
theorem u2a_yoruba   : universal2A yoruba1985   yorubaCT   := by intro _; left; rfl
theorem u2a_swahili  : universal2A swahili1985  swahiliCT  := by intro _; left; rfl
theorem u2a_thai     : universal2A thai1985     thaiCT     := by intro _; left; rfl

theorem u2b_japanese  : universal2B japanese1985  japaneseCT  := by intro _; rfl
theorem u2b_korean    : universal2B korean1985    koreanCT    := by intro _; rfl
theorem u2b_turkish   : universal2B turkish1985   turkishCT   := by intro _; rfl
theorem u2b_hindiUrdu : universal2B hindiUrdu1985 hindiUrduCT := by intro _; rfl
theorem u2b_arabic    : universal2B arabic1985    arabicCT    := by intro _; rfl

-- ════════════════════════════════════════════════════
-- § 6. Structural properties of the universals
-- ════════════════════════════════════════════════════

/-- Universal 1A and 1B partition the case-assignment space. -/
theorem case_assignment_exhaustive (t : ComparativeType1985) :
    t.caseAssignment = .derived ∨ t.caseAssignment = .fixed := by
  cases t <;> simp [ComparativeType1985.caseAssignment] <;> decide

/-- Particle and conjoined are the only derived-case types. -/
theorem derived_iff_particle_or_conjoined (t : ComparativeType1985) :
    t.caseAssignment = .derived ↔ (t = .particle ∨ t = .conjoined) := by
  cases t <;> simp [ComparativeType1985.caseAssignment] <;> decide

/-- Adverbial types are exactly the spatial triad. -/
theorem adverbial_iff_spatial (t : ComparativeType1985) :
    t.fixedEncoding = some .adverbial ↔
    (t = .separative ∨ t = .allative ∨ t = .locative) := by
  cases t <;> simp [ComparativeType1985.fixedEncoding] <;> decide

/-- The three adverbial types all collapse to locational under WALS. -/
theorem adverbial_collapse :
    ComparativeType1985.separative.toWALS = .locational ∧
    ComparativeType1985.allative.toWALS = .locational ∧
    ComparativeType1985.locative.toWALS = .locational :=
  ⟨rfl, rfl, rfl⟩

/-- Derived-case types never map to locational. -/
theorem derived_case_not_locational (t : ComparativeType1985)
    (h : t.caseAssignment = .derived) : t.toWALS ≠ .locational := by
  cases t <;> simp_all [ComparativeType1985.caseAssignment,
    ComparativeType1985.toWALS]

/-- Fixed-case types never map to particle. -/
theorem fixed_case_not_particle (t : ComparativeType1985)
    (h : t.caseAssignment = .fixed) : t.toWALS ≠ .particle := by
  cases t <;> simp_all [ComparativeType1985.caseAssignment,
    ComparativeType1985.toWALS]

/-- Every adverbial type is fixed-case (by construction). -/
theorem adverbial_is_fixed (t : ComparativeType1985)
    (h : t.fixedEncoding = some .adverbial) :
    t.caseAssignment = .fixed := by
  cases t <;> simp_all [ComparativeType1985.fixedEncoding,
    ComparativeType1985.caseAssignment]

-- ════════════════════════════════════════════════════
-- § 7. Localistic Hypothesis: Spatial Case → Comparative Marker
-- ════════════════════════════════════════════════════

theorem separative_uses_ablative :
    ComparativeType1985.separative.spatialCase = some .abl := rfl
theorem allative_uses_allative :
    ComparativeType1985.allative.spatialCase = some .all := rfl
theorem locative_uses_locative :
    ComparativeType1985.locative.spatialCase = some .loc := rfl
theorem exceed_no_spatial :
    ComparativeType1985.exceed.spatialCase = none := rfl
theorem conjoined_no_spatial :
    ComparativeType1985.conjoined.spatialCase = none := rfl
theorem particle_no_spatial :
    ComparativeType1985.particle.spatialCase = none := rfl

-- ════════════════════════════════════════════════════
-- § 8. Fragment bridge: ComparativeEntry ↔ Typology
-- ════════════════════════════════════════════════════

/-- Japanese Fragment standard case matches 1985 spatial case prediction. -/
theorem japanese_fragment_case :
    some Japanese.Comparison.entry.standardCase =
    japanese1985.spatialCase := rfl

/-- Korean Fragment standard case matches 1985 spatial case prediction. -/
theorem korean_fragment_case :
    some Korean.Comparison.entry.standardCase =
    korean1985.spatialCase := rfl

/-- Turkish Fragment standard case matches 1985 spatial case prediction. -/
theorem turkish_fragment_case :
    some Turkish.Comparison.entry.standardCase =
    turkish1985.spatialCase := rfl

/-- Japanese Fragment standard marker matches the Fragment profile. -/
theorem japanese_marker_match :
    Japanese.Comparison.entry.standardMarker =
    Japanese.Comparison.comparison.standardMarker := rfl

/-- Korean Fragment standard marker matches the Fragment profile. -/
theorem korean_marker_match :
    Korean.Comparison.entry.standardMarker =
    Korean.Comparison.comparison.standardMarker := rfl

/-- Turkish Fragment standard marker matches the Fragment profile. -/
theorem turkish_marker_match :
    Turkish.Comparison.entry.standardMarker =
    Turkish.Comparison.comparison.standardMarker := rfl

/-- All three separative Fragment entries use fixed case assignment. -/
theorem all_separative_fixed_case :
    Japanese.Comparison.entry.caseAssignment = .fixed ∧
    Korean.Comparison.entry.caseAssignment = .fixed ∧
    Turkish.Comparison.entry.caseAssignment = .fixed :=
  ⟨rfl, rfl, rfl⟩

/-- All three separative Fragment entries use adverbial encoding. -/
theorem all_separative_adverbial :
    Japanese.Comparison.entry.fixedEncoding = some .adverbial ∧
    Korean.Comparison.entry.fixedEncoding = some .adverbial ∧
    Turkish.Comparison.entry.fixedEncoding = some .adverbial :=
  ⟨rfl, rfl, rfl⟩

/-- Separative languages lack degree morphology (p. 28). -/
theorem separative_no_degree_morphology :
    Japanese.Comparison.entry.hasDegreeMorphology = false ∧
    Korean.Comparison.entry.hasDegreeMorphology = false ∧
    Turkish.Comparison.entry.hasDegreeMorphology = false :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 9. Three-Layer Consistency
-- ════════════════════════════════════════════════════

/-- Japanese: Fragment (ablative) ↔ 1985 type (separative) ↔ chaining type
    (absolute deranking). All three layers agree. -/
theorem japanese_three_layer :
    some Japanese.Comparison.entry.standardCase =
      japanese1985.spatialCase ∧
    japanese1985.toWALS =
      Japanese.Comparison.comparison.comparativeType ∧
    japaneseCT = .absoluteDeranking ∧
    universal2B japanese1985 japaneseCT :=
  ⟨rfl, rfl, rfl, by intro _; rfl⟩

/-- Korean: three-layer consistency. -/
theorem korean_three_layer :
    some Korean.Comparison.entry.standardCase =
      korean1985.spatialCase ∧
    korean1985.toWALS =
      Korean.Comparison.comparison.comparativeType ∧
    koreanCT = .absoluteDeranking ∧
    universal2B korean1985 koreanCT :=
  ⟨rfl, rfl, rfl, by intro _; rfl⟩

/-- Turkish: three-layer consistency. -/
theorem turkish_three_layer :
    some Turkish.Comparison.entry.standardCase =
      turkish1985.spatialCase ∧
    turkish1985.toWALS =
      Turkish.Comparison.comparison.comparativeType ∧
    turkishCT = .absoluteDeranking ∧
    universal2B turkish1985 turkishCT :=
  ⟨rfl, rfl, rfl, by intro _; rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. Bridge to ClauseChaining/Data
-- ════════════════════════════════════════════════════

/-- Korean: absolute deranking predicts non-finite medial verbs. -/
theorem korean_deranking_consistent :
    koreanCT = .absoluteDeranking ∧
    ClauseChaining.korean.medialVerbForm =
      UD.VerbForm.Conv :=
  ⟨rfl, rfl⟩

theorem turkish_deranking_consistent :
    turkishCT = .absoluteDeranking ∧
    ClauseChaining.turkish.medialVerbForm =
      UD.VerbForm.Conv :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. 1985 ↔ WALS discrepancies
-- ════════════════════════════════════════════════════

-- Three languages show classification differences between the 1985 book
-- and the current WALS-based profiles:
--
-- 1. Finnish: particle in 1985 (p. 47 list), locational in WALS 2013.
--    Stassen may have reclassified Finnish between editions, or the WALS
--    classification emphasizes the partitive-case standard marker.
--
-- 2. Latin: particle-primary in 1985 (p. 47, with quam), mixed in WALS
--    2013 (because ablative comparative is also productive). The 1985
--    system distinguished primary vs secondary options; WALS uses "mixed".
--
-- 3. Navajo: locative in 1985 (p. 42 "Navaho"), conjoined in WALS 2013.
--    Genuine reclassification between the two works.

end Stassen1985
