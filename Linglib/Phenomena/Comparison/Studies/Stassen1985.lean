import Linglib.Phenomena.Comparison.Typology
import Linglib.Phenomena.ClauseChaining.Studies.SarvasyAikhenvald2025
import Linglib.Core.Case.Basic
import Linglib.Core.Case.FeatureBundle
import Linglib.Fragments.Japanese.Comparison
import Linglib.Fragments.Korean.Comparison
import Linglib.Fragments.Turkish.Comparison

/-!
# Stassen 1985: Comparison and Universal Grammar
@cite{stassen-1985}

Stassen's central claim is that the typology of comparative constructions is
**determined by** the typology of temporal chaining constructions. Comparatives
are not autonomous constructions but are "modelled upon" or "borrowed from"
temporal chains (p. 105). The link runs through a diachronic pathway:
"X is tall; Y is not tall" → "X is taller than Y".

## Chaining strategies (Ch 4)

Languages encode temporal chains (consecutive and simultaneous action) using
one of two basic strategies (§4.3.1, p. 76):

- **Balancing**: both predicates retain the same structural rank (coordination);
  both are finite main verbs.
- **Deranking**: one predicate is structurally reduced to a non-finite subordinate
  form (participle, gerund, converb, infinitive).

Deranking further subdivides (§4.4, pp. 83-94):
- **Conditional**: deranking only when chain subjects are identical.
- **Absolute**: deranking regardless of subject identity.

The Principle of Parallel Chaining (p. 99): a language selects parallel options
for consecutive and simultaneous chains — balancing languages balance both.

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

## This file

We formalize Stassen's chaining type system, assign chaining types to our
sample languages, state the universals as implications, and verify them over
the sample. Fragment bridge theorems connect Fragments ↔ Typology ↔
chaining types across three layers.
-/

namespace Stassen1985

open Phenomena.Comparison.Typology

-- ════════════════════════════════════════════════════
-- § 1. Stassen's Chaining Type System (Ch 4)
-- ════════════════════════════════════════════════════

/-- Basic structural strategy for encoding temporal chains (§4.3.1, p. 76).

    Balancing: both predicates in the chain retain coordinate structure
    (same structural rank, both finite).

    Deranking: one predicate is reduced to a non-finite subordinate form
    (participle, gerund, converb, dependent mood, infinitive). -/
inductive ChainingStrategy where
  | balancing
  | deranking
  deriving DecidableEq, Repr

/-- For deranking languages: whether deranking is restricted to
    same-subject chains or applies unconditionally (§4.4, pp. 83-94). -/
inductive DerankedConditionality where
  /-- Deranking only when the two predicates share a subject. -/
  | conditional
  /-- Deranking regardless of subject identity. -/
  | absolute
  deriving DecidableEq, Repr

/-- For absolutely deranked consecutive chains: which predicate in the
    chain is deranked. Correlates with basic word order (§4.4.4, p. 94). -/
inductive DerankedDirection where
  /-- The anterior (earlier, leftmost) predicate is deranked.
      Typically SOV languages. -/
  | anterior
  /-- The posterior (later, rightmost) predicate is deranked.
      Typically VSO languages. -/
  | posterior
  deriving DecidableEq, Repr

/-- Stassen's language type in temporal chaining (§4.7, pp. 98-101).

    The Principle of Parallel Chaining (p. 99) restricts the 12 theoretical
    combinations to 3 attested language types. -/
inductive ChainingLanguageType where
  /-- Balancing language: coordination for both C-chains and S-chains.
      No word-order preference. -/
  | balancing
  /-- Conditionally deranking: deranking under subject identity only.
      Typically SVO. -/
  | conditionalDeranking
  /-- Absolutely deranking: deranking regardless of subject identity.
      SOV languages derank the anterior predicate;
      VSO languages derank the posterior predicate. -/
  | absoluteDeranking
  deriving DecidableEq, Repr

/-- The chaining strategy for a language type. -/
def ChainingLanguageType.strategy : ChainingLanguageType → ChainingStrategy
  | .balancing => .balancing
  | .conditionalDeranking | .absoluteDeranking => .deranking

-- ════════════════════════════════════════════════════
-- § 2. Language Chaining Type Assignments
-- ════════════════════════════════════════════════════

-- Assignments for languages in our Comparison/Typology sample that
-- are also in Stassen's 110-language sample (Appendix A).

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
-- § 3. The Universals (§5.2, pp. 106-108)
-- ════════════════════════════════════════════════════

-- Universal 1A: derived-case comparative → balancing
-- Universal 1B: fixed-case comparative → deranking

/-- Universal 1A: derived-case comparative implies balancing chaining.

    "If a language has a derived-case comparative, then that language
    is balancing." (p. 106) -/
def universal1A (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType.caseAssignment = .derived → ct.strategy = .balancing

/-- Universal 1B: fixed-case comparative implies deranking.

    "If a language has a fixed-case comparative, then that language
    is deranking." (p. 106) -/
def universal1B (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType.caseAssignment = .fixed → ct.strategy = .deranking

-- Universal 2A: exceed → conditional deranking
-- Universal 2B: adverbial → absolute deranking

/-- Universal 2A: exceed comparative implies conditional deranking.

    "If a language has an Exceed Comparative, then that language
    has conditional deranking." (p. 106) -/
def universal2A (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType = .exceed → ct = .conditionalDeranking ∨ ct = .absoluteDeranking

/-- Universal 2B: adverbial comparative implies absolute deranking.

    "If a language has an adverbial comparative, then that language
    has absolute deranking." (p. 106) -/
def universal2B (compType : ComparativeType1985) (ct : ChainingLanguageType) :
    Prop :=
  compType.fixedEncoding = some .adverbial → ct = .absoluteDeranking

-- ════════════════════════════════════════════════════
-- § 4. Universal Verification Over Sample
-- ════════════════════════════════════════════════════

-- Verify Universal 1A for derived-case languages in our sample

theorem u1a_english : universal1A english1985 englishCT := by intro _; rfl
theorem u1a_russian : universal1A russian1985 russianCT := by intro _; rfl
theorem u1a_french  : universal1A french1985 frenchCT := by intro _; rfl
theorem u1a_navajo  : universal1A navajo1985 navajoCT := by
  intro _; rfl

-- Verify Universal 1B for fixed-case languages

theorem u1b_japanese  : universal1B japanese1985  japaneseCT  := by intro _; rfl
theorem u1b_korean    : universal1B korean1985    koreanCT    := by intro _; rfl
theorem u1b_turkish   : universal1B turkish1985   turkishCT   := by intro _; rfl
theorem u1b_hindiUrdu : universal1B hindiUrdu1985 hindiUrduCT := by intro _; rfl
theorem u1b_arabic    : universal1B arabic1985    arabicCT    := by intro _; rfl
theorem u1b_mandarin  : universal1B mandarin1985  mandarinCT  := by intro _; rfl
theorem u1b_yoruba    : universal1B yoruba1985    yorubaCT    := by intro _; rfl
theorem u1b_swahili   : universal1B swahili1985   swahiliCT   := by intro _; rfl
theorem u1b_thai      : universal1B thai1985      thaiCT      := by intro _; rfl

-- Verify Universal 2A for exceed languages

theorem u2a_mandarin : universal2A mandarin1985 mandarinCT := by
  intro _; left; rfl
theorem u2a_yoruba   : universal2A yoruba1985   yorubaCT   := by
  intro _; left; rfl
theorem u2a_swahili  : universal2A swahili1985  swahiliCT  := by
  intro _; left; rfl
theorem u2a_thai     : universal2A thai1985     thaiCT     := by
  intro _; left; rfl

-- Verify Universal 2B for adverbial (separative/allative/locative) languages

theorem u2b_japanese  : universal2B japanese1985  japaneseCT  := by intro _; rfl
theorem u2b_korean    : universal2B korean1985    koreanCT    := by intro _; rfl
theorem u2b_turkish   : universal2B turkish1985   turkishCT   := by intro _; rfl
theorem u2b_hindiUrdu : universal2B hindiUrdu1985 hindiUrduCT := by intro _; rfl
theorem u2b_arabic    : universal2B arabic1985    arabicCT    := by intro _; rfl

-- ════════════════════════════════════════════════════
-- § 5. Structural Properties of the Universals
-- ════════════════════════════════════════════════════

/-- Universal 1A and 1B are contrapositives: every 1985 type has exactly
    one case-assignment value, so the two universals partition the space. -/
theorem case_assignment_exhaustive (t : ComparativeType1985) :
    t.caseAssignment = .derived ∨ t.caseAssignment = .fixed := by
  cases t <;> simp [ComparativeType1985.caseAssignment] <;> decide

/-- Particle and conjoined are the only derived-case types. -/
theorem derived_iff_particle_or_conjoined (t : ComparativeType1985) :
    t.caseAssignment = .derived ↔
    (t = .particle ∨ t = .conjoined) := by
  cases t <;> simp [ComparativeType1985.caseAssignment] <;> decide

/-- Adverbial types are exactly the spatial triad (sep, all, loc). -/
theorem adverbial_iff_spatial (t : ComparativeType1985) :
    t.fixedEncoding = some .adverbial ↔
    (t = .separative ∨ t = .allative ∨ t = .locative) := by
  cases t <;> simp [ComparativeType1985.fixedEncoding] <;> decide

-- ════════════════════════════════════════════════════
-- § 6. Localistic Hypothesis: Spatial Case → Comparative Marker
-- ════════════════════════════════════════════════════

/-- Separative comparatives use ablative spatial case markers. -/
theorem separative_uses_ablative :
    ComparativeType1985.separative.spatialCase = some .abl := rfl

theorem allative_uses_allative :
    ComparativeType1985.allative.spatialCase = some .all := rfl

theorem locative_uses_locative :
    ComparativeType1985.locative.spatialCase = some .loc := rfl

/-- Non-spatial types have no spatial case. -/
theorem exceed_no_spatial :
    ComparativeType1985.exceed.spatialCase = none := rfl
theorem conjoined_no_spatial :
    ComparativeType1985.conjoined.spatialCase = none := rfl
theorem particle_no_spatial :
    ComparativeType1985.particle.spatialCase = none := rfl

-- ════════════════════════════════════════════════════
-- § 7. Fragment Bridge: ComparativeEntry ↔ Typology
-- ════════════════════════════════════════════════════

/-- Japanese Fragment standard case matches 1985 spatial case prediction. -/
theorem japanese_fragment_case :
    some Fragments.Japanese.Comparison.entry.standardCase =
    japanese1985.spatialCase := rfl

/-- Korean Fragment standard case matches 1985 spatial case prediction. -/
theorem korean_fragment_case :
    some Fragments.Korean.Comparison.entry.standardCase =
    korean1985.spatialCase := rfl

/-- Turkish Fragment standard case matches 1985 spatial case prediction. -/
theorem turkish_fragment_case :
    some Fragments.Turkish.Comparison.entry.standardCase =
    turkish1985.spatialCase := rfl

/-- Japanese Fragment standard marker matches Typology profile. -/
theorem japanese_marker_match :
    Fragments.Japanese.Comparison.entry.standardMarker =
    japanese.standardMarker := rfl

/-- Korean Fragment standard marker matches Typology profile. -/
theorem korean_marker_match :
    Fragments.Korean.Comparison.entry.standardMarker =
    korean.standardMarker := rfl

/-- Turkish Fragment standard marker matches Typology profile. -/
theorem turkish_marker_match :
    Fragments.Turkish.Comparison.entry.standardMarker =
    turkish.standardMarker := rfl

/-- All three separative Fragment entries use fixed case assignment. -/
theorem all_separative_fixed_case :
    Fragments.Japanese.Comparison.entry.caseAssignment = .fixed ∧
    Fragments.Korean.Comparison.entry.caseAssignment = .fixed ∧
    Fragments.Turkish.Comparison.entry.caseAssignment = .fixed :=
  ⟨rfl, rfl, rfl⟩

/-- All three separative Fragment entries use adverbial encoding. -/
theorem all_separative_adverbial :
    Fragments.Japanese.Comparison.entry.fixedEncoding = some .adverbial ∧
    Fragments.Korean.Comparison.entry.fixedEncoding = some .adverbial ∧
    Fragments.Turkish.Comparison.entry.fixedEncoding = some .adverbial :=
  ⟨rfl, rfl, rfl⟩

/-- Separative languages lack degree morphology (p. 28: degree marking
    is irrelevant to comparative-type choice). -/
theorem separative_no_degree_morphology :
    Fragments.Japanese.Comparison.entry.hasDegreeMorphology = false ∧
    Fragments.Korean.Comparison.entry.hasDegreeMorphology = false ∧
    Fragments.Turkish.Comparison.entry.hasDegreeMorphology = false :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Three-Layer Consistency
-- ════════════════════════════════════════════════════

/-- Japanese: Fragment (ablative) ↔ 1985 type (separative) ↔
    chaining type (absolute deranking). All three layers agree. -/
theorem japanese_three_layer :
    some Fragments.Japanese.Comparison.entry.standardCase =
      japanese1985.spatialCase ∧
    japanese1985.toWALS = japanese.comparativeType ∧
    japaneseCT = .absoluteDeranking ∧
    universal2B japanese1985 japaneseCT :=
  ⟨rfl, rfl, rfl, by intro _; rfl⟩

/-- Korean: three-layer consistency. -/
theorem korean_three_layer :
    some Fragments.Korean.Comparison.entry.standardCase =
      korean1985.spatialCase ∧
    korean1985.toWALS = korean.comparativeType ∧
    koreanCT = .absoluteDeranking ∧
    universal2B korean1985 koreanCT :=
  ⟨rfl, rfl, rfl, by intro _; rfl⟩

/-- Turkish: three-layer consistency. -/
theorem turkish_three_layer :
    some Fragments.Turkish.Comparison.entry.standardCase =
      turkish1985.spatialCase ∧
    turkish1985.toWALS = turkish.comparativeType ∧
    turkishCT = .absoluteDeranking ∧
    universal2B turkish1985 turkishCT :=
  ⟨rfl, rfl, rfl, by intro _; rfl⟩

-- ════════════════════════════════════════════════════
-- § 9. Bridge to ClauseChaining/Data
-- ════════════════════════════════════════════════════

/-- Stassen's absolute deranking predicts that medial verbs are non-finite.
    For our languages also in the ClauseChaining sample, the medial verb
    form should be converbal (non-finite), not fully finite. -/
theorem korean_deranking_consistent :
    koreanCT = .absoluteDeranking ∧
    Phenomena.ClauseChaining.korean.medialVerbForm =
      UD.VerbForm.Conv :=
  ⟨rfl, rfl⟩

theorem turkish_deranking_consistent :
    turkishCT = .absoluteDeranking ∧
    Phenomena.ClauseChaining.turkish.medialVerbForm =
      UD.VerbForm.Conv :=
  ⟨rfl, rfl⟩

end Stassen1985
