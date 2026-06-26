import Linglib.Syntax.Comparative
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
import Linglib.Fragments.French.Comparison

/-!
# Stassen (2013): WALS chapter 121 on comparative constructions
[stassen-2013] [wals-2013] [haspelmath-2001]

WALS Chapter 121 by Leon Stassen covering comparative-construction typology
across 167 languages: the five-way classification
(`locational | exceed | conjoined | particle | mixed`) and its areal
distribution.

This study file holds **cross-linguistic generalisations** that consume the
Fragment-side `def comparison : ComparativeProfile` data with non-trivial
semantic content (`particle_implies_svo_in_sample`,
`conjoined_no_degree_marking`, `morph_comp_implies_morph_super`, etc.).
Per-language Fragment-vs-WALS data-equality theorems are deliberately absent
— see `feedback_no_per_lang_wals_grounding_in_studies` for the rationale.

WALS aggregate distribution theorems live in the substrate
(`Linglib/Typology/Comparison.lean`). Stassen's 1985 fine-grained 6-way
typology and the chaining-based universals live in
`Studies/Stassen1985.lean`.
-/

set_option autoImplicit false

namespace Stassen2013Comparison

open Comparative

-- ============================================================================
-- §1. The 17-language Fragment sample
-- ============================================================================

/-- The 17-language sample drawn from per-language Fragment Comparison files.
    Sample shrunk from the dissolved file's 18 (dropped Martuthunira: no
    `Fragments/Martuthunira/` directory exists). -/
def allLanguages : List ComparativeProfile :=
  [ English.Comparison.comparison
  , German.Comparison.comparison
  , Japanese.Comparison.comparison
  , Mandarin.Comparison.comparison
  , Korean.Comparison.comparison
  , Turkish.Comparison.comparison
  , Yoruba.Comparison.comparison
  , HindiUrdu.Comparison.comparison
  , Russian.Comparison.comparison
  , Finnish.Comparison.comparison
  , Swahili.Comparison.comparison
  , Latin.Comparison.comparison
  , Thai.Comparison.comparison
  , Tagalog.Comparison.comparison
  , Arabic.ModernStandard.Comparison.comparison
  , Navajo.Comparison.comparison
  , French.Comparison.comparison ]

-- ============================================================================
-- §2. Sample-level distributions
-- ============================================================================

/-- Sample size. -/
theorem sample_size : allLanguages.length = 17 := by native_decide

/-- Sample comparative-type distribution. -/
theorem sample_locational_count :
    countByType allLanguages .locational = 6 := by native_decide
theorem sample_exceed_count :
    countByType allLanguages .exceed = 5 := by native_decide
theorem sample_conjoined_count :
    countByType allLanguages .conjoined = 1 := by native_decide
theorem sample_particle_count :
    countByType allLanguages .particle = 4 := by native_decide
theorem sample_mixed_count :
    countByType allLanguages .mixed = 1 := by native_decide

/-- All five comparative types are represented in the sample. -/
theorem all_types_represented :
    countByType allLanguages .locational > 0 ∧
    countByType allLanguages .exceed > 0 ∧
    countByType allLanguages .conjoined > 0 ∧
    countByType allLanguages .particle > 0 ∧
    countByType allLanguages .mixed > 0 := by native_decide

/-- Sample degree-word distribution. -/
theorem sample_degree_word_count :
    countByDegree allLanguages .hasDegreeWord = 5 := by native_decide
theorem sample_morph_count :
    countByDegree allLanguages .morphological = 5 := by native_decide
theorem sample_no_degree_count :
    countByDegree allLanguages .noDegreeMarking = 7 := by native_decide

/-- Degree-word counts sum to sample size. -/
theorem degree_counts_sum :
    countByDegree allLanguages .hasDegreeWord +
    countByDegree allLanguages .morphological +
    countByDegree allLanguages .noDegreeMarking =
    allLanguages.length := by native_decide

/-- Sample superlative-strategy distribution. -/
theorem sample_morph_superlative :
    countBySuperlative allLanguages .morphological = 6 := by native_decide
theorem sample_def_comp_superlative :
    countBySuperlative allLanguages .definiteComparative = 3 := by native_decide
theorem sample_exceed_all_superlative :
    countBySuperlative allLanguages .exceedAll = 3 := by native_decide
theorem sample_comp_univ_superlative :
    countBySuperlative allLanguages .comparativeUniversal = 3 := by native_decide
theorem sample_elative_superlative :
    countBySuperlative allLanguages .elative = 1 := by native_decide
theorem sample_no_superlative :
    countBySuperlative allLanguages .none = 1 := by native_decide

-- ============================================================================
-- §3. Generalisation 1: Particle concentrates in Europe (SAE)
-- ============================================================================

/-- All particle languages in the sample (English, German, Russian, French)
    are SVO (or V2). This reflects [haspelmath-2001]'s identification of
    the comparative particle as a Standard Average European feature. -/
def particleLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .particle)

theorem particle_languages_count :
    particleLanguages.length = 4 := by native_decide

theorem particle_implies_svo_in_sample :
    particleLanguages.all (·.isSVO) = true := by native_decide

-- ============================================================================
-- §4. Generalisation 2: Exceed concentrates in W Africa and SE Asia
-- ============================================================================

/-- Exceed-comparative languages in the sample include Yoruba (W Africa),
    Mandarin (E Asia), Swahili (E Africa), Thai (SE Asia), and Tagalog
    (Austronesian). -/
def exceedLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .exceed)

theorem exceed_languages_count :
    exceedLanguages.length = 5 := by native_decide

-- ============================================================================
-- §5. Generalisation 3: Conjoined comparatives are rarest
-- ============================================================================

def conjoinedLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .conjoined)

theorem conjoined_languages_count :
    conjoinedLanguages.length = 1 := by native_decide

/-- Conjoined-comparative languages universally lack overt degree marking
    in the sample: comparison without any morphological apparatus. -/
theorem conjoined_no_degree_marking :
    conjoinedLanguages.all (·.noDegree) = true := by native_decide

/-- Conjoined-comparative languages also lack dedicated superlative
    strategies — if you can't grammaticalize "more than", you typically
    can't grammaticalize "most" either. -/
theorem conjoined_no_superlative :
    conjoinedLanguages.all (λ p => p.superlative == .none) = true := by
  native_decide

-- ============================================================================
-- §6. Generalisation 4: SOV favors locational
-- ============================================================================

/-- SOV languages in the sample (Japanese, Korean, Turkish, Hindi-Urdu,
    Navajo, Latin) tend toward locational comparatives. -/
def sovLanguages : List ComparativeProfile :=
  allLanguages.filter (·.isSOV)

theorem sov_languages_count :
    sovLanguages.length = 6 := by native_decide

/-- Among SOV languages, locational is the dominant single type. -/
theorem sov_locational_dominant :
    let locCount := countByType sovLanguages .locational
    let excCount := countByType sovLanguages .exceed
    let parCount := countByType sovLanguages .particle
    locCount > excCount ∧ locCount > parCount := by native_decide

-- ============================================================================
-- §7. Generalisation 5: SVO splits between exceed and particle
-- ============================================================================

def svoLanguages : List ComparativeProfile :=
  allLanguages.filter (·.isSVO)

theorem svo_languages_count :
    svoLanguages.length = 9 := by native_decide

/-- Among SVO languages, exceed and particle types are both attested. -/
theorem svo_exceed_particle_split :
    let excCount := countByType svoLanguages .exceed
    let parCount := countByType svoLanguages .particle
    excCount > 0 ∧ parCount > 0 := by native_decide

-- ============================================================================
-- §8. Generalisation 6: Exceed languages mostly lack degree morphology
-- ============================================================================

/-- Exceed-comparative languages in the sample mostly lack bound comparative
    morphology on adjectives. Comparison is expressed via the verb. -/
theorem exceed_mostly_no_morphology :
    let noMorph := exceedLanguages.filter (·.noDegree)
    noMorph.length ≥ 3 := by native_decide

-- ============================================================================
-- §9. Generalisation 7: Morphological comparative ↔ morphological superlative
-- ============================================================================

/-- Languages with morphological comparative degree marking ('-er'/'-ee')
    also have morphological superlatives in the sample. -/
theorem morph_comp_implies_morph_super :
    let morphComp := allLanguages.filter (·.hasMorphComp)
    morphComp.all (·.hasMorphSuperlative) = true := by native_decide

-- ============================================================================
-- §10. Generalisation 8: Locational standard markers are polysemous
-- ============================================================================

/-- Every locational comparative in the sample uses a standard marker that
    also has spatial/ablative meaning ('from', ablative case, partitive case).
    This is definitional but worth verifying: the standard marker is never
    semantically empty. -/
def locationalLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .locational)

theorem locational_languages_count :
    locationalLanguages.length = 6 := by native_decide

theorem locational_has_standard_marker :
    locationalLanguages.all (λ p => p.standardMarker != "") = true := by
  native_decide

-- ============================================================================
-- §11. Cross-chapter: Comparative type vs degree word
-- ============================================================================

/-- Particle comparatives in the sample all have overt degree marking
    (free word or comparative morphology). -/
theorem particle_has_degree :
    particleLanguages.all (λ p =>
      p.hasDegWord || p.hasMorphComp) = true := by native_decide

/-- Exceed comparatives show a split on degree words (Mandarin/Tagalog have
    them, Yoruba/Swahili/Thai do not). -/
theorem exceed_degree_split :
    let withDeg := exceedLanguages.filter (·.hasDegWord)
    let withoutDeg := exceedLanguages.filter (·.noDegree)
    withDeg.length > 0 ∧ withoutDeg.length > 0 := by native_decide

-- ============================================================================
-- §12. Implicational: no superlative without comparative
-- ============================================================================

/-- Conjoined-comparative languages (which lack a dedicated comparative
    construction in Stassen's terms) also lack dedicated superlative
    strategies. Implicational universal: SUPERLATIVE → COMPARATIVE
    (contrapositive). -/
theorem no_comparative_no_superlative :
    let noDedicated := allLanguages.filter (·.hasType .conjoined)
    noDedicated.all (λ p => p.superlative == .none) = true := by native_decide

end Stassen2013Comparison
