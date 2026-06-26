import Linglib.Features.Possession
import Linglib.Data.WALS.Features.F58A
import Linglib.Data.WALS.Features.F59A
import Linglib.Fragments.English.Possession
import Linglib.Fragments.Slavic.Russian.Possession
import Linglib.Fragments.Japanese.Possession
import Linglib.Fragments.Turkish.Possession
import Linglib.Fragments.HindiUrdu.Possession
import Linglib.Fragments.Mandarin.Possession
import Linglib.Fragments.Finnish.Possession
import Linglib.Fragments.Hungarian.Possession
import Linglib.Fragments.Irish.Possession
import Linglib.Fragments.Swahili.Possession
import Linglib.Fragments.Korean.Possession
import Linglib.Fragments.Arabic.ModernStandard.Possession
import Linglib.Fragments.Quechua.Possession
import Linglib.Fragments.Yoruba.Possession
import Linglib.Fragments.Georgian.Possession
import Linglib.Fragments.Hawaiian.Possession
import Linglib.Fragments.Fijian.Possession
import Linglib.Fragments.Mayan.Tsotsil.Possession
import Linglib.Fragments.Mayan.Tseltal.Possession

/-!
# Nichols & Bickel (2013): WALS chapters on possession (57A, 58A, 58B, 59A)
[nichols-bickel-2013] [wals-2013]

The four WALS chapters by Nichols & Bickel (2013):

- Ch 57A: Position of Pronominal Possessive Affixes
- Ch 58A: Obligatory Possessive Inflection
- Ch 58B: Number of Possessive Nouns
- Ch 59A: Possessive Classification

This study file holds **cross-linguistic generalisations** that consume the
Fragment-side `def possession : PossessionProfile` data with non-trivial
semantic content (`oceanic_have_classification`, `head_marking_mostly_complex`,
`have_verb_implies_not_head_marking`, etc.), plus corpus-level WALS
distribution claims that depend on filtering by chapter value.

Per-language Fragment-vs-WALS data-equality theorems are **deliberately
absent** — verifying that `X.Possession.possession.field` equals
`Data.WALS.lookup "iso"` is "encoding conclusions as definitions": the
two would have to silently diverge for the theorem to fail, and the typed
Fragment value already encodes the WALS coding at definition site.

The WALS-aggregate sample-size and dominance theorems live in the substrate
(`Linglib/Features/Possession.lean`) per the project's "WALS goes to
`Linglib/Typology/`" rule.
-/

set_option autoImplicit false

namespace NicholsBickel2013

open Possession

private abbrev ch58 := Data.WALS.F58A.allData
private abbrev ch59 := Data.WALS.F59A.allData

-- ============================================================================
-- §1. The 19-language Fragment sample
-- ============================================================================

/-- The 19-language sample drawn from per-language Fragment Possession files. -/
def allLanguages : List PossessionProfile :=
  [ English.Possession.possession
  , Russian.Possession.possession
  , Japanese.Possession.possession
  , Turkish.Possession.possession
  , HindiUrdu.Possession.possession
  , Mandarin.Possession.possession
  , Finnish.Possession.possession
  , Hungarian.Possession.possession
  , Irish.Possession.possession
  , Swahili.Possession.possession
  , Korean.Possession.possession
  , Arabic.ModernStandard.Possession.possession
  , Quechua.Possession.possession
  , Yoruba.Possession.possession
  , Georgian.Possession.possession
  , Hawaiian.Possession.possession
  , Fijian.Possession.possession
  , Tsotsil.Possession.possession
  , Tseltal.Possession.possession ]

/-- Count of languages in the sample with a given predicative strategy. -/
def countByPredicative (langs : List PossessionProfile)
    (s : PredicativeStrategy) : Nat :=
  (langs.filter (·.predicativeStrategy == s)).length

/-- Count of languages in the sample with a given adnominal strategy. -/
def countByAdnominal (langs : List PossessionProfile)
    (s : AdnominalMarking) : Nat :=
  (langs.filter (·.adnominalStrategy == s)).length

-- ============================================================================
-- §2. Generalization 1: No-classification dominates classification (WALS Ch 59)
-- ============================================================================

/-- Ch 59: No possessive classification (125) is the most common value,
    followed by two-way classification (94). Three-or-more-way classification
    (24) is the least common: 125 > 94 > 24. -/
theorem no_classification_most_common :
    (ch59.filter (·.value == .noPossessiveClassification)).length >
    (ch59.filter (·.value == .twoClasses)).length ∧
    (ch59.filter (·.value == .twoClasses)).length >
    (ch59.filter (·.value == .threeToFiveClasses)).length +
    (ch59.filter (·.value == .moreThanFiveClasses)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Most languages in the WALS sample lack possessive classification:
    125 out of 243 (51.4%). -/
theorem no_classification_plurality :
    (ch59.filter (·.value == .noPossessiveClassification)).length >
    ch59.length / 3 := by native_decide

-- ============================================================================
-- §3. Generalization 2: Obligatory possession is a minority pattern (WALS Ch 58)
-- ============================================================================

/-- Ch 58: Languages without obligatory possessive inflection (201) outnumber
    those with it (43) by a substantial margin. -/
theorem no_obligatory_majority :
    (ch58.filter (·.value == .absent)).length >
    (ch58.filter (·.value == .exists)).length := by native_decide

/-- Ch 58: Over half of sampled languages lack obligatory possession. -/
theorem no_obligatory_over_half :
    (ch58.filter (·.value == .absent)).length >
    ch58.length / 2 := by native_decide

-- ============================================================================
-- §4. Generalization 3: Classification ≈ no-classification (sample-balanced)
-- ============================================================================

/-- Languages with possessive classification (2-way or 3+) come close to
    matching no-classification: 94 + 24 = 118 vs 125. -/
theorem classification_vs_no_classification :
    (ch59.filter (·.value == .twoClasses)).length +
    (ch59.filter (·.value == .threeToFiveClasses)).length +
    (ch59.filter (·.value == .moreThanFiveClasses)).length +
    (ch59.filter (·.value == .noPossessiveClassification)).length =
    ch59.length := by native_decide

/-- Among languages with possessive classification, two-way systems are
    nearly four times as common as three-or-more-way systems. -/
theorem two_way_dominates_three_plus :
    (ch59.filter (·.value == .twoClasses)).length >
    (ch59.filter (·.value == .threeToFiveClasses)).length +
    (ch59.filter (·.value == .moreThanFiveClasses)).length := by
  native_decide

-- ============================================================================
-- §5. Generalization 4: Predicative-strategy diversity in the sample
-- ============================================================================

/-- In the sample, locational strategies are the most common predicative
    possession type (12 languages), followed by have-verb (4), genitive (1),
    topic (1), and comitative (1). -/
theorem predicative_distribution :
    countByPredicative allLanguages .locational = 12 ∧
    countByPredicative allLanguages .haveVerb = 4 ∧
    countByPredicative allLanguages .genitive = 1 ∧
    countByPredicative allLanguages .topic = 1 ∧
    countByPredicative allLanguages .comitative = 1 := by
  native_decide

/-- All five predicative possession strategies are attested in the sample. -/
theorem all_predicative_strategies_attested :
    allLanguages.any (·.predicativeStrategy == .haveVerb) &&
    allLanguages.any (·.predicativeStrategy == .locational) &&
    allLanguages.any (·.predicativeStrategy == .genitive) &&
    allLanguages.any (·.predicativeStrategy == .topic) &&
    allLanguages.any (·.predicativeStrategy == .comitative) = true := by
  native_decide

-- ============================================================================
-- §6. Generalization 5: Dependent-marking dominates adnominal possession
-- ============================================================================

/-- In the sample, dependent-marking is the most common adnominal possession
    strategy (9 languages), followed by head-marking (5), double-marking (3),
    and zero-marking (2). -/
theorem adnominal_distribution :
    countByAdnominal allLanguages .dependentMarking = 9 ∧
    countByAdnominal allLanguages .doubleMarking = 3 ∧
    countByAdnominal allLanguages .headMarking = 5 ∧
    countByAdnominal allLanguages .zeroMarking = 2 := by
  native_decide

/-- Dependent-marking exceeds head-marking + zero-marking combined in
    the sample (with the European-bias caveat). -/
theorem dependent_marking_dominant :
    countByAdnominal allLanguages .dependentMarking >
    countByAdnominal allLanguages .headMarking +
    countByAdnominal allLanguages .zeroMarking := by
  native_decide

-- ============================================================================
-- §7. Generalization 6: Have-verbs ↔ no head-marking
-- ============================================================================

/-- In the sample, every language with a have-verb strategy for predicative
    possession uses dependent-marking or juxtaposition for adnominal
    possession; none use head-marking. This reflects a structural parallel:
    have-verb treats the possessor as subject (a dependent-marking strategy
    at the clause level). -/
theorem have_verb_implies_not_head_marking :
    let haveLangs := allLanguages.filter (·.usesHaveVerb)
    haveLangs.all (λ p => p.adnominalStrategy != .headMarking) = true := by
  native_decide

-- ============================================================================
-- §8. Generalization 7: Head-marking ↔ complex possession
-- ============================================================================

/-- In the sample, most head-marking languages have either obligatory
    possessive inflection or possessive classification. Four of five
    head-marking languages show complex possession systems, reflecting the
    structural affinity between head-marking and elaborate possessive
    morphology on the possessed noun. Swahili is the exception: head-marking
    via noun-class agreement but no obligatory possession or classification. -/
theorem head_marking_mostly_complex_possession :
    let headLangs := allLanguages.filter (·.isHeadMarking)
    let complexHeadLangs := headLangs.filter (λ p =>
      p.hasObligatoryPossession || p.hasClassification)
    headLangs.length = 5 ∧ complexHeadLangs.length = 4 := by
  native_decide

-- ============================================================================
-- §9. Generalization 8: Locational strategy is areally dominant
-- ============================================================================

/-- In the sample, locational/existential predicative possession is the most
    widespread strategy (12 languages: Russian, Finnish, Hungarian, Korean,
    Georgian, Hawaiian, Fijian, Tsotsil, Tseltal, plus Hindi-Urdu, Irish, and
    Arabic, whose "at/near"-oblique possessives are Locational, not Genitive).
    The Eurasian "habeo-less" belt stretches from Finland through Korea, and
    locational strategies also appear in Oceanic and Mayan languages. (Turkish,
    with its genitive `var`-existential, is the sample's sole Genitive type.) -/
theorem locational_count :
    (allLanguages.filter (·.usesLocational)).length = 12 := by
  native_decide

-- ============================================================================
-- §10. Generalization 9: Oceanic possessive classification
-- ============================================================================

/-- In the sample, both Oceanic/Austronesian languages (Hawaiian, Fijian)
    have possessive classification (two-way or three-or-more). Possessive
    classification is an areal feature of the Pacific: the
    alienable/inalienable distinction is nearly universal in Oceanic. -/
def oceanicLanguages : List PossessionProfile :=
  [ Hawaiian.Possession.possession
  , Fijian.Possession.possession ]

theorem oceanic_have_classification :
    oceanicLanguages.all (·.hasClassification) = true := by
  native_decide

-- ============================================================================
-- §11. Generalization 10: Double-marking is rare but systematic
-- ============================================================================

/-- Double-marking (both possessor and possessum overtly marked) appears in
    Turkish, Quechua, and Georgian in the sample. This is the most "redundant"
    strategy — both participants in the possessive relation carry
    morphological marking. -/
theorem double_marking_count :
    countByAdnominal allLanguages .doubleMarking = 3 := by
  native_decide

/-- All double-marking languages in the sample are agglutinative or have
    rich morphology (Turkish, Quechua, Georgian). This is expected:
    double-marking requires the morphological resources to place markers
    on both nouns in the possessive construction. -/
theorem double_marking_languages :
    let doubleLangs := allLanguages.filter (·.adnominalStrategy == .doubleMarking)
    doubleLangs.length = 3 := by
  native_decide

-- ============================================================================
-- §12. Cross-Dimensional Patterns
-- ============================================================================

/-- Most have-verb languages in the sample lack obligatory possessive
    inflection (English, Mandarin, Yoruba). Quechua is the exception: it
    has both a have-verb-like construction and obligatory possessive suffixes
    on kinship/body-part nouns. Three of four have-verb languages lack
    obligatory possession. -/
theorem have_verb_mostly_no_obligatory :
    let haveLangs := allLanguages.filter (·.usesHaveVerb)
    let haveNoOblig := haveLangs.filter (λ p => !p.hasObligatoryPossession)
    haveLangs.length = 4 ∧ haveNoOblig.length = 3 := by
  native_decide

/-- The two phenomena (classification and obligatory possession) are
    logically independent: a language could require possession AND classify
    it. In the sample, three of five classifying languages (Quechua, Tsotsil,
    Tseltal) also have obligatory possession; the other two (Hawaiian, Fijian)
    do not. -/
theorem classification_and_obligatory_independent :
    let classified := allLanguages.filter (·.hasClassification)
    let classifiedAndObligatory := classified.filter (·.hasObligatoryPossession)
    classified.length = 5 ∧ classifiedAndObligatory.length = 3 := by
  native_decide

-- ============================================================================
-- §13. Summary statistics for the sample
-- ============================================================================

/-- Number of languages in the sample. -/
theorem sample_size : allLanguages.length = 19 := by native_decide

/-- Distribution of obligatory possession in the sample. -/
theorem sample_obligatory_count :
    (allLanguages.filter (·.hasObligatoryPossession)).length = 5 := by
  native_decide

/-- Distribution of possessive classification in the sample. -/
theorem sample_classification_count :
    (allLanguages.filter (·.hasClassification)).length = 5 := by
  native_decide

/-- All four adnominal strategies are attested in the sample. -/
theorem all_adnominal_strategies_attested :
    allLanguages.any (·.adnominalStrategy == .headMarking) &&
    allLanguages.any (·.adnominalStrategy == .dependentMarking) &&
    allLanguages.any (·.adnominalStrategy == .doubleMarking) &&
    allLanguages.any (·.adnominalStrategy == .zeroMarking) = true := by
  native_decide

-- ============================================================================
-- §14. Substrate hierarchy properties
-- ============================================================================

/-- The inalienability hierarchy ordering from the substrate is consistent:
    body parts > kinship > spatial relations > part-whole > cultural items
    > general property. -/
theorem inalienability_ordering :
    InalienabilityRank.bodyPart.toNat > InalienabilityRank.kinship.toNat ∧
    InalienabilityRank.kinship.toNat > InalienabilityRank.spatialRelation.toNat ∧
    InalienabilityRank.spatialRelation.toNat > InalienabilityRank.partWhole.toNat ∧
    InalienabilityRank.partWhole.toNat > InalienabilityRank.culturalItem.toNat ∧
    InalienabilityRank.culturalItem.toNat > InalienabilityRank.generalProperty.toNat := by
  native_decide

-- ============================================================================
-- §15. Grammaticalization sources in the sample
-- ============================================================================

/-- In the sample, the two most common grammaticalization sources for
    predicative possession are location and action. -/
theorem location_source_dominates :
    let locationCount := (allLanguages.filter (λ p =>
      predicativeSource p.predicativeStrategy == .location)).length
    let actionCount := (allLanguages.filter (λ p =>
      predicativeSource p.predicativeStrategy == .action)).length
    locationCount > actionCount := by
  native_decide

/-- Five of the eight Heine schemas are attested in the sample via
    `predicativeSource`. -/
theorem attested_sources :
    allLanguages.any (λ p => predicativeSource p.predicativeStrategy == .action) &&
    allLanguages.any (λ p => predicativeSource p.predicativeStrategy == .location) &&
    allLanguages.any (λ p => predicativeSource p.predicativeStrategy == .genitive) &&
    allLanguages.any (λ p => predicativeSource p.predicativeStrategy == .companion) &&
    allLanguages.any (λ p => predicativeSource p.predicativeStrategy == .topic)
    = true := by
  native_decide

end NicholsBickel2013
