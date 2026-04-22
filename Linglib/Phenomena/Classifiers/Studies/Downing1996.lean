import Linglib.Core.Lexical.NounCategorization
import Linglib.Fragments.Japanese.Classifier
import Linglib.Fragments.Japanese.Nouns
import Linglib.Phenomena.Classifiers.Typology
import Linglib.Theories.Semantics.Noun.Kind.Chierchia1998

/-!
# @cite{downing-1996} — Numeral Classifier Systems: The Case of Japanese
@cite{downing-1996} @cite{aikhenvald-2000} @cite{chierchia-1998}

Formalizes core contributions from Downing's monograph on Japanese numeral
classifiers (Studies in Discourse and Grammar, vol. 4).

## Two Central Hypotheses

**Hypothesis 1** (Universal semantic trends): Classifier categories encode
culturally significant categories defined by physical, functional, and social
interaction. The choice of which features are exploited is culture-dependent.

**Hypothesis 2** (Semantic supplementation): Classifiers systematically
supplement the information carried by nouns — the classifier system provides
categorization *independent of* and *additional to* the common noun system.

UNVERIFIED: chapter/section/table location references throughout this file
were inherited from earlier formalization work and have not been
cross-checked against the @cite{downing-1996} monograph. Specific cell
counts in the frequency tables below should be treated as illustrative
of the qualitative shape of the data, not as verbatim transcriptions.

## Individuation Function

@cite{downing-1996} treats classifier phrases and plural markers as
individuators. @cite{chierchia-1998}'s later Nominal Mapping Parameter provides
a formal framework for this insight: in [+arg, -pred] languages, bare nouns
denote kinds, and classifiers supply individuation for enumeration. The bridge
to @cite{chierchia-1998} is a linglib contribution, not one Downing herself
makes (Chierchia 1998 postdates this monograph). The strict NMP correlation
has been challenged (e.g., Turkish has bare arguments without classifiers;
Li 2013 argues Chinese nouns are not uniformly mass), but the core insight —
that classifiers relate to individuation — is preserved in current work, with
the mechanism (atomization vs. unitization) still debated.

## Anaphoric Use

Classifier phrases (numeral + classifier without accompanying noun) serve
as anaphoric devices in discourse, occupying a unique niche between zero
anaphora (short range) and full lexical NPs (long range). Qualitative
findings (UNVERIFIED specific percentages): 人 *nin* dominates the
anaphoric distribution; numeral 2 dominates the numeral distribution;
striking distance is intermediate between pronouns and full NPs.

## Shape Dimensionality

Shape-based classifiers decompose along a 1D/2D/3D dimensionality axis
per @cite{allan-1977}, formalized via `Fragments.Japanese.Classifier.shapeDim`.

## Core Inventory

All 27 classifiers from Downing's core inventory (UNVERIFIED: claimed
to be Table 1.1) are represented in the Japanese fragment
(`Fragments.Japanese.Classifier.core`), including the homophonous
軒 `kenBuilding` / 件 `kenIncident` pair, the maritime size split
(隻 seki / 艘 soo), and the two building classifiers (軒 kenBuilding / 棟 mune).

## Frequency Distribution

UNVERIFIED: the n=500 corpus sample and specific cell counts below were
inherited from prior formalization work and have not been verified against
the monograph. The qualitative pattern they encode is well-attested
(extreme Zipfian skew with 人 nin and つ tsu dominating; shape-based
classifiers collectively outweigh function-based ones), but the precise
numbers should be regarded as a placeholder until reconfirmed.

-/

namespace Downing1996

open Fragments.Japanese (Classifier)

-- ============================================================================
-- § 1. Shape Dimensionality (Downing 1996, UNVERIFIED location)
-- ============================================================================

/-- Shape-based classifiers in the Japanese inventory decompose into
    three dimensionality classes (Downing 1996, UNVERIFIED location). -/
def shapeClassifiers : List Classifier :=
  Classifier.all.filter fun c => decide (Classifier.Encodes c .shape)

/-- At least 5 classifiers in the inventory encode shape. -/
theorem shape_classifier_count :
    shapeClassifiers.length ≥ 5 := by decide

/-- All three shape dimensions (1D, 2D, 3D) are attested. -/
theorem all_dimensions_in_inventory :
    shapeClassifiers.any (fun c => c.shapeDim == some .oneD) = true ∧
    shapeClassifiers.any (fun c => c.shapeDim == some .twoD) = true ∧
    shapeClassifiers.any (fun c => c.shapeDim == some .threeD) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 2. Animacy Hierarchy in Classifiers (Downing 1996, UNVERIFIED location)
-- ============================================================================

/-- The animacy hierarchy in Japanese classifiers:
    human (nin/mei) > large animal (tou) > small animal (hiki) > inanimate (tsu).
    Each level is distinguished by a distinct classifier. -/
theorem animacy_hierarchy_witnessed :
    Classifier.Encodes .nin .humanness ∧
    Classifier.Encodes .mei .humanness ∧
    Classifier.Encodes .tou .animacy ∧
    Classifier.Encodes .hiki .animacy ∧
    Classifier.IsDefault .tsu := by decide

/-- The human classifier has a formal register variant (名 mei) marking
    formality/register of the speech act, unlike the neutral 人 nin.
    Note: this indexes register (formal vs casual) rather than
    `socialStatus` (honorific status of the referent — kin, age, social
    rank). -/
theorem human_has_register_variant :
    Classifier.Encodes .nin .humanness ∧
    Classifier.Encodes .mei .humanness ∧
    Classifier.Encodes .mei .register ∧
    ¬ Classifier.Encodes .nin .register := by decide

-- ============================================================================
-- § 3. Anaphoric Use Data (Downing 1996, UNVERIFIED location)
-- ============================================================================

/-- Distribution of classifiers in anaphoric examples
    (Downing 1996, UNVERIFIED location). -/
structure AnaphoricDistribution where
  classifier : Classifier
  count : Nat
  deriving Repr

/-- UNVERIFIED: cell-precise counts (nin=48, tsu=4, hiki=2, wa=1) inherited
    from prior formalization. The qualitative claim — that the anaphoric
    distribution is dominated by `-nin` and skewed against the long tail —
    is well-attested; the precise counts have not been cross-checked. -/
def anaphoricClassifierData : List AnaphoricDistribution :=
  [ { classifier := .nin, count := 48 }
  , { classifier := .tsu, count := 4 }
  , { classifier := .hiki, count := 2 }
  , { classifier := .wa, count := 1 } ]

/-- UNVERIFIED: total anaphoric classifier examples = 55 (sum of cells in
    `anaphoricClassifierData`). -/
theorem anaphoric_total :
    (anaphoricClassifierData.map (·.count)).foldl (· + ·) 0 = 55 := by decide

/-- UNVERIFIED specific count: 人 nin dominates anaphoric classifier use
    at 48/55 ≈ 87%. The dominance claim is qualitatively robust; the
    precise count is unverified. -/
theorem nin_dominates_anaphoric :
    (anaphoricClassifierData.find? (·.classifier == .nin)).map (·.count)
    = some 48 := by decide

/-- Distribution of numerals in anaphoric classifier examples
    (Downing 1996, UNVERIFIED location).
    Numeral 1 is absent — explained by competition with zero anaphora. -/
structure NumeralDistribution where
  numeral : Nat
  count : Nat
  deriving Repr

/-- UNVERIFIED: cell-precise counts (n=2:41, n=3:12, n=4:1, n=5:1)
    inherited from prior formalization. -/
def anaphoricNumeralData : List NumeralDistribution :=
  [ { numeral := 2, count := 41 }
  , { numeral := 3, count := 12 }
  , { numeral := 4, count := 1 }
  , { numeral := 5, count := 1 } ]

/-- UNVERIFIED specific count: numeral 2 dominates anaphoric use at
    41/55 ≈ 75%. -/
theorem two_dominates_anaphoric :
    (anaphoricNumeralData.find? (·.numeral == 2)).map (·.count)
    = some 41 := by decide

/-- Numeral 1 is absent from anaphoric classifier constructions.
    Explanation: 'one' + CL has low contrastive information potential
    and competes with zero anaphora. -/
theorem one_absent_from_anaphoric :
    anaphoricNumeralData.all (·.numeral ≠ 1) = true := by decide

-- ============================================================================
-- § 4. Individuation Bridge (Downing 1996 ↔ Chierchia 1998)
-- ============================================================================

/--  (UNVERIFIED location: Ch. 7) discusses classifier phrases as individuators.
    @cite{chierchia-1998}'s later linking hypothesis formalizes this:
    [+arg, -pred] languages have kind-denoting bare nouns and need classifiers
    for individuation. The strict correlation is contested (see module docstring),
    but the co-occurrence is robustly attested.

    Witnessed by: Japanese is [+arg, -pred] AND has numeral classifiers. -/
theorem argOnly_has_classifiers :
    Fragments.Japanese.Nouns.japaneseMapping = .argOnly ∧
    Phenomena.Classifiers.Typology.japanese.classifierType = .numeralClassifier := by
  exact ⟨rfl, rfl⟩

/-- In @cite{chierchia-1998}'s framework, [+arg, -pred] languages have no
    type-shift blocking (no articles), so bare nouns freely occur as arguments.
    Classifiers rather than articles provide individuation. -/
theorem no_blocking_needs_classifiers :
    Fragments.Japanese.Nouns.japaneseBlocking.iotaBlocked = false ∧
    Fragments.Japanese.Nouns.japaneseBlocking.existsBlocked = false ∧
    Phenomena.Classifiers.Typology.japanese.classifierType = .numeralClassifier := by
  exact ⟨rfl, rfl, rfl⟩

/-- Non-default classifiers encode at least one semantic parameter,
    confirming they carry individuation-relevant information beyond
    mere enumeration. The default classifier つ is the only one
    that enumerates without individuating. Delegates to the structural
    theorem in `Fragments.Japanese.Classifier`. -/
theorem classifiers_carry_individuation_info :
    ∀ c : Classifier, ¬ Classifier.IsDefault c → ¬ Classifier.IsMensural c →
      c.encodes ≠ [] :=
  Classifier.specific_classifiers_have_semantics

-- ============================================================================
-- § 5. Semantic Supplementation (Hypothesis 2)
-- ============================================================================

/-- Seven recurrent semantic relations between the independent sense
    of the classifier morpheme and the classifier category.
    Six are from Downing 1996 (UNVERIFIED location: Ch. 5, Table 5.2); the seventh
    (`sharedQuality`) is attested in non-Japanese languages and noted
    by Downing as recurring cross-linguistically but absent in Japanese. -/
inductive MorphemeCategoryRelation where
  /-- Morpheme denotes a class identical/superordinate to the category.
      e.g., 件 ken 'matter' → classifier for incidents. -/
  | identicalClass
  /-- Morpheme denotes a part possessed by category members.
      e.g., 頭 tou 'head' → classifier for large animals. -/
  | partOfMembers
  /-- Morpheme denotes an action associated with category members.
      e.g., 通 tsuu 'to pass' → classifier for letters/documents. -/
  | associatedAction
  /-- Morpheme denotes an exemplar possessing the defining traits.
      e.g., 筋 suji 'sinew' → classifier for long, slender objects. -/
  | exemplar
  /-- Morpheme denotes the action creating category members.
      e.g., 巻 maki 'to roll up' → classifier for scrolls. -/
  | creationAction
  /-- Morpheme denotes the beneficiary/goal of category activity.
      e.g., 足 soku 'foot' → classifier for pairs of footwear. -/
  | beneficiaryGoal
  /-- Morpheme independently represents a quality shared by members.
      e.g., Indonesian bentuk 'curved' → classifier for rings, wheels. -/
  | sharedQuality
  deriving DecidableEq, Repr

/-- A witness pairing a classifier with its morpheme (UNVERIFIED location: Table 5.2)-category
    relation and the independent meaning of the morpheme. -/
structure MorphemeRelationWitness where
  classifier : Classifier
  relation : MorphemeCategoryRelation
  independentMeaning : String
  deriving Repr

/-- Concrete morpheme (UNVERIFIED location: Table 5.2)-category relation
    assignments for classifiers in our inventory. Each entry records
    the classifier, the relation type, and the independent lexical
    meaning of the morpheme that motivates the relation. -/
def table5_2_witnesses : List MorphemeRelationWitness :=
  [ -- Type 1: morpheme denotes a class identical/superordinate to the category
    { classifier := .kenIncident, relation := .identicalClass
    , independentMeaning := "matter, case" }
  , { classifier := .ki, relation := .identicalClass
    , independentMeaning := "machine" }
    -- Type 2: morpheme denotes a part possessed by category members
  , { classifier := .tou, relation := .partOfMembers
    , independentMeaning := "head" }
  , { classifier := .kyaku, relation := .partOfMembers
    , independentMeaning := "leg" }
    -- Type 3: morpheme denotes an action associated with category members
  , { classifier := .tsuu, relation := .associatedAction
    , independentMeaning := "to pass" }
  , { classifier := .furi, relation := .associatedAction
    , independentMeaning := "to shake" }
    -- Type 6: morpheme denotes the beneficiary/goal of the category activity
  , { classifier := .soku, relation := .beneficiaryGoal
    , independentMeaning := "foot" } ]

/-- At least four of the six Japanese-attested relation types
    are witnessed in the inventory (Types 1, 2, 3, 6). -/
theorem four_relation_types_attested :
    (table5_2_witnesses.map (·.relation)).eraseDups.length ≥ 4 := by decide

/-- All witnesses reference classifiers in our inventory.
    Trivial since `Classifier.mem_all` says every constructor is in `all`. -/
theorem witnesses_in_inventory :
    ∀ w ∈ table5_2_witnesses, w.classifier ∈ Classifier.all :=
  fun w _ => Classifier.mem_all w.classifier

-- ============================================================================
-- § 6. Classifier System Composition
-- ============================================================================

/-- The Japanese classifier inventory includes both sortal and mensural
    classifiers, with sortal classifiers dominating. -/
theorem sortal_dominance :
    (Classifier.all.filter (fun c => ¬ decide (Classifier.IsMensural c))).length >
    (Classifier.all.filter (fun c => decide (Classifier.IsMensural c))).length := by
  decide

/-- Function-based classifiers are the largest semantic group,
    confirming Downing's observation that the system concentrates on
    interactionally significant categories. -/
theorem function_classifiers_numerous :
    (Classifier.all.filter (fun c => decide (Classifier.Encodes c .function))).length ≥ 8 := by
  decide

-- ============================================================================
-- § 7. Core Inventory Completeness (Downing 1996 core inventory)
-- ============================================================================

/-- The core inventory (UNVERIFIED location: Table 1.1) has exactly 27 classifiers. -/
theorem core_inventory_complete : Classifier.core.length = 27 := by decide

/-- Every core classifier is in the full inventory.
    Trivial by construction: `all := core ++ extended ++ sudoAdditions`. -/
theorem full_inventory_includes_core :
    ∀ c ∈ Classifier.core, c ∈ Classifier.all :=
  fun c _ => Classifier.mem_all c

/-- The core inventory distinguishes two homophonous ken classifiers:
    軒 `kenBuilding` and 件 `kenIncident` — different kanji, different
    semantic domains. -/
theorem two_ken_classifiers :
    Classifier.kenBuilding.form = "軒" ∧ Classifier.kenIncident.form = "件" ∧
    Classifier.Encodes .kenBuilding .function ∧
    Classifier.Encodes .kenIncident .function := by decide

/-- Two building classifiers exist: 軒 `kenBuilding` (functional capacity —
    home/shop) and 棟 `mune` (roofed structure). -/
theorem two_building_classifiers :
    Classifier.kenBuilding.gloss = "building" ∧
    Classifier.mune.gloss = "building.roof" :=
  ⟨rfl, rfl⟩

/-- Two maritime classifiers exist: 隻 seki (large boats) and
    艘 soo (small boats), paralleling the animacy size split
    (頭 tou / 匹 hiki). -/
theorem maritime_size_split :
    Classifier.seki.gloss = "large.boat" ∧
    Classifier.soo.gloss = "small.boat" :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 8. Frequency Distribution (Downing 1996, UNVERIFIED location)
-- ============================================================================

/-- Frequency data (UNVERIFIED location: Ch. 3, Table 3.1):
    raw counts of classifiers in a 500-form corpus sample
    (first 50 uses from each of five works of fiction + 250 forms
    from transcribed conversations and oral narrative). -/
structure FrequencyEntry where
  classifier : Classifier
  count : Nat
  deriving Repr

/-- UNVERIFIED: 17-cell frequency distribution claimed to be from
    Downing 1996's n=500 corpus sample. Cells inherited from prior
    formalization and not cross-checked against the monograph; the
    qualitative shape (extreme Zipfian skew, `-nin` and `-tsu`
    dominating, shape-based collectively outweighing function-based)
    is well-attested but the precise counts are placeholders. -/
def frequencyData : List FrequencyEntry :=
  [ { classifier := .nin,  count := 201 }
  , { classifier := .tsu,  count := 115 }
  , { classifier := .hiki, count := 32 }
  , { classifier := .hon, count := 31 }
  , { classifier := .mai,  count := 31 }
  , { classifier := .kenBuilding,  count := 11 }
  , { classifier := .ko,   count := 11 }
  , { classifier := .mei,  count := 6 }
  , { classifier := .teki, count := 6 }
  , { classifier := .tsuu, count := 5 }
  , { classifier := .dai,  count := 4 }
  , { classifier := .satsu, count := 4 }
  , { classifier := .wa,   count := 4 }
  , { classifier := .tsubu, count := 2 }
  , { classifier := .kenIncident, count := 1 }
  , { classifier := .kabu, count := 1 }
  , { classifier := .soku, count := 1 } ]

/-- 人 nin is the single most frequent classifier (qualitatively robust).
    UNVERIFIED specific count: 201/500 ≈ 40%. -/
theorem nin_most_frequent :
    (frequencyData.find? (·.classifier == .nin)).map (·.count) = some 201 := by decide

/-- 人 nin and つ tsu together dominate the distribution (qualitatively
    robust). UNVERIFIED specific arithmetic: 201 + 115 = 316 ≈ 63% of 500. -/
theorem nin_tsu_dominate :
    (201 : Nat) + 115 = 316 ∧ 316 * 100 / 500 = 63 := ⟨rfl, rfl⟩

/-- The top five classifiers (nin, tsu, hiki, hon, mai) account for the
    bulk of the distribution (Zipfian skew, qualitatively robust).
    UNVERIFIED specific arithmetic: top-5 sum = 410 ≈ 82% of 500. -/
theorem top_five_dominate :
    let top5 := [201, 115, 32, 31, 31]
    top5.foldl (· + ·) 0 = 410 ∧ 410 * 100 / 500 = 82 := ⟨rfl, rfl⟩

/-- Quality classifiers (shape-based: hon, mai, ko) are collectively more
    frequent than any individual kind classifier (function-based like ken,
    dai).  observes that "classifiers denoting categories united by
    a common shape ... are used relatively more often than most of the
    'kind-based' classifiers." -/
theorem quality_over_kind_classifiers :
    (31 + 31 + 11 : Nat) > 11 := by omega

end Downing1996
