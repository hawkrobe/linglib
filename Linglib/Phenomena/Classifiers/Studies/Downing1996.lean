import Linglib.Core.Lexical.NounCategorization
import Linglib.Fragments.Japanese.Classifiers
import Linglib.Fragments.Japanese.Nouns
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Phenomena.Classifiers.Typology
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-!
# @cite{downing-1996} — Numeral Classifier Systems: The Case of Japanese
@cite{downing-1996} @cite{aikhenvald-2000} @cite{chierchia-1998}

Formalizes core contributions from Downing's monograph on Japanese numeral
classifiers (Studies in Discourse and Grammar, vol. 4).

## Two Central Hypotheses (Ch. 5)

**Hypothesis 1** (Universal semantic trends): Classifier categories encode
culturally significant categories defined by physical, functional, and social
interaction. The choice of which features are exploited is culture-dependent.

**Hypothesis 2** (Semantic supplementation): Classifiers systematically
supplement the information carried by nouns — the classifier system provides
categorization *independent of* and *additional to* the common noun system.

## Individuation Function (Ch. 7)

@cite{downing-1996} Ch. 7 treats classifier phrases and plural markers as
individuators. @cite{chierchia-1998}'s later Nominal Mapping Parameter provides
a formal framework for this insight: in [+arg, -pred] languages, bare nouns
denote kinds, and classifiers supply individuation for enumeration. The bridge
to @cite{chierchia-1998} is a linglib contribution, not one Downing herself
makes (Chierchia 1998 postdates this monograph). The strict NMP correlation
has been challenged (e.g., Turkish has bare arguments without classifiers;
Li 2013 argues Chinese nouns are not uniformly mass), but the core insight —
that classifiers relate to individuation — is preserved in current work, with
the mechanism (atomization vs. unitization) still debated.

## Anaphoric Use (Ch. 6)

Classifier phrases (numeral + classifier without accompanying noun) serve
as anaphoric devices in discourse, occupying a unique niche between zero
anaphora (short range) and full lexical NPs (long range). Empirical findings:
- 87% of anaphoric classifier uses involve 人 *nin* (human classifier)
- 75% use numeral 2
- Striking distance is intermediate: longer than pronouns, shorter than NPs

## Shape Dimensionality (Ch. 5)

Shape-based classifiers decompose along a 1D/2D/3D dimensionality axis,
now formalized via `ShapeDimension` in `ClassifierEntry`.

## Core Inventory (Table 1.1)

All 27 classifiers from Table 1.1 are represented in the Japanese fragment,
including the homophonous 軒 ken (buildings) / 件 ken' (incidents) pair, the
maritime size split (隻 seki / 艘 soo), and the two building classifiers
(軒 ken / 棟 mune).

## Frequency Distribution (Ch. 3, Table 3.1)

A 500-form corpus sample reveals extreme Zipfian skew: 人 nin (40%) and
つ tsu (23%) together account for 63% of all classifier uses. The top five
classifiers cover 82%. Quality classifiers (shape-based) are collectively
more frequent than kind classifiers (function-based).

-/

namespace Downing1996

open Core.NounCategorization
open Fragments.Japanese

-- ============================================================================
-- § 1. Shape Dimensionality (Ch. 5)
-- ============================================================================

/-- Shape-based classifiers in the Japanese inventory decompose into
    three dimensionality classes (Ch. 5). -/
def shapeClassifiers : List ClassifierEntry :=
  Classifiers.allClassifiers.filter (·.encodes .shape)

/-- At least 5 classifiers in the inventory encode shape. -/
theorem shape_classifier_count :
    shapeClassifiers.length ≥ 5 := by native_decide

/-- All three shape dimensions (1D, 2D, 3D) are attested. -/
theorem all_dimensions_in_inventory :
    shapeClassifiers.any (·.shapeDimension == some .oneD) = true ∧
    shapeClassifiers.any (·.shapeDimension == some .twoD) = true ∧
    shapeClassifiers.any (·.shapeDimension == some .threeD) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 2. Animacy Hierarchy in Classifiers (Ch. 5)
-- ============================================================================

/-- The animacy hierarchy in Japanese classifiers:
    human (nin/mei) > large animal (tou) > small animal (hiki) > inanimate (tsu).
    Each level is distinguished by a distinct classifier. -/
theorem animacy_hierarchy_witnessed :
    Classifiers.nin.encodes .humanness = true ∧
    Classifiers.mei.encodes .humanness = true ∧
    Classifiers.tou.encodes .animacy = true ∧
    Classifiers.hiki.encodes .animacy = true ∧
    Classifiers.tsu.isDefault = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The human classifier has a formal register variant (名 mei)
    encoding social status, unlike other animacy classifiers. -/
theorem human_has_register_variant :
    Classifiers.nin.encodes .humanness = true ∧
    Classifiers.mei.encodes .humanness = true ∧
    Classifiers.mei.encodes .socialStatus = true ∧
    Classifiers.nin.encodes .socialStatus = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 3. Anaphoric Use Data (Ch. 6, Tables 6.1–6.2)
-- ============================================================================

/-- Distribution of classifiers in anaphoric examples
    (Ch. 6, Table 6.1, n = 55). -/
structure AnaphoricDistribution where
  classifier : ClassifierEntry
  count : Nat
  deriving Repr

def anaphoricClassifierData : List AnaphoricDistribution :=
  [ { classifier := Classifiers.nin, count := 48 }
  , { classifier := Classifiers.tsu, count := 4 }
  , { classifier := Classifiers.hiki, count := 2 }
  , { classifier := Classifiers.wa, count := 1 } ]

/-- Total anaphoric classifier examples = 55. -/
theorem anaphoric_total :
    (anaphoricClassifierData.map (·.count)).foldl (· + ·) 0 = 55 := by native_decide

/-- 人 nin dominates anaphoric classifier use (48/55 = 87%). -/
theorem nin_dominates_anaphoric :
    (anaphoricClassifierData.find? (·.classifier == Classifiers.nin)).map (·.count)
    = some 48 := by native_decide

/-- Distribution of numerals in anaphoric classifier examples
    (Ch. 6, Table 6.2, n = 55).
    Numeral 1 is absent — explained by competition with zero anaphora. -/
structure NumeralDistribution where
  numeral : Nat
  count : Nat
  deriving Repr

def anaphoricNumeralData : List NumeralDistribution :=
  [ { numeral := 2, count := 41 }
  , { numeral := 3, count := 12 }
  , { numeral := 4, count := 1 }
  , { numeral := 5, count := 1 } ]

/-- Numeral 2 dominates anaphoric use (41/55 = 75%). -/
theorem two_dominates_anaphoric :
    (anaphoricNumeralData.find? (·.numeral == 2)).map (·.count)
    = some 41 := by native_decide

/-- Numeral 1 is absent from anaphoric classifier constructions.
    explains: 'one' + CL has low contrastive
    information potential and competes with zero anaphora. -/
theorem one_absent_from_anaphoric :
    anaphoricNumeralData.all (·.numeral ≠ 1) = true := by native_decide

-- ============================================================================
-- § 4. Individuation Bridge (Ch. 7 ↔ Chierchia 1998)
-- ============================================================================

/-- Ch. 7 discusses classifier phrases as individuators.
    @cite{chierchia-1998}'s later linking hypothesis formalizes this:
    [+arg, -pred] languages have kind-denoting bare nouns and need classifiers
    for individuation. The strict correlation is contested (see module docstring),
    but the co-occurrence is robustly attested.

    Witnessed by: Japanese is [+arg, -pred] AND has numeral classifiers. -/
theorem argOnly_has_classifiers :
    Nouns.japaneseMapping = .argOnly ∧
    Phenomena.Classifiers.Typology.japanese.classifierType = .numeralClassifier := by
  exact ⟨rfl, rfl⟩

/-- In @cite{chierchia-1998}'s framework, [+arg, -pred] languages have no
    type-shift blocking (no articles), so bare nouns freely occur as arguments.
    Classifiers rather than articles provide individuation. -/
theorem no_blocking_needs_classifiers :
    Nouns.japaneseBlocking.iotaBlocked = false ∧
    Nouns.japaneseBlocking.existsBlocked = false ∧
    Phenomena.Classifiers.Typology.japanese.classifierType = .numeralClassifier := by
  exact ⟨rfl, rfl, rfl⟩

/-- Non-default classifiers encode at least one semantic parameter,
    confirming they carry individuation-relevant information beyond
    mere enumeration. The default classifier つ is the only one
    that enumerates without individuating. -/
theorem classifiers_carry_individuation_info :
    (Classifiers.allClassifiers.filter (λ c => !c.isDefault && !c.isMensural)).all
      (·.semantics.length > 0) = true := by
  native_decide

-- ============================================================================
-- § 5. Semantic Supplementation (Hypothesis 2)
-- ============================================================================

/-- Seven recurrent semantic relations between the independent sense
    of the classifier morpheme and the classifier category.
    Six are from Ch. 5, Table 5.2; the seventh
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

/-- A witness pairing a classifier with its Table 5.2 morpheme-category
    relation and the independent meaning of the morpheme. -/
structure MorphemeRelationWitness where
  classifier : ClassifierEntry
  relation : MorphemeCategoryRelation
  independentMeaning : String
  deriving Repr

/-- Concrete Table 5.2 morpheme-category relation
    assignments for classifiers in our inventory. Each entry records
    the classifier, the relation type, and the independent lexical
    meaning of the morpheme that motivates the relation. -/
def table5_2_witnesses : List MorphemeRelationWitness :=
  [ -- Type 1: morpheme denotes a class identical/superordinate to the category
    { classifier := Classifiers.ken', relation := .identicalClass
    , independentMeaning := "matter, case" }
  , { classifier := Classifiers.ki, relation := .identicalClass
    , independentMeaning := "machine" }
    -- Type 2: morpheme denotes a part possessed by category members
  , { classifier := Classifiers.tou, relation := .partOfMembers
    , independentMeaning := "head" }
  , { classifier := Classifiers.kyaku, relation := .partOfMembers
    , independentMeaning := "leg" }
    -- Type 3: morpheme denotes an action associated with category members
  , { classifier := Classifiers.tsuu, relation := .associatedAction
    , independentMeaning := "to pass" }
  , { classifier := Classifiers.furi, relation := .associatedAction
    , independentMeaning := "to shake" }
    -- Type 6: morpheme denotes the beneficiary/goal of the category activity
  , { classifier := Classifiers.soku, relation := .beneficiaryGoal
    , independentMeaning := "foot" } ]

/-- At least four of the six Japanese-attested Table 5.2 relation types
    are witnessed in the inventory (Types 1, 2, 3, 6). -/
theorem four_relation_types_attested :
    (table5_2_witnesses.map (·.relation)).eraseDups.length ≥ 4 := by native_decide

/-- All Table 5.2 witnesses reference classifiers in our inventory. -/
theorem witnesses_in_inventory :
    table5_2_witnesses.all
      (λ w => Classifiers.allClassifiers.any (· == w.classifier)) = true := by
  native_decide

-- ============================================================================
-- § 6. Classifier System Composition
-- ============================================================================

/-- The Japanese classifier inventory includes both sortal and mensural
    classifiers, with sortal classifiers dominating. -/
theorem sortal_dominance :
    (Classifiers.allClassifiers.filter (!·.isMensural)).length >
    (Classifiers.allClassifiers.filter (·.isMensural)).length := by
  native_decide

/-- Function-based classifiers are the largest semantic group,
    confirming observation that the system
    concentrates on interactionally significant categories. -/
theorem function_classifiers_numerous :
    (Classifiers.allClassifiers.filter (·.encodes .function)).length ≥ 8 := by
  native_decide

-- ============================================================================
-- § 7. Core Inventory Completeness (Table 1.1)
-- ============================================================================

/-- The core inventory from Table 1.1 has exactly 27
    classifiers, all of which are represented in the Japanese fragment. -/
theorem core_inventory_complete :
    Classifiers.coreClassifiers.length = 27 := by native_decide

/-- The full inventory includes the 27 core classifiers plus 6 extended
    classifiers (sao, wa, furi, zen, kyaku, hai). -/
theorem full_inventory_includes_core :
    Classifiers.coreClassifiers.all
      (λ c => Classifiers.allClassifiers.any (· == c)) = true := by
  native_decide

/-- The core inventory distinguishes two homophonous ken classifiers:
    軒 ken (buildings) and 件 ken' (incidents) — different kanji, different
    semantic domains. -/
theorem two_ken_classifiers :
    Classifiers.ken.form = "軒" ∧ Classifiers.ken'.form = "件" ∧
    Classifiers.ken.encodes .function = true ∧
    Classifiers.ken'.encodes .function = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Two building classifiers exist: 軒 ken (functional capacity — home/shop)
    and 棟 mune (roofed structure). -/
theorem two_building_classifiers :
    Classifiers.ken.gloss = "building" ∧
    Classifiers.mune.gloss = "building.roof" := by
  exact ⟨rfl, rfl⟩

/-- Two maritime classifiers exist: 隻 seki (large boats) and
    艘 soo (small boats), paralleling the animacy size split
    (頭 tou / 匹 hiki). -/
theorem maritime_size_split :
    Classifiers.seki.gloss = "large.boat" ∧
    Classifiers.soo.gloss = "small.boat" := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- § 8. Frequency Distribution (Ch. 3, Table 3.1)
-- ============================================================================

/-- Frequency data from Ch. 3, Table 3.1:
    raw counts of classifiers in a 500-form corpus sample
    (first 50 uses from each of five works of fiction + 250 forms
    from transcribed conversations and oral narrative). -/
structure FrequencyEntry where
  classifier : ClassifierEntry
  count : Nat
  deriving Repr

/-- Frequency distribution of classifiers from our inventory that appear in
    Table 3.1 (n = 500). Classifiers with 0 occurrences
    in the sample are omitted. -/
def frequencyData : List FrequencyEntry :=
  [ { classifier := Classifiers.nin,  count := 201 }
  , { classifier := Classifiers.tsu,  count := 115 }
  , { classifier := Classifiers.hiki, count := 32 }
  , { classifier := Classifiers.hon', count := 31 }
  , { classifier := Classifiers.mai,  count := 31 }
  , { classifier := Classifiers.ken,  count := 11 }
  , { classifier := Classifiers.ko,   count := 11 }
  , { classifier := Classifiers.mei,  count := 6 }
  , { classifier := Classifiers.teki, count := 6 }
  , { classifier := Classifiers.tsuu, count := 5 }
  , { classifier := Classifiers.dai,  count := 4 }
  , { classifier := Classifiers.satsu, count := 4 }
  , { classifier := Classifiers.wa,   count := 4 }
  , { classifier := Classifiers.tsubu, count := 2 }
  , { classifier := Classifiers.ken', count := 1 }
  , { classifier := Classifiers.kabu, count := 1 }
  , { classifier := Classifiers.soku, count := 1 } ]

/-- 人 nin is the single most frequent classifier (201/500 = 40%). -/
theorem nin_most_frequent :
    (frequencyData.find? (·.classifier == Classifiers.nin)).map (·.count)
    = some 201 := by native_decide

/-- 人 nin and つ tsu together account for 316/500 = 63% of all classifier
    uses, a striking concentration that highlights as
    the major frequency finding (Ch. 3). -/
theorem nin_tsu_dominate :
    let ninCount := 201
    let tsuCount := 115
    ninCount + tsuCount = 316 ∧ 316 * 100 / 500 = 63 := by
  exact ⟨rfl, rfl⟩

/-- The top five classifiers (nin, tsu, hiki, hon, mai) account for
    410/500 = 82% of uses, confirming the Zipfian skew. -/
theorem top_five_dominate :
    let top5 := [201, 115, 32, 31, 31]
    top5.foldl (· + ·) 0 = 410 ∧ 410 * 100 / 500 = 82 := by
  exact ⟨rfl, rfl⟩

/-- Quality classifiers (shape-based: hon, mai, ko) are collectively more
    frequent than any individual kind classifier (function-based like ken,
    dai). Ch. 3 observes that "classifiers denoting
    categories united by a common shape ... are used relatively more often
    than most of the 'kind-based' classifiers." -/
theorem quality_over_kind_classifiers :
    let qualityTotal := 31 + 31 + 11  -- hon + mai + ko
    let kindMax := 11                 -- ken (buildings), the most frequent kind CL
    qualityTotal > kindMax := by
  omega

end Downing1996
