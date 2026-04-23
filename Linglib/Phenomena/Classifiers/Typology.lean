import Linglib.Core.Lexical.NounCategorization
import Linglib.Core.Typology.ClassifierSystem
import Linglib.Datasets.WALS.Features.F55A
import Linglib.Fragments.French.Nouns
import Linglib.Fragments.French.Typology
import Linglib.Fragments.Mandarin.Nouns
import Linglib.Fragments.Mandarin.Typology
import Linglib.Fragments.Japanese.Nouns
import Linglib.Fragments.Japanese.Typology
import Linglib.Fragments.Italian.Nouns
import Linglib.Fragments.Italian.Typology
import Linglib.Fragments.Xhosa.Typology
import Linglib.Fragments.Shona.Typology
import Linglib.Fragments.Swahili.Typology
import Linglib.Fragments.Armenian.Typology

/-!
# Classifier Typology
@cite{aikhenvald-2000} @cite{chierchia-1998} @cite{dixon-1982} @cite{greenberg-1972}

Cross-linguistic typology of noun categorization systems following
@cite{aikhenvald-2000} "Classifiers: A Typology of Noun Categorization Devices."

## Architecture

The schema (`NounCategorizationSystem`) lives in
`Core.Typology.ClassifierSystem`, parallel to
`Core.Typology.WordOrder`/`Adposition`. Per-language data lives in each
language's `Fragments/{Lang}/Typology.lean`, accessed through
`LanguageProfile.classifierSystem`.

This file is the cross-linguistic *aggregation* layer: it pulls system
descriptions from the seven currently-formalized languages (French,
Italian, Mandarin, Japanese, Xhosa, Shona, Swahili) and verifies typological
properties from @cite{aikhenvald-2000} and @cite{greenberg-1972} *over
that sample*. None of the theorems below are universals over the
abstract `NounCategorizationSystem` type — they are sample-restricted
empirical claims, and adding a counterexample language to the sample is
the right way to falsify them. (Earlier versions stipulated several
`axiom` declarations that did make universal claims; those were
soundness landmines and have been removed.)

## Convenience extractors

Per-language `def` extractors below use `csOf`, which wraps `Option.getD`
with a sentinel default whose `family` is `"<missing>"` and whose other
fields are intentionally weird. If a Fragment ever drops its
`classifierSystem` field, every per-language theorem below will fail
loudly: the `decide` proof can't unify the sentinel against the
expected real values. (`Option.get!` was tried first but doesn't reduce
through `decide`.)
-/

namespace Phenomena.Classifiers.Typology

open Core.NounCategorization
open Core.Typology

-- ============================================================================
-- §1: Per-language convenience extractors
-- ============================================================================

/-- Extract a `NounCategorizationSystem` from a `LanguageProfile`'s
    `classifierSystem` field. The fallback uses sentinel values that
    don't match any realistic Fragment, so dropped fields surface as
    failed `decide` proofs in the per-language theorems below. -/
private def csOf (p : Core.Typology.LanguageProfile) : NounCategorizationSystem :=
  p.classifierSystem.getD
    { family := "<missing>", classifierType := .nounClassifier
    , scopes := [], assignment := .semantic, realizations := []
    , hasAgreement := false, inventorySize := 0, isObligatory := false }

abbrev french          := csOf Fragments.French.typology
abbrev italian         := csOf Fragments.Italian.typology
abbrev mandarin        := csOf Fragments.Mandarin.typology
abbrev japanese        := csOf Fragments.Japanese.typology
abbrev xhosa           := csOf Fragments.Xhosa.typology
abbrev shona           := csOf Fragments.Shona.typology
abbrev swahili         := csOf Fragments.Swahili.typology
abbrev westernArmenian := csOf Fragments.Armenian.typology

-- ============================================================================
-- §2: Per-language sanity checks
-- ============================================================================

open NounCategorizationSystem in
theorem french_is_noun_class : isNounClassType french.classifierType = true := rfl

open NounCategorizationSystem in
theorem mandarin_is_classifier : isClassifierType mandarin.classifierType = true := rfl

open NounCategorizationSystem in
theorem japanese_is_classifier : isClassifierType japanese.classifierType = true := rfl

theorem mandarin_inventory_from_fragment :
    mandarin.inventorySize = 15 := by decide

theorem japanese_inventory_from_fragment :
    japanese.inventorySize = 36 := by decide

theorem classifier_systems_have_default :
    mandarin.hasUnmarkedDefault = true ∧
    japanese.hasUnmarkedDefault = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §3: Cross-linguistic sample
-- ============================================================================

/-- The seven systems formalized so far (4 Indo-European + 2 East Asian + 3
    Bantu). Built from per-language `LanguageProfile.classifierSystem`
    fields via `filterMap`, so adding a language to the import list above
    automatically extends the sample.

    Western Armenian is intentionally *excluded*: it is non-obligatory
    with no unmarked default, and the @cite{aikhenvald-2000}-style
    sample-restricted findings below (`all_obligatory`, `all_have_default`)
    are about the obligatory-classifier subspace. Armenian appears
    separately in `optionalClassifierSystems`. -/
def allSystems : List NounCategorizationSystem :=
  [Fragments.French.typology, Fragments.Italian.typology,
   Fragments.Mandarin.typology, Fragments.Japanese.typology,
   Fragments.Xhosa.typology, Fragments.Shona.typology,
   Fragments.Swahili.typology].filterMap (·.classifierSystem)

/-- Languages whose Fragment is in `allSystems` are all obligatory. -/
theorem sample_all_obligatory :
    allSystems.all (·.isObligatory) = true := by decide

/-- Languages in the sample all have an unmarked default classifier/class. -/
theorem sample_all_have_default :
    allSystems.all (·.hasUnmarkedDefault) = true := by decide

open NounCategorizationSystem in
/-- @cite{aikhenvald-2000} Table 15.1, sample-restricted: in our 7
    languages, classifier-type systems lack agreement and noun-class
    systems have agreement. -/
theorem sample_classifier_no_agreement_nounclass_agreement :
    (allSystems.filter (isClassifierType ·.classifierType)).all
      (!·.hasAgreement) = true ∧
    (allSystems.filter (isNounClassType ·.classifierType)).all
      (·.hasAgreement) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Bare NPs are licensed in [+arg] languages, not in [-arg] languages. -/
theorem bare_np_tracks_arg :
    Fragments.Mandarin.Nouns.bareNPLicensed = true ∧
    Fragments.Japanese.Nouns.bareNPLicensed = true ∧
    Fragments.French.Nouns.barePluralLicensed = false := ⟨rfl, rfl, rfl⟩

/-- @cite{chierchia-1998} blocking principle: [+arg, -pred] languages have no
    articles to block covert type shifts. [-arg, +pred] languages block ι and ∃. -/
theorem blocking_tracks_mapping :
    Fragments.Mandarin.Nouns.mandarinBlocking.iotaBlocked = false ∧
    Fragments.Japanese.Nouns.japaneseBlocking.iotaBlocked = false ∧
    Fragments.French.Nouns.frenchBlocking.iotaBlocked = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §4: Sample-restricted empirical claims (@cite{aikhenvald-2000})
-- ============================================================================

/-! All theorems in this section quantify over `allSystems` (or specific
languages within it) — they are *not* universals over the abstract
`NounCategorizationSystem` type. Adding a counterexample language to the
sample falsifies the relevant theorem; that is the intended falsification
mode. -/

/-- French has agreement; Mandarin and Japanese do not (@cite{aikhenvald-2000} Table 15.1). -/
theorem fr_mandarin_jp_agreement_split :
    french.hasAgreement = true ∧
    mandarin.hasAgreement = false ∧
    japanese.hasAgreement = false := ⟨rfl, rfl, rfl⟩

/-- Numeral classifier systems in the sample have purely semantic
    assignment; the noun-class system has mixed assignment
    (@cite{aikhenvald-2000} Table 15.2). -/
theorem fr_mandarin_jp_assignment_split :
    mandarin.assignment = .semantic ∧
    japanese.assignment = .semantic ∧
    french.assignment = .mixed := ⟨rfl, rfl, rfl⟩

/-- The two East Asian classifier systems in the sample prefer physical
    properties (shape) — partial witness for @cite{aikhenvald-2000}'s
    cross-linguistic generalization. Not a universal over
    `NounCategorizationSystem`. -/
theorem mandarin_japanese_prefer_shape :
    mandarin.preferredSemantics.any (· == .shape) = true ∧
    japanese.preferredSemantics.any (· == .shape) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Animacy is attested in both Mandarin and Japanese classifiers
    (witnessed by 只 zhī and 匹 hiki). -/
theorem mandarin_japanese_have_animacy :
    mandarin.preferredSemantics.any (· == .animacy) = true ∧
    japanese.preferredSemantics.any (· == .animacy) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Mandarin/Japanese classifier inventories exceed French's noun-class
    inventory. Sample-restricted; @cite{aikhenvald-2000} Table 15.1 reports
    the cross-linguistic tendency that classifier systems are larger than
    noun-class systems. -/
theorem fr_inventory_smaller_than_clf_inventories :
    french.inventorySize < mandarin.inventorySize ∧
    french.inventorySize < japanese.inventorySize := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- §5: Sample-restricted scope claims
-- ============================================================================

/-- Numeral classifiers in the sample operate inside numeral/quantifier NPs. -/
theorem mandarin_japanese_scope_numeralNP :
    mandarin.scopes.any (· == .numeralNP) = true ∧
    japanese.scopes.any (· == .numeralNP) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- French (the noun-class member of the sample) operates in
    head-modifier and predicate-argument scopes. -/
theorem french_scope_agreement :
    french.scopes.any (· == .headModifierNP) = true ∧
    french.scopes.any (· == .predicateArgument) = true := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- §6: Interaction with grammatical categories
-- ============================================================================

/-- @cite{aikhenvald-2000} Table 10.17 records that noun classes interact
    with more grammatical categories than numeral classifiers. Verified
    here against the framework-agnostic `interacts` table in
    `Core.Typology.NounCategorization`. -/
theorem noun_class_more_interactions :
    let cats := [GrammaticalCategory.definiteness, .number, .case_, .tenseAspect, .possession]
    let ncInteractions := cats.filter (interacts .nounClass)
    let clInteractions := cats.filter (interacts .numeralClassifier)
    ncInteractions.length > clInteractions.length := by decide

-- ============================================================================
-- §7: Greenberg's classifier–number complementarity (sample-restricted)
-- ============================================================================

open NounCategorizationSystem in
/-- @cite{greenberg-1972}: numeral classifiers and obligatory number
    marking are in complementary distribution. Holds in our 7-language
    sample. @cite{little-moroney-royer-2022} §3.4 refines: Greenberg's
    generalization holds for CLF-for-N languages (CLF and PL share a
    projection) but fails for CLF-for-NUM languages (different
    projections — Ch'ol, Mi'gmaq). -/
theorem sample_greenberg_complementarity :
    (allSystems.filter (isClassifierType ·.classifierType)).all
      (!·.hasObligatoryNumber) = true ∧
    (allSystems.filter (isNounClassType ·.classifierType)).all
      (·.hasObligatoryNumber) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- No type-shift blocking in Mandarin. -/
theorem mandarin_no_blocking :
    Fragments.Mandarin.Nouns.mandarinBlocking.iotaBlocked = false ∧
    Fragments.Mandarin.Nouns.mandarinBlocking.existsBlocked = false ∧
    Fragments.Mandarin.Nouns.mandarinBlocking.downBlocked = false := ⟨rfl, rfl, rfl⟩

/-- No type-shift blocking in Japanese. -/
theorem japanese_no_blocking :
    Fragments.Japanese.Nouns.japaneseBlocking.iotaBlocked = false ∧
    Fragments.Japanese.Nouns.japaneseBlocking.existsBlocked = false ∧
    Fragments.Japanese.Nouns.japaneseBlocking.downBlocked = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §8: Default classifier facts
-- ============================================================================

/-- Mandarin and Japanese both have a semantically bleached default
    classifier (Mandarin 个 ge, Japanese つ tsu). -/
theorem mandarin_japanese_have_default_clf :
    Fragments.Mandarin.Classifiers.defaultClassifier.isDefault = true ∧
    Fragments.Japanese.Classifier.defaultClassifier? = some .tsu :=
  ⟨rfl, Fragments.Japanese.Classifier.default_eq_tsu⟩

/-- Non-default classifiers always carry at least one semantic parameter. -/
theorem specific_classifiers_motivated :
    (Fragments.Mandarin.Classifiers.allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true ∧
    ∀ c : Fragments.Japanese.Classifier,
      ¬Fragments.Japanese.Classifier.IsDefault c →
      ¬Fragments.Japanese.Classifier.IsMensural c →
      c.encodes ≠ [] := by
  refine ⟨?_, ?_⟩
  · decide
  · exact Fragments.Japanese.Classifier.specific_classifiers_have_semantics

-- ============================================================================
-- §9: Bantu noun-class systems (sample = Xhosa, Shona, Swahili)
-- ============================================================================

open NounCategorizationSystem in
theorem xhosa_is_noun_class : isNounClassType xhosa.classifierType = true := rfl

open NounCategorizationSystem in
theorem shona_is_noun_class : isNounClassType shona.classifierType = true := rfl

open NounCategorizationSystem in
theorem swahili_is_noun_class : isNounClassType swahili.classifierType = true := rfl

theorem xhosa_has_agreement : xhosa.hasAgreement = true := rfl

/-- The three sampled Bantu languages have inventories in the
    @cite{aikhenvald-2000} Table 15.1 noun-class range (≤ 20).
    Sample-restricted; the bound is an empirical generalization, not a
    type-level constraint. -/
theorem sample_bantu_inventory_within_aikhenvald_range :
    xhosa.inventorySize ≤ 20 ∧
    shona.inventorySize ≤ 20 ∧
    swahili.inventorySize ≤ 20 := by decide

theorem bantu_have_prefix_realization :
    xhosa.realizations.any (· == .prefix) = true ∧
    shona.realizations.any (· == .prefix) = true ∧
    swahili.realizations.any (· == .prefix) = true := by decide

-- ============================================================================
-- §10: Optional-classifier systems
-- ============================================================================

/-- Languages with non-obligatory classifier systems (per WALS Ch 55
    `optional`). Western Armenian is the worked example
    (@cite{bale-khanjian-2014}). Kept *separate* from `allSystems`
    because the sample-restricted findings above are over obligatory
    systems — Armenian is precisely the kind of language those
    generalizations don't cover. -/
def optionalClassifierSystems : List NounCategorizationSystem :=
  [westernArmenian]

theorem westernArmenian_not_obligatory :
    westernArmenian.isObligatory = false ∧
    westernArmenian.hasUnmarkedDefault = false := ⟨rfl, rfl⟩

-- ============================================================================
-- §11: WALS Chapter 55 — Numeral Classifiers (Gil)
-- ============================================================================

/-- Whether a language uses numeral classifiers (WALS Ch 55). -/
inductive ClassifierStatus where
  | absent      -- no numeral classifiers (English, Spanish, Arabic)
  | optional    -- classifiers available but not required (Turkish, Bengali)
  | obligatory  -- classifiers required (Mandarin, Japanese, Thai)
  deriving DecidableEq, Repr

/-- Convert WALS 55A numeral classifier values to the local `ClassifierStatus`. -/
def fromWALS55A : Datasets.WALS.F55A.NumeralClassifiers → ClassifierStatus
  | .absent => .absent
  | .optional => .optional
  | .obligatory => .obligatory

end Phenomena.Classifiers.Typology
