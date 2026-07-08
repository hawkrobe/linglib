import Linglib.Features.NounCategorization.Basic
import Linglib.Fragments.Romance.French.ClassifierSystem
import Linglib.Fragments.Italian.ClassifierSystem
import Linglib.Fragments.Mandarin.ClassifierSystem
import Linglib.Fragments.Japanese.ClassifierSystem
import Linglib.Fragments.Xhosa.ClassifierSystem
import Linglib.Fragments.Shona.ClassifierSystem
import Linglib.Fragments.Swahili.ClassifierSystem
import Linglib.Fragments.Armenian.ClassifierSystem
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Fragments.Japanese.Classifier

/-!
# Aikhenvald (2000): Classifiers — A Typology of Noun Categorization Devices
[aikhenvald-2000] [greenberg-1972] [dixon-1982]

Aikhenvald, Alexandra Y. (2000). *Classifiers: A Typology of Noun
Categorization Devices*. Oxford Studies in Typology and Linguistic Theory.
Oxford University Press.

Cross-linguistic typology of noun categorization systems following
Aikhenvald's 7-property schema (A–G, §1.5). The schema
(`System`) lives in `Typology/ClassifierSystem.lean`;
per-language data in `Fragments/{Lang}/ClassifierSystem.lean`.

This file aggregates the 7 currently-formalized systems
(French/Italian/Mandarin/Japanese/Xhosa/Shona/Swahili) and verifies
typological properties from [aikhenvald-2000] (Tables 10.17, 15.1,
15.2) and [greenberg-1972]'s classifier-number complementarity *over
that sample*. None of the theorems below are universals over the abstract
`System` type — they are sample-restricted empirical
claims; adding a counterexample language to the sample is the right way to
falsify them.

Western Armenian is intentionally *excluded* from the main `allSystems`
sample: it is non-obligatory with no unmarked default, and the
Aikhenvald-style sample-restricted findings (`sample_all_obligatory`,
`sample_all_have_default`) are about the obligatory-classifier subspace.
Armenian appears separately in `optionalClassifierSystems`.

Chierchia-anchored claims about Mandarin/Japanese type-shift blocking are
in `Studies/NMP.lean` (chronologically older paper, separate
study file). The Greenberg classifier-number complementarity claim
appears here (Aikhenvald §15 cites Greenberg) and is refined in
`Studies/LittleMoroneyRoyer2022.lean` (CLF-for-N vs CLF-for-NUM split).
-/

namespace Aikhenvald2000

open NounCategorization
open NounCategorization.System

-- ============================================================================
-- §0: Per-language convenience aliases
-- ============================================================================

abbrev french          := French.classifierSystem
abbrev italian         := Italian.classifierSystem
abbrev mandarin        := Mandarin.classifierSystem
abbrev japanese        := Japanese.classifierSystem
abbrev xhosa           := Xhosa.classifierSystem
abbrev shona           := Shona.classifierSystem
abbrev swahili         := Swahili.classifierSystem
abbrev westernArmenian := Armenian.classifierSystem

-- ============================================================================
-- §1: The cross-linguistic sample
-- ============================================================================

/-- The seven obligatory-classifier systems formalized so far. -/
def allSystems : List System :=
  [french, italian, mandarin, japanese, xhosa, shona, swahili]

/-- Languages whose Fragment is in `allSystems` are all obligatory. -/
theorem sample_all_obligatory :
    ∀ s ∈ allSystems, s.IsObligatory := by decide

/-- Languages in the sample all have an unmarked default classifier/class. -/
theorem sample_all_have_default :
    ∀ s ∈ allSystems, s.HasUnmarkedDefault := by decide

-- ============================================================================
-- §2: Per-language sanity checks
-- ============================================================================

theorem french_is_noun_class :
    isNounClassType French.classifierSystem.classifierType = true := rfl

theorem mandarin_is_classifier :
    isClassifierType Mandarin.classifierSystem.classifierType = true := rfl

theorem japanese_is_classifier :
    isClassifierType Japanese.classifierSystem.classifierType = true := rfl

theorem mandarin_inventory_from_fragment :
    Mandarin.classifierSystem.inventorySize = 15 := by decide

theorem japanese_inventory_from_fragment :
    Japanese.classifierSystem.inventorySize = 36 := by decide

theorem classifier_systems_have_default :
    Mandarin.classifierSystem.HasUnmarkedDefault ∧
    Japanese.classifierSystem.HasUnmarkedDefault := by decide

-- ============================================================================
-- §3: Aikhenvald Table 15.1 (sample-restricted)
-- ============================================================================

/-- [aikhenvald-2000] Table 15.1, sample-restricted: classifier-type
    systems lack agreement; noun-class systems have agreement. -/
theorem sample_classifier_no_agreement_nounclass_agreement :
    (∀ s ∈ allSystems, isClassifierType s.classifierType = true → ¬ s.HasAgreement) ∧
    (∀ s ∈ allSystems, isNounClassType s.classifierType = true → s.HasAgreement) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- French has agreement; Mandarin and Japanese do not (Table 15.1). -/
theorem fr_mandarin_jp_agreement_split :
    French.classifierSystem.HasAgreement ∧
    ¬ Mandarin.classifierSystem.HasAgreement ∧
    ¬ Japanese.classifierSystem.HasAgreement := by decide

/-- Numeral classifier systems have purely semantic assignment; the
    noun-class system has mixed assignment ([aikhenvald-2000] Table 15.2). -/
theorem fr_mandarin_jp_assignment_split :
    Mandarin.classifierSystem.assignment = .semantic ∧
    Japanese.classifierSystem.assignment = .semantic ∧
    French.classifierSystem.assignment = .mixed :=
  ⟨rfl, rfl, rfl⟩

/-- East Asian classifier systems prefer physical properties (shape) —
    partial witness for Aikhenvald's cross-linguistic generalization. -/
theorem mandarin_japanese_prefer_shape :
    Mandarin.classifierSystem.preferredSemantics.any (· == .shape) = true ∧
    Japanese.classifierSystem.preferredSemantics.any (· == .shape) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Animacy is attested in both Mandarin and Japanese classifiers. -/
theorem mandarin_japanese_have_animacy :
    Mandarin.classifierSystem.preferredSemantics.any (· == .animacy) = true ∧
    Japanese.classifierSystem.preferredSemantics.any (· == .animacy) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Mandarin/Japanese classifier inventories exceed French's noun-class
    inventory. [aikhenvald-2000] Table 15.1 generalization. -/
theorem fr_inventory_smaller_than_clf_inventories :
    French.classifierSystem.inventorySize <
      Mandarin.classifierSystem.inventorySize ∧
    French.classifierSystem.inventorySize <
      Japanese.classifierSystem.inventorySize := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- §4: Scope claims (sample-restricted)
-- ============================================================================

/-- Numeral classifiers operate inside numeral/quantifier NPs. -/
theorem mandarin_japanese_scope_numeralNP :
    Mandarin.classifierSystem.scopes.any (· == .numeralNP) = true ∧
    Japanese.classifierSystem.scopes.any (· == .numeralNP) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- French (the noun-class member of the sample) operates in
    head-modifier and predicate-argument scopes. -/
theorem french_scope_agreement :
    French.classifierSystem.scopes.any (· == .headModifierNP) = true ∧
    French.classifierSystem.scopes.any (· == .predicateArgument) = true := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- §5: Interaction with grammatical categories (Aikhenvald Table 10.17)
-- ============================================================================

/-- [aikhenvald-2000] Table 10.17: noun classes interact with more
    grammatical categories than numeral classifiers. Verified against the
    framework-agnostic `interacts` table in `NounCategorization.NounCategorization`. -/
theorem noun_class_more_interactions :
    let cats := [GrammaticalCategory.definiteness, .number, .case_, .tenseAspect, .possession]
    let ncInteractions := cats.filter (interacts .nounClass)
    let clInteractions := cats.filter (interacts .numeralClassifier)
    ncInteractions.length > clInteractions.length := by decide

-- ============================================================================
-- §6: Greenberg's classifier-number complementarity (sample-restricted)
-- ============================================================================

/-- [greenberg-1972]: numeral classifiers and obligatory number
    marking are in complementary distribution. Holds in the sample.
    Aikhenvald §15 endorses Greenberg's generalization;
    [little-moroney-royer-2022] §3.4 refines it (CLF-for-N languages
    obey it, CLF-for-NUM languages — Ch'ol, Mi'gmaq — falsify it). -/
theorem sample_greenberg_complementarity :
    (∀ s ∈ allSystems, isClassifierType s.classifierType = true → ¬ s.HasObligatoryNumber) ∧
    (∀ s ∈ allSystems, isNounClassType s.classifierType = true → s.HasObligatoryNumber) := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- §7: Default classifier facts
-- ============================================================================

/-- Mandarin and Japanese both have a semantically bleached default
    classifier (Mandarin 个 ge, Japanese つ tsu). -/
theorem mandarin_japanese_have_default_clf :
    Mandarin.Classifiers.defaultClassifier.isDefault = true ∧
    Japanese.Classifier.defaultClassifier? = some .tsu :=
  ⟨rfl, Japanese.Classifier.default_eq_tsu⟩

/-- Non-default classifiers always carry at least one semantic parameter. -/
theorem specific_classifiers_motivated :
    (Mandarin.Classifiers.allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true ∧
    ∀ c : Japanese.Classifier,
      ¬Japanese.Classifier.IsDefault c →
      ¬Japanese.Classifier.IsMensural c →
      c.encodes ≠ [] := by
  refine ⟨?_, ?_⟩
  · decide
  · exact Japanese.Classifier.specific_classifiers_have_semantics

-- ============================================================================
-- §8: Bantu noun-class systems (sample = Xhosa, Shona, Swahili)
-- ============================================================================

theorem xhosa_is_noun_class :
    isNounClassType Xhosa.classifierSystem.classifierType = true := rfl

theorem shona_is_noun_class :
    isNounClassType Shona.classifierSystem.classifierType = true := rfl

theorem swahili_is_noun_class :
    isNounClassType Swahili.classifierSystem.classifierType = true := rfl

theorem xhosa_has_agreement :
    Xhosa.classifierSystem.HasAgreement := by decide

/-- The three sampled Bantu languages have inventories in the
    [aikhenvald-2000] Table 15.1 noun-class range (≤ 20). -/
theorem sample_bantu_inventory_within_aikhenvald_range :
    Xhosa.classifierSystem.inventorySize ≤ 20 ∧
    Shona.classifierSystem.inventorySize ≤ 20 ∧
    Swahili.classifierSystem.inventorySize ≤ 20 := by decide

theorem bantu_have_prefix_realization :
    Xhosa.classifierSystem.realizations.any (· == .prefix) = true ∧
    Shona.classifierSystem.realizations.any (· == .prefix) = true ∧
    Swahili.classifierSystem.realizations.any (· == .prefix) = true := by decide

-- ============================================================================
-- §9: Optional-classifier systems
-- ============================================================================

/-- Languages with non-obligatory classifier systems (per WALS Ch 55
    `optional`). Western Armenian is the worked example
    ([bale-khanjian-2014]). Kept *separate* from `allSystems` because
    the sample-restricted findings above are over obligatory systems —
    Armenian is precisely the kind of language those generalizations
    don't cover. -/
def optionalClassifierSystems : List System :=
  [Armenian.classifierSystem]

theorem westernArmenian_not_obligatory :
    ¬ Armenian.classifierSystem.IsObligatory ∧
    ¬ Armenian.classifierSystem.HasUnmarkedDefault := by decide

end Aikhenvald2000
