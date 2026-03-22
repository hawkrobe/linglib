import Linglib.Core.Lexical.NounCategorization
import Linglib.Core.WALS.Features.F55A
import Linglib.Fragments.French.Nouns
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Fragments.Mandarin.Nouns
import Linglib.Fragments.Japanese.Classifiers
import Linglib.Fragments.Japanese.Nouns
import Linglib.Fragments.Italian.Nouns

/-!
# Classifier Typology
@cite{aikhenvald-2000} @cite{chierchia-1998} @cite{dixon-1982} @cite{greenberg-1972}

Cross-linguistic typology of noun categorization systems, following
@cite{aikhenvald-2000} "Classifiers: A Typology of Noun Categorization Devices."

## NounCategorizationSystem

@cite{aikhenvald-2000}'s 7-property (A–G) per-language system description.
The vocabulary types it depends on (`ClassifierType`, `SemanticParameter`,
`ClassifierEntry`, etc.) live in `Core.Lexical.NounCategorization` as
settled descriptive infrastructure; this file provides the framework for
assembling them into per-language system descriptions.

## Part I — Per-Language Data

Four languages from three families:
- **French** (Indo-European): Noun class / gender (2 classes). Agreement.
- **Italian** (Indo-European): Noun class / gender (2 classes). Agreement.
- **Mandarin** (Sino-Tibetan): Numeral classifiers (~100+). No agreement.
- **Japanese** (Japonic): Numeral classifiers (josūshi). No agreement.

System descriptions are **derived from** Fragment data (single source of truth).

## Part II — Universals

@cite{aikhenvald-2000}'s empirical generalizations (Chapters 11, 15):
agreement diagnostics, semantic parameter universals, inventory size
constraints, @cite{greenberg-1972} classifier–number complementarity.

## Thread map

- **Core infrastructure**: `Core.NounCategorization` —
  `ClassifierType`, `SemanticParameter`, `ClassifierEntry`
- **Classifier lexicons**: `Fragments.Mandarin.Classifiers`, `Fragments.Japanese.Classifiers`
- **Noun entries**: `Fragments.{Mandarin,Japanese,French,Italian}.Nouns`
- **WALS 55A**: `Core.WALS.F55A` — 400-language numeral classifier survey
  (imported in `Phenomena.Numerals.Typology`)
- **Chierchia bridge**: `Theories.Semantics.Lexical.Noun.Kind.Chierchia1998`
-/

namespace Phenomena.Classifiers.Typology

open Core.NounCategorization

-- ============================================================================
-- NounCategorizationSystem
-- ============================================================================

/-- A noun categorization system in a language.

    Captures @cite{aikhenvald-2000}'s 7 definitional properties (A–G from §1.5):
    (A) morphosyntactic locus → `scopes`
    (B) scope/domain → `classifierType` + `scopes`
    (C) assignment principles → `assignment`
    (D) surface realization → `realizations`
    (E) agreement → `hasAgreement`
    (F) markedness → `hasUnmarkedDefault`
    (G) grammaticalization → `isObligatory` -/
structure NounCategorizationSystem where
  /-- Language name -/
  language : String
  /-- Language family -/
  family : String
  /-- Aikhenvald classifier type -/
  classifierType : ClassifierType
  /-- Morphosyntactic scopes this system operates in (A, B) -/
  scopes : List CategorizationScope
  /-- How nouns are assigned to classes/classifiers (C) -/
  assignment : AssignmentPrinciple
  /-- Morphological realization types used (D) -/
  realizations : List SurfaceRealization
  /-- Does the system involve agreement? (E) — definitional for noun classes -/
  hasAgreement : Bool
  /-- Inventory size (number of classes or classifiers) -/
  inventorySize : Nat
  /-- Is realization obligatory or optional? (G) -/
  isObligatory : Bool
  /-- Is there a formally/functionally unmarked default? (F) -/
  hasUnmarkedDefault : Bool := false
  /-- Preferred semantic parameters (§11.2, Table 11.13) -/
  preferredSemantics : List SemanticParameter := []
  /-- Citation -/
  source : String := ""
  deriving Repr

-- ============================================================================
-- Dixon's Divide
-- ============================================================================

/-- @cite{dixon-1982}'s noun-class vs. classifier divide (Table 1.2).
    Noun classes: small, closed, grammaticalized, agreement.
    Classifiers: large, open, lexical, no agreement. -/
def isNounClassType (t : ClassifierType) : Bool :=
  t == .nounClass

/-- All non-noun-class types are "classifier" types in the broad sense. -/
def isClassifierType (t : ClassifierType) : Bool :=
  !isNounClassType t

-- ============================================================================
-- Part I: Cross-Linguistic Data
-- ============================================================================

/-- Compute preferred semantics from the actual classifier entries.
    This ensures adding a new classifier with a new parameter automatically
    updates the system description (single source of truth). -/
private def semanticsFromClassifiers (cls : List ClassifierEntry) :
    List SemanticParameter :=
  collectSemantics cls

-- ============================================================================
-- §1: French (Indo-European) — Noun class / gender
-- ============================================================================

/-- French noun categorization: 2-class gender system (masc/fem).
    Agreement on determiners, adjectives, and past participles.
    Aikhenvald type: noun class. -/
def french : NounCategorizationSystem :=
  { language := "French"
  , family := "Indo-European"
  , classifierType := .nounClass
  , scopes := [.headModifierNP, .predicateArgument]
  , assignment := .mixed  -- Mostly semantic + morphological residue
  , realizations := [.freeForm, .suffix]  -- le/la + -e/-eur, etc.
  , hasAgreement := true
  , inventorySize := 2  -- Masculine, feminine
  , isObligatory := true
  , hasUnmarkedDefault := true  -- Masculine is unmarked
  , preferredSemantics := [.sex, .animacy]
  , source := "Aikhenvald (2000), §2" }

-- ============================================================================
-- §1b: Italian (Indo-European) — Noun class / gender
-- ============================================================================

/-- Italian noun categorization: 2-class gender system (masc/fem).
    Like French, [-arg, +pred]. Agreement on determiners
    (il/la, un/una), adjectives (‑o/‑a), and past participles (‑o/‑a).
    Richer article allomorphy than French (il/lo/la, i/gli/le). -/
def italian : NounCategorizationSystem :=
  { language := "Italian"
  , family := "Indo-European"
  , classifierType := .nounClass
  , scopes := [.headModifierNP, .predicateArgument]
  , assignment := .mixed  -- Semantic (sex) + morphological (-o/-a endings)
  , realizations := [.freeForm, .suffix]  -- il/la + -o/-a, etc.
  , hasAgreement := true
  , inventorySize := 2  -- Masculine, feminine
  , isObligatory := true
  , hasUnmarkedDefault := true  -- Masculine is unmarked
  , preferredSemantics := [.sex, .animacy]
  , source := "Aikhenvald (2000), §2; Chierchia (1998)" }

-- ============================================================================
-- §2: Mandarin (Sino-Tibetan) — Numeral classifier
-- ============================================================================

/-- Mandarin noun categorization: numeral classifier system.
    Large inventory, semantically motivated, no agreement.
    Aikhenvald type: numeral classifier. -/
def mandarin : NounCategorizationSystem :=
  { language := "Mandarin"
  , family := "Sino-Tibetan"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP]
  , assignment := .semantic
  , realizations := [.freeForm]
  , hasAgreement := false
  , inventorySize := Fragments.Mandarin.Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true  -- 个 gè is default
  , preferredSemantics := semanticsFromClassifiers Fragments.Mandarin.Classifiers.allClassifiers
  , source := "Aikhenvald (2000), §4, §11.2.3" }

-- ============================================================================
-- §3: Japanese (Japonic) — Numeral classifier
-- ============================================================================

/-- Japanese noun categorization: numeral classifier system (josūshi).
    Similar to Mandarin but with native Japanese default counter (つ).
    Aikhenvald type: numeral classifier. -/
def japanese : NounCategorizationSystem :=
  { language := "Japanese"
  , family := "Japonic"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP]
  , assignment := .semantic
  , realizations := [.suffix]  -- Classifiers suffix to numerals
  , hasAgreement := false
  , inventorySize := Fragments.Japanese.Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true  -- つ tsu is default
  , preferredSemantics := semanticsFromClassifiers Fragments.Japanese.Classifiers.allClassifiers
  , source := "@cite{aikhenvald-2000}; @cite{downing-1996}" }

-- ============================================================================
-- §4: Per-language verification
-- ============================================================================

/-- French is a noun-class system. -/
theorem french_is_noun_class :
    isNounClassType french.classifierType = true := rfl

/-- Mandarin is a classifier system (not noun class). -/
theorem mandarin_is_classifier :
    isClassifierType mandarin.classifierType = true := rfl

/-- Japanese is a classifier system (not noun class). -/
theorem japanese_is_classifier :
    isClassifierType japanese.classifierType = true := rfl

/-- French has agreement; Mandarin and Japanese do not (Table 15.1). -/
theorem agreement_divides_types :
    french.hasAgreement = true ∧
    mandarin.hasAgreement = false ∧
    japanese.hasAgreement = false := ⟨rfl, rfl, rfl⟩

/-- Mandarin inventory is derived from the classifier lexicon. -/
theorem mandarin_inventory_from_fragment :
    mandarin.inventorySize = 15 := by native_decide

/-- Japanese inventory is derived from the classifier lexicon. -/
theorem japanese_inventory_from_fragment :
    japanese.inventorySize = 33 := by native_decide

/-- Both classifier systems have a default (Mandarin 个, Japanese つ). -/
theorem classifier_systems_have_default :
    mandarin.hasUnmarkedDefault = true ∧
    japanese.hasUnmarkedDefault = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §6: Cross-linguistic summary
-- ============================================================================

def allSystems : List NounCategorizationSystem :=
  [french, italian, mandarin, japanese]

/-- All four systems are obligatory (not optional). -/
theorem all_obligatory :
    allSystems.all (·.isObligatory) = true := by native_decide

/-- All four systems have an unmarked default. -/
theorem all_have_default :
    allSystems.all (·.hasUnmarkedDefault) = true := by native_decide

/-- Numeral classifier languages have no agreement;
    noun class languages have agreement (Aikhenvald Table 15.1). -/
theorem classifier_no_agreement_nounclass_agreement :
    (allSystems.filter (isClassifierType ·.classifierType)).all
      (!·.hasAgreement) = true ∧
    (allSystems.filter (isNounClassType ·.classifierType)).all
      (·.hasAgreement) = true := by
  constructor <;> native_decide

/-- Numeral classifier systems have purely semantic assignment;
    noun class systems have mixed assignment (Aikhenvald Table 15.2). -/
theorem classifier_semantic_nounclass_mixed :
    mandarin.assignment = .semantic ∧
    japanese.assignment = .semantic ∧
    french.assignment = .mixed := ⟨rfl, rfl, rfl⟩

/-- Bare NPs are licensed in [+arg] languages, not in [-arg] languages.
    This connects Fragment-level bare NP facts to the typological parameter. -/
theorem bare_np_tracks_arg :
    Fragments.Mandarin.Nouns.bareNPLicensed = true ∧
    Fragments.Japanese.Nouns.bareNPLicensed = true ∧
    Fragments.French.Nouns.barePluralLicensed = false := ⟨rfl, rfl, rfl⟩

/-- Blocking principle: [+arg, -pred] languages have no articles to block
    covert type shifts. [-arg, +pred] languages block ι and ∃. -/
theorem blocking_tracks_mapping :
    Fragments.Mandarin.Nouns.mandarinBlocking.iotaBlocked = false ∧
    Fragments.Japanese.Nouns.japaneseBlocking.iotaBlocked = false ∧
    Fragments.French.Nouns.frenchBlocking.iotaBlocked = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Part II: Universals (@cite{aikhenvald-2000}, Chapters 11 and 15)
-- ============================================================================

-- ============================================================================
-- §7: Agreement universals (@cite{aikhenvald-2000}, Table 15.1)
-- ============================================================================

/-- U1 (Aikhenvald Table 15.1): Noun class / gender systems require agreement.
    This is definitional — agreement is what makes a noun class system a
    "class" rather than a "classifier" (@cite{dixon-1982}, Table 1.2). -/
axiom noun_class_requires_agreement :
  ∀ sys : NounCategorizationSystem,
    isNounClassType sys.classifierType = true →
    sys.hasAgreement = true

/-- U2 (Aikhenvald Table 15.1): Numeral classifier systems lack agreement.
    Classifiers are independent morphemes, not agreement markers.
    Witnessed by Mandarin and Japanese in our typology. -/
axiom numeral_classifier_no_agreement :
  ∀ sys : NounCategorizationSystem,
    sys.classifierType = .numeralClassifier →
    sys.hasAgreement = false

-- ============================================================================
-- §8: Assignment universals (@cite{aikhenvald-2000}, §11.1, Table 15.2)
-- ============================================================================

/-- U3 (Aikhenvald §11.1.1): Classifier selection is always at least partly
    semantic. There are no purely phonological or purely morphological
    classifier systems (unlike noun class, which can be morphological). -/
axiom classifier_assignment_semantic :
  ∀ sys : NounCategorizationSystem,
    isClassifierType sys.classifierType = true →
    sys.assignment = .semantic ∨ sys.assignment = .mixed

/-- U4 (Aikhenvald Table 15.2): Noun class assignment may be mixed
    (semantic core + morphological overlay), while classifier systems
    are purely semantic. Witnessed by French (mixed) vs Mandarin (semantic). -/
theorem assignment_difference :
    french.assignment = .mixed ∧
    mandarin.assignment = .semantic ∧
    japanese.assignment = .semantic := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §9: Semantic parameter universals (@cite{aikhenvald-2000}, §11.1.1)
-- ============================================================================

/-- U5 (Aikhenvald §11.1.1): Animacy (animate vs. inanimate or human vs.
    non-human) is a semantic parameter found in EVERY type of noun
    categorization device. This is the universal semantic "core." -/
axiom animacy_universal :
  ∀ sys : NounCategorizationSystem,
    sys.preferredSemantics.any (· == .animacy) = true ∨
    sys.preferredSemantics.any (· == .humanness) = true

/-- U6 (Aikhenvald §11.1.1): Physical properties (shape, size) are the
    preferred semantic parameters for numeral classifiers, while animacy
    is the core for noun classes. -/
theorem classifiers_prefer_physical :
    mandarin.preferredSemantics.any (· == .shape) = true ∧
    japanese.preferredSemantics.any (· == .shape) = true := by
  constructor <;> native_decide

/-- U7 (Aikhenvald §11.2.3): In numeral classifier systems, animacy
    outranks shape, which outranks function. Formalized as an implicational
    universal: if a system uses shape, it also uses animacy; if function,
    also shape.
    TODO: prove from attested systems once typology is extended. -/
axiom classifier_semantic_hierarchy :
  ∀ sys : NounCategorizationSystem,
    isClassifierType sys.classifierType = true →
    (sys.preferredSemantics.any (· == .shape) = true →
     sys.preferredSemantics.any (· == .animacy) = true) ∧
    (sys.preferredSemantics.any (· == .function) = true →
     sys.preferredSemantics.any (· == .shape) = true)

/-- Animacy is attested in both Mandarin and Japanese classifiers.
    Derived from the classifier lexicons (witnessed by 只 zhī and 匹 hiki). -/
theorem animacy_in_both_classifier_systems :
    mandarin.preferredSemantics.any (· == .animacy) = true ∧
    japanese.preferredSemantics.any (· == .animacy) = true := by
  constructor <;> native_decide

-- ============================================================================
-- §10: Inventory size universals (@cite{aikhenvald-2000}, Table 15.1)
-- ============================================================================

/-- U8 (Aikhenvald Table 15.1): Noun class systems have small inventories
    (2–20 classes), while classifier systems have large inventories
    (typically 20–200+). -/
axiom noun_class_small_inventory :
  ∀ sys : NounCategorizationSystem,
    isNounClassType sys.classifierType = true →
    sys.inventorySize ≤ 20

/-- U9 (Aikhenvald §1.5): Classifier systems have larger inventories than
    noun class systems. Open (extendable) vs. closed. -/
theorem french_smaller_than_classifiers :
    french.inventorySize < mandarin.inventorySize ∧
    french.inventorySize < japanese.inventorySize := by
  constructor <;> native_decide

-- ============================================================================
-- §11: Scope universals (@cite{aikhenvald-2000}, Table 15.1)
-- ============================================================================

/-- U10 (Aikhenvald Table 15.1): Numeral classifiers operate inside
    numeral/quantifier NPs. -/
theorem numeral_classifiers_scope_numeralNP :
    mandarin.scopes.any (· == .numeralNP) = true ∧
    japanese.scopes.any (· == .numeralNP) = true := by
  constructor <;> native_decide

/-- U11 (Aikhenvald Table 15.1): Noun classes operate inside head-modifier
    NPs and predicate-argument structures (agreement). -/
theorem noun_class_scope_agreement :
    french.scopes.any (· == .headModifierNP) = true ∧
    french.scopes.any (· == .predicateArgument) = true := by
  constructor <;> native_decide

-- ============================================================================
-- §12: Interaction with other grammatical categories (Table 10.17)
-- ============================================================================

/-- Table 10.17 interaction matrix (simplified): Which grammatical categories
    interact with which classifier types.

    Key patterns:
    - Noun classes interact with definiteness, number, case, tense/aspect
    - Numeral classifiers interact with number, definiteness
    - Verbal classifiers interact with tense/aspect -/
inductive GrammaticalCategory where
  | definiteness | number | case_ | tenseAspect | possession
  deriving DecidableEq, Repr, BEq

/-- Whether a classifier type typically interacts with a grammatical category
    (Aikhenvald Table 10.17). -/
def interacts : ClassifierType → GrammaticalCategory → Bool
  | .nounClass, .definiteness => true
  | .nounClass, .number => true
  | .nounClass, .case_ => true
  | .nounClass, .tenseAspect => true
  | .nounClass, .possession => true
  | .numeralClassifier, .definiteness => true
  | .numeralClassifier, .number => true
  | .numeralClassifier, .possession => false
  | .numeralClassifier, .case_ => false
  | .numeralClassifier, .tenseAspect => false
  | .verbalClassifier, .tenseAspect => true
  | .verbalClassifier, .number => true
  | .relationalClassifier, .possession => true
  | .possessedClassifier, .possession => true
  | _, _ => false

/-- Noun classes interact with more grammatical categories than numeral
    classifiers (Table 10.17). This reflects their deeper grammaticalization. -/
theorem noun_class_more_interactions :
    let cats := [GrammaticalCategory.definiteness, .number, .case_, .tenseAspect, .possession]
    let ncInteractions := cats.filter (interacts .nounClass)
    let clInteractions := cats.filter (interacts .numeralClassifier)
    ncInteractions.length > clInteractions.length := by native_decide

-- ============================================================================
-- §13: @cite{greenberg-1972} universal
-- ============================================================================

/- @cite{greenberg-1972}: Numeral classifiers and obligatory number marking are
   in complementary distribution. Witnessed by Mandarin (no number morphology)
   and Japanese (optional -tachi) vs. French (obligatory singular/plural).
   TODO: Add `hasObligatoryNumber : Bool` to NounCategorizationSystem to state
   this formally. -/

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
-- §14: Default classifier universals
-- ============================================================================

/-- U12: Every numeral classifier system has a semantically bleached default
    classifier that can substitute for any specific classifier (Aikhenvald
    §4.2). The default is the "elsewhere" case.

    Witnessed by: Mandarin 个 gè, Japanese つ tsu. -/
theorem default_classifiers_exist :
    Fragments.Mandarin.Classifiers.defaultClassifier.isDefault = true ∧
    Fragments.Japanese.Classifiers.defaultClassifier.isDefault = true := ⟨rfl, rfl⟩

/-- Non-default classifiers always carry at least one semantic parameter.
    The default is the only semantically empty classifier. -/
theorem specific_classifiers_motivated :
    (Fragments.Mandarin.Classifiers.allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true ∧
    (Fragments.Japanese.Classifiers.allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true := by
  constructor <;> native_decide

-- ============================================================================
-- Part III: WALS Chapter 55 — Numeral Classifiers (Gil)
-- ============================================================================

/-- Whether a language uses numeral classifiers (WALS Ch 55).

    Numeral classifiers are morphemes that co-occur with a numeral when it
    modifies a noun (e.g., Mandarin san *ge* ren 'three CL person'). The key
    distinction is between obligatory classifiers (required whenever a numeral
    modifies a noun) and optional classifiers (available but not required). -/
inductive ClassifierStatus where
  | absent               -- no numeral classifiers (e.g., English, Spanish, Arabic)
  | optional             -- classifiers available but not required (e.g., Turkish, Bengali)
  | obligatory           -- classifiers required with numeral+noun (e.g., Mandarin, Japanese, Thai)
  deriving DecidableEq, BEq, Repr

/-- WALS Chapter 55 distribution: language counts per classifier status.
    Total: 400 languages. -/
structure ClassifierDistribution where
  absent : Nat
  optional : Nat
  obligatory : Nat
  deriving Repr

def ClassifierDistribution.total (d : ClassifierDistribution) : Nat :=
  d.absent + d.optional + d.obligatory

/-- Actual WALS Ch 55 counts. -/
def ch55Distribution : ClassifierDistribution :=
  { absent := 260
  , optional := 62
  , obligatory := 78 }

/-- Ch 55 total: 400 languages. -/
example : ch55Distribution.total = 400 := by native_decide

/-- Convert WALS 55A numeral classifier values to our ClassifierStatus type.
    The mapping is one-to-one: absent, optional, obligatory. -/
def fromWALS55A : Core.WALS.F55A.NumeralClassifiers → ClassifierStatus
  | .absent => .absent
  | .optional => .optional
  | .obligatory => .obligatory

/-- Languages without numeral classifiers are the global majority (WALS Ch 55).
    260 out of 400 sampled languages lack classifiers entirely. -/
theorem no_classifiers_is_majority :
    ch55Distribution.absent > ch55Distribution.optional + ch55Distribution.obligatory := by
  native_decide

/-- Languages without classifiers constitute over half the sample. -/
theorem no_classifiers_over_half :
    ch55Distribution.absent * 2 > ch55Distribution.total := by
  native_decide

/-- Obligatory classifiers are more common than optional ones globally.
    This is somewhat counterintuitive — it suggests that once a language
    develops classifiers, they tend to become grammaticalized as obligatory. -/
theorem obligatory_more_common_than_optional :
    ch55Distribution.obligatory > ch55Distribution.optional := by
  native_decide

end Phenomena.Classifiers.Typology
