import Linglib.Semantics.Genericity.NominalMappingParameter
import Linglib.Studies.Aikhenvald2000
import Linglib.Fragments.Romance.French.Nouns
import Linglib.Fragments.Mandarin.Nouns
import Linglib.Fragments.Japanese.Nouns
import Linglib.Fragments.Italian.Nouns

/-!
Noun Categorization × [chierchia-1998] Nominal Mapping Parameter
[chierchia-1998]

Connects the cross-linguistic noun categorization typology in
`Aikhenvald2000` to the Nominal Mapping
Parameter from `Semantics.Kinds.NMP`.

## Predictions verified

- `argOnly_implies_numeral_classifier`: [+arg, -pred] → numeral classifiers
- `predOnly_implies_noun_class`: [-arg, +pred] → noun class
- `mandarin_chierchia_consistent`, `japanese_chierchia_consistent`,
  `french_chierchia_consistent`, `italian_chierchia_consistent`:
  Actual classifier types match predictions

## Classifier Strategy Connection ([little-moroney-royer-2022])

[chierchia-1998]'s theory is a CLF-for-N theory: the classifier
atomizes the noun denotation (which denotes kinds in [+arg, -pred]
languages). This predicts that classifiers in [+arg, -pred] languages
should appear beyond numerals — with demonstratives, quantifiers, and
relative clauses. Mandarin and Japanese confirm this (那本书 'that CLF
book', Mandarin).

The NMP-to-classifier bridge is accurate at Aikhenvald's morphosyntactic
level but does not distinguish between CLF-for-NUM and CLF-for-N within
the numeral classifier type. Both Ch'ol (CLF-for-NUM) and Shan (CLF-for-N)
are `numeralClassifier` in Aikhenvald's typology. The `ClassifierStrategy`
field on `NounCategorizationSystem` captures this finer distinction.

## Known gaps

- English [+arg, +pred] prediction (no system) not yet connected to data
-/

namespace NMP

open NounCategorization
open Semantics.Kinds.NMP (NominalMapping)
open Aikhenvald2000 (mandarin japanese french italian)

/-- Map NominalMapping to the expected classifier type.
    [+arg, -pred] languages have numeral classifiers.
    [-arg, +pred] languages have noun class/gender.
    [+arg, +pred] languages (English/Germanic) lack a productive system. -/
def nominalMappingToClassifierType : NominalMapping → Option ClassifierType
  | .argOnly => some .numeralClassifier   -- Mandarin, Japanese
  | .predOnly => some .nounClass          -- French, Italian
  | .argAndPred => none                   -- English: no productive system

/-- French mapping is [-arg, +pred]. -/
theorem french_mapping : French.Nouns.frenchMapping = .predOnly := rfl

/-- Mandarin mapping is [+arg, -pred]. -/
theorem mandarin_mapping : Mandarin.Nouns.mandarinMapping = .argOnly := rfl

/-- Japanese mapping is [+arg, -pred]. -/
theorem japanese_mapping : Japanese.Nouns.japaneseMapping = .argOnly := rfl

/-- Italian mapping is [-arg, +pred]. Italian is the
    star witness for `predOnly`: bare arguments are restricted and D
    must be projected for argumenthood. -/
theorem italian_mapping : Italian.Nouns.italianMapping = .predOnly := rfl

/-- The Chierchia-Aikhenvald bridge: [+arg, -pred] languages are numeral
    classifier languages. -/
theorem argOnly_implies_numeral_classifier :
    nominalMappingToClassifierType .argOnly = some .numeralClassifier := rfl

/-- [-arg, +pred] languages are noun class languages. -/
theorem predOnly_implies_noun_class :
    nominalMappingToClassifierType .predOnly = some .nounClass := rfl

/-- [+arg, +pred] languages (English/Germanic) lack a productive noun
    categorization system in Aikhenvald's sense. -/
theorem argAndPred_no_system :
    nominalMappingToClassifierType .argAndPred = none := rfl

/-- Mandarin's actual classifier type matches the Chierchia prediction. -/
theorem mandarin_chierchia_consistent :
    some mandarin.classifierType =
      nominalMappingToClassifierType Mandarin.Nouns.mandarinMapping := rfl

/-- Japanese's actual classifier type matches the Chierchia prediction. -/
theorem japanese_chierchia_consistent :
    some japanese.classifierType =
      nominalMappingToClassifierType Japanese.Nouns.japaneseMapping := rfl

/-- French's actual classifier type matches the Chierchia prediction. -/
theorem french_chierchia_consistent :
    some french.classifierType =
      nominalMappingToClassifierType French.Nouns.frenchMapping := rfl

/-- Italian's actual classifier type matches the Chierchia prediction. -/
theorem italian_chierchia_consistent :
    some italian.classifierType =
      nominalMappingToClassifierType Italian.Nouns.italianMapping := rfl

/-- French and Italian agree on Chierchia mapping: both are predOnly. -/
theorem french_italian_same_mapping :
    French.Nouns.frenchMapping =
      Italian.Nouns.italianMapping := rfl

/-! ## §2: [chierchia-1998]'s per-language strategy assignments

[chierchia-1998]'s theory is a CLF-for-N theory: the classifier
atomizes the noun denotation. The NMP determines that nouns denote kinds
(need individuation), so classifiers serve the noun (atomization), not the
numeral. This commits Chierchia's framework to a `.forNoun` strategy for
every [+arg, -pred] language with classifiers.

Per-language assignments live here (in this study file) rather than on
`NounCategorizationSystem`, where they would silently endorse Chierchia's
framework over alternatives like [sudo-2016]'s `.sudoBlocking`. -/

/-- Chierchia's strategy assignment for Japanese: CLF atomizes a kind-denoting
    noun. -/
def japaneseStrategy : NounCategorization.ClassifierStrategy := .forNoun

/-- Chierchia's strategy assignment for Mandarin: CLF atomizes a kind-denoting
    noun. -/
def mandarinStrategy : NounCategorization.ClassifierStrategy := .forNoun

/-- Chierchia's framework assigns the CLF-for-N strategy to all
    [+arg, -pred] classifier languages. -/
theorem chierchia_assignments_uniform :
    japaneseStrategy = .forNoun ∧ mandarinStrategy = .forNoun := ⟨rfl, rfl⟩

-- ============================================================================
-- §?: Bare-NP / Type-Shift Blocking Predictions
-- ============================================================================

/-! Empirical predictions of [chierchia-1998]'s Nominal Mapping
Parameter, verified against Fragment data. -/

/-- Bare NPs are licensed in [+arg] languages, not in [-arg] languages
    (Chierchia's central typological prediction). -/
theorem bare_np_tracks_arg :
    Mandarin.Nouns.bareNPLicensed = true ∧
    Japanese.Nouns.bareNPLicensed = true ∧
    French.Nouns.barePluralLicensed = false := ⟨rfl, rfl, rfl⟩

/-- Chierchia's blocking principle: [+arg, -pred] languages have no
    articles to block covert type shifts. [-arg, +pred] languages
    block ι and ∃. -/
theorem blocking_tracks_mapping :
    Mandarin.Nouns.mandarinBlocking.iotaBlocked = false ∧
    Japanese.Nouns.japaneseBlocking.iotaBlocked = false ∧
    French.Nouns.frenchBlocking.iotaBlocked = true := ⟨rfl, rfl, rfl⟩

/-- No type-shift blocking in Mandarin (`[+arg, -pred]`: ι, ∃, ∩ all
    available). -/
theorem mandarin_no_blocking :
    Mandarin.Nouns.mandarinBlocking.iotaBlocked = false ∧
    Mandarin.Nouns.mandarinBlocking.existsBlocked = false ∧
    Mandarin.Nouns.mandarinBlocking.downBlocked = false := ⟨rfl, rfl, rfl⟩

/-- No type-shift blocking in Japanese. -/
theorem japanese_no_blocking :
    Japanese.Nouns.japaneseBlocking.iotaBlocked = false ∧
    Japanese.Nouns.japaneseBlocking.existsBlocked = false ∧
    Japanese.Nouns.japaneseBlocking.downBlocked = false := ⟨rfl, rfl, rfl⟩

end NMP
