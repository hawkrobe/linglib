import Linglib.Phenomena.Classifiers.Typology
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-!
Noun Categorization × @cite{chierchia-1998} Nominal Mapping Parameter
@cite{chierchia-1998}

Connects the cross-linguistic noun categorization typology in
`Phenomena.Classifiers.Typology` to the Nominal Mapping
Parameter from `Theories.Semantics.Lexical.Noun.Kind.Chierchia1998`.

## Predictions verified

- `argOnly_implies_numeral_classifier`: [+arg, -pred] → numeral classifiers
- `predOnly_implies_noun_class`: [-arg, +pred] → noun class
- `mandarin_chierchia_consistent`, `japanese_chierchia_consistent`,
  `french_chierchia_consistent`, `italian_chierchia_consistent`:
  Actual classifier types match predictions

## Classifier Strategy Connection (@cite{little-moroney-royer-2022})

@cite{chierchia-1998}'s theory is a CLF-for-N theory: the classifier
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

namespace Chierchia1998

open Core.NounCategorization
open Semantics.Lexical.Noun.Kind.Chierchia1998 (NominalMapping)
open Phenomena.Classifiers.Typology

/-- Map NominalMapping to the expected classifier type.
    [+arg, -pred] languages have numeral classifiers.
    [-arg, +pred] languages have noun class/gender.
    [+arg, +pred] languages (English/Germanic) lack a productive system. -/
def nominalMappingToClassifierType : NominalMapping → Option ClassifierType
  | .argOnly => some .numeralClassifier   -- Mandarin, Japanese
  | .predOnly => some .nounClass          -- French, Italian
  | .argAndPred => none                   -- English: no productive system

/-- French mapping is [-arg, +pred]. -/
theorem french_mapping : Fragments.French.Nouns.frenchMapping = .predOnly := rfl

/-- Mandarin mapping is [+arg, -pred]. -/
theorem mandarin_mapping : Fragments.Mandarin.Nouns.mandarinMapping = .argOnly := rfl

/-- Japanese mapping is [+arg, -pred]. -/
theorem japanese_mapping : Fragments.Japanese.Nouns.japaneseMapping = .argOnly := rfl

/-- Italian mapping is [-arg, +pred]. Italian is the
    star witness for `predOnly`: bare arguments are restricted and D
    must be projected for argumenthood. -/
theorem italian_mapping : Fragments.Italian.Nouns.italianMapping = .predOnly := rfl

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
      nominalMappingToClassifierType Fragments.Mandarin.Nouns.mandarinMapping := rfl

/-- Japanese's actual classifier type matches the Chierchia prediction. -/
theorem japanese_chierchia_consistent :
    some japanese.classifierType =
      nominalMappingToClassifierType Fragments.Japanese.Nouns.japaneseMapping := rfl

/-- French's actual classifier type matches the Chierchia prediction. -/
theorem french_chierchia_consistent :
    some french.classifierType =
      nominalMappingToClassifierType Fragments.French.Nouns.frenchMapping := rfl

/-- Italian's actual classifier type matches the Chierchia prediction. -/
theorem italian_chierchia_consistent :
    some italian.classifierType =
      nominalMappingToClassifierType Fragments.Italian.Nouns.italianMapping := rfl

/-- French and Italian agree on Chierchia mapping: both are predOnly. -/
theorem french_italian_same_mapping :
    Fragments.French.Nouns.frenchMapping =
      Fragments.Italian.Nouns.italianMapping := rfl

/-- @cite{chierchia-1998}'s theory is a CLF-for-N theory: the classifier
    atomizes the noun denotation. This predicts CLF-for-N strategy for
    [+arg, -pred] languages, which is confirmed by Mandarin and Japanese
    (@cite{little-moroney-royer-2022}).

    The NMP determines that nouns denote kinds (need individuation),
    so classifiers serve the noun (atomization), not the numeral. -/
theorem chierchia_predicts_clf_for_noun :
    mandarin.classifierStrategy = some .forNoun ∧
    japanese.classifierStrategy = some .forNoun := ⟨rfl, rfl⟩

end Chierchia1998
