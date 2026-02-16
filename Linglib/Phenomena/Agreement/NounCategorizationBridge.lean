import Linglib.Phenomena.Agreement.NounCategorization
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-!
# Bridge: Noun Categorization × Chierchia (1998) Nominal Mapping Parameter

Connects the cross-linguistic noun categorization typology in
`Phenomena.Agreement.NounCategorization` to the Nominal Mapping
Parameter from `Theories.TruthConditional.Noun.Kind.Chierchia1998`.

## Predictions verified

- `argOnly_implies_numeral_classifier`: [+arg, -pred] → numeral classifiers
- `predOnly_implies_noun_class`: [-arg, +pred] → noun class
- `mandarin_chierchia_consistent`, `japanese_chierchia_consistent`,
  `french_chierchia_consistent`: Actual classifier types match predictions

## Known gaps

- English [+arg, +pred] prediction (no system) not yet connected to data
-/

namespace Phenomena.Agreement.NounCategorization.Bridge

open Core.NounCategorization
open TruthConditional.Noun.Kind.Chierchia1998 (NominalMapping)
open Phenomena.Agreement.NounCategorization

/-- Map NominalMapping to the expected classifier type.
    [+arg, -pred] languages have numeral classifiers.
    [-arg, +pred] languages have noun class/gender.
    [+arg, +pred] languages (English/Germanic) lack a productive system. -/
def nominalMappingToClassifierType : NominalMapping → Option ClassifierType
  | .argOnly => some .numeralClassifier   -- Mandarin, Japanese
  | .predOnly => some .nounClass          -- French, Italian
  | .argAndPred => none                   -- English: no productive system

/-- French mapping is [-arg, +pred] (Chierchia 1998). -/
theorem french_mapping : Fragments.French.Nouns.frenchMapping = .predOnly := rfl

/-- Mandarin mapping is [+arg, -pred] (Chierchia 1998). -/
theorem mandarin_mapping : Fragments.Mandarin.Nouns.mandarinMapping = .argOnly := rfl

/-- Japanese mapping is [+arg, -pred] (Chierchia 1998). -/
theorem japanese_mapping : Fragments.Japanese.Nouns.japaneseMapping = .argOnly := rfl

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

end Phenomena.Agreement.NounCategorization.Bridge
