import Linglib.Semantics.Genericity.NominalMappingParameter
import Linglib.Fragments.Italian.NumberGender
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Fragments.Japanese.Classifiers
import Linglib.Fragments.Romance.French.Nouns
import Linglib.Fragments.Mandarin.Nouns
import Linglib.Fragments.Japanese.Nouns
import Linglib.Fragments.Italian.Nouns

/-!
# Chierchia 1998: the Nominal Mapping Parameter and noun categorization

This file formalizes the typological half of [chierchia-1998]. The Nominal Mapping Parameter sets
whether a language's nouns denote kinds, predicates, or either, and the noun categorization system
follows: a [+arg, −pred] language's kind-denoting nouns need individuating before they can be
counted, so it has numeral classifiers; a [−arg, +pred] language projects D for argumenthood and
carries noun class or gender instead; a [+arg, +pred] language has no productive system. Bare
arguments and covert type-shifting track the same setting — [+arg] languages license bare
arguments with no shift blocked, while a [−arg] language's articles pre-empt ι.

The parameter commits the framework to classifiers that serve the noun rather than the numeral:
`japaneseStrategy` and `mandarinStrategy` record that commitment, and the studies of later
classifier accounts dispute it there rather than in the Fragments.

## Main definitions

* `nominalMappingToClassifierType` — the mapping's predicted categorization system
* `predictsBareNP`, `predictsIotaBlocked` — its predicted bare-argument and blocking profile
* `japaneseStrategy`, `mandarinStrategy` — the classifier-for-noun commitment

## Main results

* `sample_matches_prediction` — each sampled language's recorded system is the predicted one
* `bare_np_tracks_mapping`, `iota_blocking_tracks_mapping`, `argOnly_no_blocking` — bare
  arguments and blocking track the mapping at the sampled languages

## References

* [chierchia-1998]
-/

namespace NMP

open Classifier
open Semantics.Kinds.NMP (NominalMapping)

/-- Map NominalMapping to the expected classifier type.
    [+arg, -pred] languages have numeral classifiers.
    [-arg, +pred] languages have noun class/gender.
    [+arg, +pred] languages (English/Germanic) lack a productive system. -/
def nominalMappingToClassifierType : NominalMapping → Option Kind
  | .argOnly => some .numeralClassifier   -- Mandarin, Japanese
  | .predOnly => some .nounClass          -- French, Italian
  | .argAndPred => none                   -- English: no productive system

/-- At each sampled language the recorded categorization system is the one its nominal mapping
predicts: numeral classifiers for Mandarin and Japanese, noun class for French and Italian. -/
theorem sample_matches_prediction :
    ∀ p ∈ [ (Mandarin.classifierKind, Mandarin.Nouns.mandarinMapping)
          , (Japanese.classifierKind, Japanese.Nouns.japaneseMapping)
          , (French.classifierKind, French.Nouns.frenchMapping)
          , (Italian.classifierKind, Italian.Nouns.italianMapping) ],
      p.1 = nominalMappingToClassifierType p.2 := by decide

/-! ### The classifier-for-noun commitment

The parameter makes the nouns of a [+arg, −pred] language denote kinds, which need individuating,
so the classifier serves the noun. The assignments are the framework's commitment and live here
rather than in the Fragments, which stay neutral between classifier accounts. -/

/-- Chierchia's strategy assignment for Japanese: CLF atomizes a kind-denoting
    noun. -/
def japaneseStrategy : Classifier.Strategy := .forNoun

/-- Chierchia's strategy assignment for Mandarin: CLF atomizes a kind-denoting
    noun. -/
def mandarinStrategy : Classifier.Strategy := .forNoun

/-! ### Bare arguments and type-shift blocking -/

/-- The mapping's predicted bare-argument profile: [+arg] languages license them. -/
def predictsBareNP : NominalMapping → Bool
  | .predOnly => false
  | _ => true

/-- The mapping's predicted ι-blocking: only a [−arg] language's articles pre-empt the shift. -/
def predictsIotaBlocked : NominalMapping → Bool
  | .predOnly => true
  | _ => false

/-- Bare-argument licensing tracks the mapping at the sampled languages. -/
theorem bare_np_tracks_mapping :
    ∀ p ∈ [ (Mandarin.Nouns.bareNPLicensed, Mandarin.Nouns.mandarinMapping)
          , (Japanese.Nouns.bareNPLicensed, Japanese.Nouns.japaneseMapping)
          , (French.Nouns.barePluralLicensed, French.Nouns.frenchMapping) ],
      p.1 = predictsBareNP p.2 := by decide

/-- So does ι-blocking. -/
theorem iota_blocking_tracks_mapping :
    ∀ p ∈ [ (Mandarin.Nouns.mandarinBlocking.iotaBlocked, Mandarin.Nouns.mandarinMapping)
          , (Japanese.Nouns.japaneseBlocking.iotaBlocked, Japanese.Nouns.japaneseMapping)
          , (French.Nouns.frenchBlocking.iotaBlocked, French.Nouns.frenchMapping) ],
      p.1 = predictsIotaBlocked p.2 := by decide

/-- A [+arg, −pred] language blocks no covert shift at all: ι, ∃ and ∩ are all available. -/
theorem argOnly_no_blocking :
    ∀ b ∈ [Mandarin.Nouns.mandarinBlocking, Japanese.Nouns.japaneseBlocking],
      b.iotaBlocked = false ∧ b.existsBlocked = false ∧ b.downBlocked = false := by decide

end NMP
