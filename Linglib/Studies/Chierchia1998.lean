module

public import Linglib.Semantics.Genericity.NominalMappingParameter
public import Linglib.Fragments.Romance.Italian.NumberGender
public import Linglib.Fragments.Mandarin.Classifiers
public import Linglib.Fragments.Japanese.Classifiers
public import Linglib.Fragments.Romance.French.Nouns
public import Linglib.Fragments.Romance.French.Determiners
public import Linglib.Fragments.Mandarin.Nouns
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Japanese.Nouns
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.Romance.Italian.Nouns
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Determiners

/-!
# Chierchia (1998): Reference to kinds across languages

This file formalizes the typological half of [chierchia-1998]. The Nominal Mapping Parameter sets
whether a language's nouns denote kinds, predicates, or either, and the noun categorization system
follows: a [+arg, −pred] language's kind-denoting nouns need individuating before they can be
counted, so it has numeral classifiers; a [−arg, +pred] language projects D for argumenthood and
carries noun class or gender instead; a [+arg, +pred] language has no productive system. Bare
arguments and covert type-shifting track the same setting: a [+arg, −pred] language has no
articles and blocks no shift, a [−arg] language's articles pre-empt ι, and a [+arg, +pred]
language with articles admits exactly the bare nominals kind formation is defined for, so
English has bare plurals and bare mass nouns but no bare singular count nouns. Each language's
blocking is derived from its determiner inventory by `Determiner.Inventory.Blocks`.

The parameter commits the framework to classifiers that serve the noun rather than the numeral:
`japaneseStrategy` and `mandarinStrategy` record that commitment, and the studies of later
classifier accounts dispute it there rather than in the Fragments.

## Main definitions

* `nominalMappingToClassifierType` — the mapping's predicted categorization system
* `japaneseStrategy`, `mandarinStrategy` — the classifier-for-noun commitment

## Main results

* `sample_matches_prediction` — each sampled language's recorded system is the predicted one
* `argOnly_blocks_nothing`, `predOnly_blocks_iota` — blocking at the sampled languages
* `english_licensesBare_iff` — English admits exactly the bare nominals ∩ is defined for

## References

* [chierchia-1998]
-/

@[expose] public section

namespace Chierchia1998

open Classifier
open Genericity

/-- Map NominalMapping to the expected classifier type.
    [+arg, -pred] languages have numeral classifiers.
    [-arg, +pred] languages have noun class/gender.
    [+arg, +pred] languages (English/Germanic) lack a productive system. -/
def nominalMappingToClassifierType (m : NominalMapping) : Option Kind :=
  if .kind ∈ m then if .property ∈ m then none else some .numeralClassifier
  else some .nounClass

/-- At each sampled language the recorded categorization system is the one its nominal mapping
predicts: numeral classifiers for Mandarin and Japanese, noun class for French and Italian. -/
theorem sample_matches_prediction :
    ∀ p ∈ [ (Mandarin.classifierKind, Mandarin.Nouns.nominalMapping)
          , (Japanese.classifierKind, Japanese.Nouns.nominalMapping)
          , (French.classifierKind, French.Nouns.nominalMapping)
          , (Italian.classifierKind, Italian.Nouns.nominalMapping) ],
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

/-! ### Bare arguments and type-shift blocking

The determiner inventory of each sampled language decides by the Blocking Principle which
covert shifts it blocks, and with the mapping which bare nominals it admits as arguments
(`NominalMapping.LicensesBare`). -/

/-- A [+arg, −pred] language has no articles and so blocks neither ι nor ∃, and ∩ is never
blocked: all three of Chierchia's shifts are available to Mandarin and Japanese bare nouns. -/
theorem argOnly_blocks_nothing :
    ∀ ds ∈ [Mandarin.Determiners.inventory, Japanese.Determiners.inventory],
      ¬ ds.Blocks .iota ∧ ¬ ds.Blocks .exists := by
  decide

/-- Mandarin and Japanese admit every bare nominal as an argument. -/
theorem argOnly_licensesBare (nt : MassCount) (num : Number) :
    Mandarin.Nouns.nominalMapping.LicensesBare Mandarin.Determiners.inventory nt num ∧
      Japanese.Nouns.nominalMapping.LicensesBare Japanese.Determiners.inventory nt num := by
  simp [NominalMapping.LicensesBare, Mandarin.Nouns.nominalMapping, Japanese.Nouns.nominalMapping]

/-- The [−arg, +pred] languages of the sample have a definite article, so block ι. -/
theorem predOnly_blocks_iota :
    ∀ ds ∈ [French.Determiners.inventory, Italian.Determiners.inventory], ds.Blocks .iota := by
  decide

/-- French and Italian admit no bare nominal as an argument: their nouns need D. -/
theorem predOnly_not_licensesBare (nt : MassCount) (num : Number) :
    ¬ French.Nouns.nominalMapping.LicensesBare French.Determiners.inventory nt num ∧
      ¬ Italian.Nouns.nominalMapping.LicensesBare Italian.Determiners.inventory nt num := by
  simp [NominalMapping.LicensesBare, French.Nouns.nominalMapping, Italian.Nouns.nominalMapping]

/-- English, [+arg, +pred] with *the* and *a* blocking ι and ∃, admits exactly the bare nominals
kind formation is defined for: bare plurals and bare mass nouns, not bare singular count
nouns. -/
theorem english_licensesBare_iff (nt : MassCount) (num : Number) :
    English.Nouns.nominalMapping.LicensesBare English.Determiners.inventory nt num ↔
      DownDefined nt num :=
  NominalMapping.licensesBare_iff_downDefined (by decide) (by decide)

end Chierchia1998
