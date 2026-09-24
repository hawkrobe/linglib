module

public import Linglib.Semantics.Genericity.NominalMappingParameter
public import Linglib.Fragments.Mandarin.Nouns
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Japanese.Classifiers
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.Romance.French.Determiners
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.English.Determiners

/-!
# Chierchia (1998): Reference to kinds across languages

This file formalizes the typological half of [chierchia-1998]. The Nominal Mapping Parameter sets
whether a language's nouns denote kinds, predicates, or either: Chinese and Japanese are
[+arg, −pred], the Romance languages [−arg, +pred], English and most of Germanic [+arg, +pred]
(`Language.nominalMapping`). In a [+arg, −pred] language every noun is kind-denoting, so its
extension is mass, there is no plural, and a numeral needs a classifier to find a level of
counting; conversely a classifier language must be [+arg, −pred], since otherwise its nouns
could not all be mass-like. The fragments decide which of the sampled languages have
classifiers, and exactly the [+arg, −pred] ones do (`hasClassifiers_iff`). Bare arguments and
covert type-shifting track the same setting: a [+arg, −pred] language has no articles and blocks
no shift, a [−arg] language's articles pre-empt ι, and a [+arg, +pred] language with articles
admits exactly the bare nominals kind formation is defined for, so English has bare plurals and
bare mass nouns but no bare singular count nouns. Each language's blocking is derived from its
determiner inventory by `Determiner.Inventory.Blocks`.

The parameter commits the framework to classifiers that serve the noun rather than the numeral:
`japaneseStrategy` and `mandarinStrategy` record that commitment, and the studies of later
classifier accounts dispute it there rather than in the Fragments.

## Main definitions

* `Language.nominalMapping` — the setting of the parameter in each sampled language
* `japaneseStrategy`, `mandarinStrategy` — the classifier-for-noun commitment

## Main results

* `hasClassifiers_iff` — the classifier languages of the sample are the [+arg, −pred] ones
* `argOnly_blocks_nothing`, `predOnly_blocks_iota` — blocking at the sampled languages
* `english_licensesBare_iff` — English admits exactly the bare nominals ∩ is defined for

## References

* [chierchia-1998]
-/

@[expose] public section

namespace Chierchia1998

open Genericity

/-- The languages the paper discusses. -/
inductive Language where
  | mandarin | japanese | french | italian | english
  deriving DecidableEq, Fintype

namespace Language

/-- The setting of the Nominal Mapping Parameter: Chinese and Japanese are [+arg, −pred], French
and Italian [−arg, +pred], English [+arg, +pred]. -/
def nominalMapping : Language → NominalMapping
  | mandarin | japanese => .argOnly
  | french | italian => .predOnly
  | english => .argAndPred

/-- The determiner inventory of the language's fragment. -/
def determiners : Language → Determiner.Inventory
  | mandarin => Mandarin.Determiners.inventory
  | japanese => Japanese.Determiners.inventory
  | french => French.Determiners.inventory
  | italian => Italian.Determiners.inventory
  | english => English.Determiners.inventory

/-- The language has numeral classifiers, as its fragment records for Mandarin and Japanese; the
Romance languages and English have none. -/
def HasClassifiers : Language → Prop
  | mandarin => Mandarin.Classifiers.classifiers.Nonempty
  | japanese => Japanese.Classifiers.classifiers.Nonempty
  | french | italian | english => False

end Language

open Language

/-- A [+arg, −pred] language has a generalized classifier system, and a classifier language must
be [+arg, −pred]: the classifier languages of the sample are exactly the [+arg, −pred] ones. -/
theorem hasClassifiers_iff : ∀ l : Language, l.HasClassifiers ↔ l.nominalMapping = .argOnly
  | .mandarin =>
    iff_of_true ⟨Mandarin.Classifiers.ge, by simp [Mandarin.Classifiers.classifiers]⟩ rfl
  | .japanese =>
    iff_of_true ⟨Japanese.Classifiers.tsu, by simp [Japanese.Classifiers.classifiers]⟩ rfl
  | .french | .italian | .english => iff_of_false id (by decide)

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
    ∀ l : Language, l.nominalMapping = .argOnly →
      ¬ l.determiners.Blocks .iota ∧ ¬ l.determiners.Blocks .exists := by
  decide

/-- Mandarin and Japanese admit every bare nominal as an argument. -/
theorem argOnly_licensesBare (nt : MassCount) (num : Number) :
    (nominalMapping .mandarin).LicensesBare (determiners .mandarin) nt num ∧
      (nominalMapping .japanese).LicensesBare (determiners .japanese) nt num := by
  simp [NominalMapping.LicensesBare, nominalMapping]

/-- The [−arg, +pred] languages of the sample have a definite article, so block ι. -/
theorem predOnly_blocks_iota :
    ∀ l : Language, l.nominalMapping = .predOnly → l.determiners.Blocks .iota := by
  decide

/-- French and Italian admit no bare nominal as an argument: their nouns need D. -/
theorem predOnly_not_licensesBare (nt : MassCount) (num : Number) :
    ¬ (nominalMapping .french).LicensesBare (determiners .french) nt num ∧
      ¬ (nominalMapping .italian).LicensesBare (determiners .italian) nt num := by
  simp [NominalMapping.LicensesBare, nominalMapping]

/-- English, [+arg, +pred] with *the* and *a* blocking ι and ∃, admits exactly the bare nominals
kind formation is defined for: bare plurals and bare mass nouns, not bare singular count
nouns. -/
theorem english_licensesBare_iff (nt : MassCount) (num : Number) :
    (nominalMapping .english).LicensesBare (determiners .english) nt num ↔ DownDefined nt num :=
  NominalMapping.licensesBare_iff_downDefined (by decide) (by decide)

end Chierchia1998
