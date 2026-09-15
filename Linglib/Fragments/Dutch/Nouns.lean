import Linglib.Syntax.Category.Noun.Basic
import Linglib.Semantics.Plurality.MassCount
import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Dutch nouns

The Dutch noun as a lexical entry: the root `GenderedNoun` over the common and neuter genders
that *de* and *het* mark, with the mass/count feature and its plural and diminutive where the
entry records them; names are the root `ProperName`. Dutch is [+arg, +pred] like the other
Germanic languages ([chierchia-1998]): with *de*, *het* and *een* blocking the covert ι and ∃,
bare plurals and bare mass nouns are arguments and bare singular count nouns are not. The
entries are the nouns of [le-bruyn-de-swart-2022]'s scrambling data.

## References

* [chierchia-1998]
* [le-bruyn-de-swart-2022]
-/

namespace Dutch.Nouns

open Genericity

/-- A Dutch noun: the root gendered entry with the mass/count feature and its plural and
diminutive where recorded. -/
structure Noun extends GenderedNoun Gender where
  /-- The mass/count feature. -/
  countable : MassCount := .count
  /-- The plural. -/
  plural : Option String := none
  /-- The diminutive. -/
  diminutive : Option String := none
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

/-! ### Count nouns -/

def boek : Noun :=
  { form := "boek", gloss := "book", gender := .neuter, plural := "boeken", diminutive := "boekje" }
def mens : Noun :=
  { form := "mens", gloss := "human", gender := .common, isNaturalGender := true,
    plural := "mensen" }
def geest : Noun := { form := "geest", gloss := "ghost", gender := .common, plural := "geesten" }
def student : Noun :=
  { form := "student", gloss := "student", gender := .common, isNaturalGender := true,
    plural := "studenten" }
def hond : Noun :=
  { form := "hond", gloss := "dog", gender := .common, plural := "honden", diminutive := "hondje" }
def kat : Noun :=
  { form := "kat", gloss := "cat", gender := .common, plural := "katten", diminutive := "katje" }
def film : Noun :=
  { form := "film", gloss := "film", gender := .common, plural := "films", diminutive := "filmpje" }

/-! ### Mass nouns -/

def water : Noun := { form := "water", gloss := "water", gender := .neuter, countable := .mass }
def goud : Noun := { form := "goud", gloss := "gold", gender := .neuter, countable := .mass }
def meel : Noun := { form := "meel", gloss := "flour", gender := .neuter, countable := .mass }

/-! ### Proper names -/

/-- A personal name with its natural gender. -/
private def name (form : String) (gender : Gender) : ProperName :=
  { form, gloss := form, gender := some gender }

def helen : ProperName := name "Helen" .feminine
def jan : ProperName := name "Jan" .masculine
def piet : ProperName := name "Piet" .masculine
def marie : ProperName := name "Marie" .feminine

/-! ### The Nominal Mapping Parameter -/

/-- Dutch is [+arg, +pred], like the other Germanic languages ([chierchia-1998]); its articles
(`Dutch.Determiners.inventory`) block the covert ι and ∃. -/
def nominalMapping : NominalMapping := .argAndPred

end Dutch.Nouns
