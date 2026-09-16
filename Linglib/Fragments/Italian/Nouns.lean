import Linglib.Syntax.Category.Noun.Basic
import Linglib.Semantics.Plurality.MassCount
import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Italian nouns

The Italian noun as a lexical entry: the root `GenderedNoun` over the masculine and feminine
genders, with the mass/count feature and its plural; names are the root `ProperName`. Italian is
[−arg, +pred] ([chierchia-1998]): nouns are predicates and need a determiner
(`Italian.Determiners.inventory`) to be arguments, so no bare nominal is one; the definite
plural denotes a kind and the bare plural, where licensed, a property
(`Studies/Guerrini2026.lean`). The plurals in *-a* that change gender are
`Italian.NumberGender`.

## References

* [chierchia-1998]
-/

namespace Italian.Nouns

open Genericity

/-- An Italian noun: the root gendered entry with the mass/count feature and its plural. -/
structure Noun extends GenderedNoun Gender where
  /-- The mass/count feature. -/
  countable : MassCount := .count
  /-- The plural. -/
  plural : Option String := none
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

/-! ### Count nouns -/

def libro : Noun := { form := "libro", gloss := "book", gender := .masculine, plural := "libri" }
def ragazzo : Noun :=
  { form := "ragazzo", gloss := "boy", gender := .masculine, naturalGender := some .masculine,
    plural := "ragazzi" }
def uomo : Noun :=
  { form := "uomo", gloss := "man", gender := .masculine, naturalGender := some .masculine,
    plural := "uomini" }
def gatto : Noun := { form := "gatto", gloss := "cat", gender := .masculine, plural := "gatti" }
def cane : Noun := { form := "cane", gloss := "dog", gender := .masculine, plural := "cani" }
def tavolo : Noun :=
  { form := "tavolo", gloss := "table", gender := .masculine, plural := "tavoli" }
def ragazza : Noun :=
  { form := "ragazza", gloss := "girl", gender := .feminine, naturalGender := some .feminine,
    plural := "ragazze" }
def donna : Noun :=
  { form := "donna", gloss := "woman", gender := .feminine, naturalGender := some .feminine,
    plural := "donne" }
def casa : Noun := { form := "casa", gloss := "house", gender := .feminine, plural := "case" }

/-! ### Mass nouns -/

def acqua : Noun := { form := "acqua", gloss := "water", gender := .feminine, countable := .mass }
def vino : Noun := { form := "vino", gloss := "wine", gender := .masculine, countable := .mass }
def pane : Noun := { form := "pane", gloss := "bread", gender := .masculine, countable := .mass }
def latte : Noun := { form := "latte", gloss := "milk", gender := .masculine, countable := .mass }

/-! ### Proper names -/

/-- A personal name with its natural gender. -/
private def name (form : String) (gender : Gender) : ProperName :=
  { form, gloss := form, gender := some gender }

def paolo : ProperName := name "Paolo" .masculine
def maria : ProperName := name "Maria" .feminine

/-! ### The Nominal Mapping Parameter -/

/-- Italian is [−arg, +pred]: nouns are predicates and need D to be arguments
([chierchia-1998]); its articles are `Italian.Determiners.inventory`. -/
def nominalMapping : NominalMapping := .predOnly

end Italian.Nouns
