import Linglib.Syntax.Category.Noun.Basic
import Linglib.Semantics.Plurality.MassCount
import Linglib.Semantics.Genericity.NominalMappingParameter
import Linglib.Morphology.Word.Basic
import Linglib.Fragments.English.Inflection

/-!
# English nouns

The English noun as a lexical entry: the root `Noun` with the mass/count feature, its lexical
gender where it has one, and its plural where that is not the regular *-s* one, which
`Inflection.lean`'s `suffixS` supplies; names are the root `ProperName`. English nouns have
no grammatical gender; the label recorded for *man*, *woman* and the names is the natural
gender their pronouns agree with. English sets [chierchia-1998]'s Nominal Mapping Parameter to [+arg, +pred], so
nouns denote kinds or predicates: with *the* and *a* blocking the covert ι and ∃, bare plurals
and bare mass nouns are arguments and a bare singular count noun is not
(`Studies/Chierchia1998.lean`).

## Main definitions

* `Noun` — the entry, with `Noun.realize` giving its form at a number
* `Noun.toWordSg`, `Noun.toWord` — the entry as a `Word` token
* `nominalMapping` — the Nominal Mapping Parameter setting

## References

* [chierchia-1998]
* [krifka-2026]
-/

namespace English.Nouns

open Genericity
open Morphology (Word Features)

/-- An English noun: the root entry with the mass/count feature, its lexical gender where it
has one, and its plural where that is not the regular *-s* one. -/
structure Noun extends _root_.Noun where
  /-- The mass/count feature ([krifka-2026]). -/
  countable : MassCount := .count
  /-- The natural gender the noun's pronouns agree with, where it has one. -/
  gender : Option Gender := none
  /-- The plural, where it is not the regular *-s* one. -/
  irregularPlural : Option String := none
  deriving DecidableEq, Repr

/-- A common count noun; English is the metalanguage, so the gloss is the form. -/
def Noun.common (form : String) : Noun := { form, gloss := form }

/-- A mass noun. -/
def Noun.mass (form : String) : Noun := { form, gloss := form, countable := .mass }

/-- The form at a number: the citation form in the singular; in the plural, for a count noun,
the irregular plural where there is one and else the regular *-s* one. -/
def Noun.realize (n : Noun) : Number → Option String
  | .singular => some n.form
  | .plural =>
    if n.countable = .mass then none else some (n.irregularPlural.getD (suffixS n.form))
  | _ => none

/-- The singular as a word token: a `NOUN` with the gender where the entry has one. -/
def Noun.toWordSg (n : Noun) : Word :=
  { form := n.form, cat := .NOUN
    features := Features.of (number := some .singular) (gender := n.gender) }

/-- The entry as a word token at a number, where it has a form there. -/
def Noun.toWord (n : Noun) (num : Number) : Option Word :=
  (n.realize num).map λ form =>
    { n.toWordSg with form, features := Features.of (number := some num) (gender := n.gender) }

theorem Noun.toWord_singular (n : Noun) : n.toWord .singular = some n.toWordSg := rfl

/-! ### Count nouns -/

def pizza : Noun := .common "pizza"
def book : Noun := .common "book"
def cat : Noun := .common "cat"
def dog : Noun := .common "dog"
def girl : Noun := .common "girl"
def boy : Noun := .common "boy"
def ball : Noun := .common "ball"
def table : Noun := .common "table"
def squirrel : Noun := .common "squirrel"
def kitchen : Noun := .common "kitchen"
def story : Noun := .common "story"
def lawyer : Noun := .common "lawyer"
def student : Noun := .common "student"
def teacher : Noun := .common "teacher"
def soldier : Noun := .common "soldier"
def horse : Noun := .common "horse"
def brother : Noun := .common "brother"
def spy : Noun := .common "spy"
def idea : Noun := .common "idea"
def bean : Noun := .common "bean"
def father : Noun := { Noun.common "father" with gender := some .masculine }
def mother : Noun := { Noun.common "mother" with gender := some .feminine }
def man : Noun := { Noun.common "man" with gender := some .masculine, irregularPlural := "men" }
def woman : Noun :=
  { Noun.common "woman" with gender := some .feminine, irregularPlural := "women" }
def fireman : Noun := { Noun.common "fireman" with irregularPlural := "firemen" }
def person : Noun := { Noun.common "person" with irregularPlural := "people" }
def child : Noun := { Noun.common "child" with irregularPlural := "children" }

/-! ### Mass nouns -/

def water : Noun := .mass "water"
def sand : Noun := .mass "sand"
def trash : Noun := .mass "trash"
def furniture : Noun := .mass "furniture"
def rice : Noun := .mass "rice"
def gold : Noun := .mass "gold"
def air : Noun := .mass "air"
def wine : Noun := .mass "wine"
def coffee : Noun := .mass "coffee"
def beer : Noun := .mass "beer"
def milk : Noun := .mass "milk"
def tea : Noun := .mass "tea"

/-! ### Proper names -/

/-- A name glossed by itself. -/
private def name (form : String) (gender : Option Gender := none) : ProperName :=
  { form, gloss := form, gender }

def john : ProperName := name "John" (some .masculine)
def mary : ProperName := name "Mary" (some .feminine)
def bill : ProperName := name "Bill" (some .masculine)
def sue : ProperName := name "Sue" (some .feminine)
def fred : ProperName := name "Fred" (some .masculine)
def sam : ProperName := name "Sam"
def pat : ProperName := name "Pat"

/-! ### The Nominal Mapping Parameter -/

/-- English is [+arg, +pred]: nouns denote kinds or predicates ([chierchia-1998]). -/
def nominalMapping : NominalMapping := .argAndPred

end English.Nouns
