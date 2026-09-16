import Linglib.Syntax.Category.Noun.Basic
import Linglib.Syntax.Category.Classifier.Basic
import Linglib.Semantics.Plurality.MassCount
import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# French nouns

The French noun as a lexical entry: the root `GenderedNoun` over the masculine and feminine
genders, with the mass/count feature and its plural; names are the root `ProperName`. French is
[−arg, +pred] ([chierchia-1998]): nouns are predicates and need a determiner
(`French.Determiners.inventory`) to be arguments, so no bare nominal is one. The typological
parameters of the gender system as a classifier device follow the entries.

## References

* [chierchia-1998]
-/

namespace French.Nouns

open Genericity

/-- A French noun: the root gendered entry with the mass/count feature and its plural. -/
structure Noun extends GenderedNoun Gender where
  /-- The mass/count feature. -/
  countable : MassCount := .count
  /-- The plural. -/
  plural : Option String := none
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

/-! ### Count nouns -/

def chien : Noun := { form := "chien", gloss := "dog", gender := .masculine, plural := "chiens" }
def chat : Noun := { form := "chat", gloss := "cat", gender := .masculine, plural := "chats" }
def livre : Noun := { form := "livre", gloss := "book", gender := .masculine, plural := "livres" }
def homme : Noun :=
  { form := "homme", gloss := "man", gender := .masculine, naturalGender := some .masculine,
    plural := "hommes" }
def garcon : Noun :=
  { form := "garçon", gloss := "boy", gender := .masculine, naturalGender := some .masculine,
    plural := "garçons" }
def professeur : Noun :=
  { form := "professeur", gloss := "teacher", gender := .masculine, plural := "professeurs" }
def etudiant : Noun :=
  { form := "étudiant", gloss := "student", gender := .masculine, naturalGender := some .masculine,
    plural := "étudiants" }
def avocat : Noun :=
  { form := "avocat", gloss := "lawyer", gender := .masculine, plural := "avocats" }
def cheval : Noun :=
  { form := "cheval", gloss := "horse", gender := .masculine, plural := "chevaux" }
def fille : Noun :=
  { form := "fille", gloss := "girl", gender := .feminine, naturalGender := some .feminine,
    plural := "filles" }
def femme : Noun :=
  { form := "femme", gloss := "woman", gender := .feminine, naturalGender := some .feminine,
    plural := "femmes" }
def table : Noun := { form := "table", gloss := "table", gender := .feminine, plural := "tables" }
def pomme : Noun := { form := "pomme", gloss := "apple", gender := .feminine, plural := "pommes" }
def fleur : Noun := { form := "fleur", gloss := "flower", gender := .feminine, plural := "fleurs" }

/-! ### Mass nouns -/

def eau : Noun := { form := "eau", gloss := "water", gender := .feminine, countable := .mass }
def vin : Noun := { form := "vin", gloss := "wine", gender := .masculine, countable := .mass }
def pain : Noun := { form := "pain", gloss := "bread", gender := .masculine, countable := .mass }
def lait : Noun := { form := "lait", gloss := "milk", gender := .masculine, countable := .mass }

/-! ### Proper names -/

/-- A personal name with its natural gender. -/
private def name (form : String) (gender : Gender) : ProperName :=
  { form, gloss := form, gender := some gender }

def jean : ProperName := name "Jean" .masculine
def marie : ProperName := name "Marie" .feminine
def pierre : ProperName := name "Pierre" .masculine

/-! ### The Nominal Mapping Parameter -/

/-- French is [−arg, +pred]: nouns are predicates and need D to be arguments
([chierchia-1998]); its articles are `French.Determiners.inventory`. -/
def nominalMapping : NominalMapping := .predOnly

end French.Nouns

/-! ### Typological parameters -/

namespace French

/-- Gender is realized by agreement inside the head-modifier NP; the clause is a further scope. -/
def classifierLocus : Classifier.Scope := .headModifierNP

def classifierConstituent : Classifier.Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
abbrev classifierKind : Option Classifier.Kind :=
  Classifier.kind classifierLocus classifierConstituent

/-- Every environment the device operates in. -/
def classifierScopes : List Classifier.Scope := [.headModifierNP, .predicateArgument]

/-- Semantic core with a morphological residue. -/
def classifierAssignment : Classifier.Assignment := .mixed

/-- Agreement inflection on modifiers; noun classes are never free lexemes. -/
def classifierRealizations : List Classifier.Realization := [.suffix]

def classifierAgreement : Bool := true

def classifierObligatory : Bool := true

/-- Masculine is the unmarked gender. -/
def classifierDefault : Bool := true

def classifierSemantics : List Classifier.Parameter := [.sex, .animacy]

def obligatoryNumber : Bool := true

end French
