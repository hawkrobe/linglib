import Linglib.Syntax.Gender.Basic
import Linglib.Morphology.Word.Basic

/-!
# Noun

The noun as a lexical entry: its citation form and its gloss, everything a noun of any
language carries. A proper name extends the entry with the natural gender its pronouns agree
with, where it has one, and projects as a third-person `PROPN` token; it is its own type rather
than a flag on the noun, since a name has no countability or plural and the syntax projects it
as a different head. A language with gender extends the entry with the controller gender in
its own carrier, the gender the language's assignment rules give the noun, and with the
gender of its referents where they have one, the one facet every system with a semantic core
reads; the facets particular rules read besides, animacy, rationality, declension class or
accent, are the fields of the fragments' further extensions. A noun's gender is natural when
it is the gender of its referents. The general concept takes the
plain name and the specializations extend it, as in mathlib.

## Implementation notes

* A fragment's extension is its own `Noun`, in its namespace; a file that opens that
  namespace qualifies the name, the root `Noun` being in scope too.

## Main declarations

* `Noun` — the noun entry.
* `ProperName` — the entry of a name, with its natural gender and its `Word` token.
* `GenderedNoun G` — the entry with its controller gender over the carrier `G` and the
  gender of its referents
* `GenderedNoun.IsNaturalGender` — the gender is the referents', under a labelling of the
  carrier
-/

/-- A noun entry: citation form and gloss. -/
structure Noun where
  /-- The citation form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  deriving DecidableEq, Repr

/-- A proper name: a noun that names its referent, with the natural gender its pronouns agree
with, where it has one. -/
structure ProperName extends Noun where
  /-- The natural gender, where the name has one. -/
  gender : Option Gender := none
  deriving DecidableEq, Repr

/-- The name as a word token: a third-person `PROPN` with its gender. -/
def ProperName.toWord (n : ProperName) : Morphology.Word :=
  { form := n.form, cat := .PROPN
    features := { person := some .third, gender := n.gender.bind Gender.toUD } }

/-- A noun with its controller gender over the carrier `G` and the gender of its referents,
where they have one. -/
structure GenderedNoun (G : Type*) extends Noun where
  /-- The controller gender, the agreements the noun takes. -/
  gender : G
  /-- The gender of the referents, where they have one. -/
  naturalGender : Option Gender := none
  deriving DecidableEq, Repr

namespace GenderedNoun

variable {G : Type*} (label : G → Gender) (n : GenderedNoun G)

/-- A noun's gender is natural when, under the carrier's comparative labelling, it is the
gender of its referents. -/
def IsNaturalGender : Prop := n.naturalGender = some (label n.gender)

instance : Decidable (n.IsNaturalGender label) := inferInstanceAs (Decidable (_ = _))

end GenderedNoun
