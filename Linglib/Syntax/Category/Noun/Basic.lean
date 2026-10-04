module

public import Linglib.Syntax.Gender.Basic
public import Linglib.Morphology.Word.Basic

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
it is the gender of its referents. A language with classifiers extends the entry with the
classifiers the noun is counted with, in the language's carrier of classifiers, and a language
that counts some nouns directly and others through a measure word records which class a noun
is in, `MassCount`.

## Main definitions

* `Noun`: the noun entry.
* `ProperName`: the entry of a name, with its natural gender and its `Word` token.
* `GenderedNoun G`: the entry with its controller gender over the carrier `G` and the gender of
  its referents.
* `GenderedNoun.IsNaturalGender`: the gender is the referents', under a labelling of the carrier.
* `ClassifiedNoun C`: the entry with the classifiers it is counted with, over the carrier `C`.
* `MassCount`: the count/mass class of a noun.

## Implementation notes

The general concept takes the plain name and the specializations extend it, as in mathlib. A
fragment's extension is its own `Noun`, in its namespace; a file that opens that namespace
qualifies the name, the root `Noun` being in scope too. A noun that is count in one use and
mass in another, *many seeds* and *much seed*, has an entry for each class.
-/

@[expose] public section

/-- A noun entry records a citation form and a gloss. -/
structure Noun where
  /-- The citation form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  deriving DecidableEq, Repr

/-- A proper name is a noun that names its referent, with the natural gender its pronouns agree
with, where it has one. -/
structure ProperName extends Noun where
  /-- The natural gender, where the name has one. -/
  gender : Option Gender := none
  deriving DecidableEq, Repr

/-- The word token of a name is a third-person `PROPN` with the name's gender. -/
def ProperName.toWord (n : ProperName) : Morphology.Word :=
  { form := n.form, cat := .PROPN
    features := Morphology.Features.of (person := some .third) (gender := n.gender) }

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

/-- A noun with the classifiers it is counted with, over the carrier `C` of the language's
classifiers; empty for a noun counted only through a measure word. -/
structure ClassifiedNoun (C : Type*) extends Noun where
  /-- The classifiers the noun is counted with. -/
  classifiers : Finset C
  deriving DecidableEq

/-- The count/mass class of a noun. A count noun combines with a numeral directly, *three cups*,
and a mass noun only through a measure or container noun, *three cups of milk*. -/
inductive MassCount where
  /-- A mass noun, such as *milk*, *gold* or *furniture*. -/
  | mass
  /-- A count noun, such as *dog* or *cup*. -/
  | count
  deriving DecidableEq, Repr, Fintype
