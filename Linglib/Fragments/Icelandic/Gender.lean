module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Icelandic nouns by gender and humanness

Icelandic has three genders, the masculine, the feminine and the neuter, and the gender of a
noun is only indirectly related to the sex of its referents: most nouns for women are feminine,
but *skáld* 'poet' is neuter whoever the poet, as Thráinsson's overview of the nominal
inflection notes. The entries are the nouns of [adamson-anagnostopoulou-2025]'s Icelandic
examples, each with its grammatical gender, the gender of its referents where they have one, and
whether it denotes a human.

## Main definitions

* `Icelandic.Gender.Noun`: a noun with its gender and whether it denotes a human.

## References

* [adamson-anagnostopoulou-2025]
* [thrainsson-2007]
-/

@[expose] public section

namespace Icelandic.Gender

/-- A noun with its grammatical gender and whether it denotes a human. -/
structure Noun extends GenderedNoun _root_.Gender where
  /-- Whether the noun denotes a human; the natural-gender flag marks the humans whose gender
  is not fixed. -/
  human : Bool
  deriving DecidableEq, Repr

/-- *maður* 'man', masculine. -/
def madur : Noun :=
  { form := "maður", gloss := "man", gender := .masculine,
    naturalGender := some .masculine, human := true }

/-- *kona* 'woman', feminine. -/
def kona : Noun :=
  { form := "kona", gloss := "woman", gender := .feminine,
    naturalGender := some .feminine, human := true }

/-- *Jón*, a man's name, masculine. -/
def jon : Noun :=
  { form := "Jón", gloss := "Jón", gender := .masculine,
    naturalGender := some .masculine, human := true }

/-- *skáld* 'poet', neuter whatever the sex of the poet. -/
def skald : Noun := { form := "skáld", gloss := "poet", gender := .neuter, human := true }

/-- *frægð* 'fame', feminine. -/
def fraegd : Noun := { form := "frægð", gloss := "fame", gender := .feminine, human := false }

/-- *frami* 'success', masculine. -/
def frami : Noun := { form := "frami", gloss := "success", gender := .masculine, human := false }

/-- *skeið* 'spoon', feminine. -/
def skeid : Noun := { form := "skeið", gloss := "spoon", gender := .feminine, human := false }

/-- *stóll* 'chair', masculine. -/
def stoll : Noun := { form := "stóll", gloss := "chair", gender := .masculine, human := false }

/-- *epli* 'apple', neuter. -/
def epli : Noun := { form := "epli", gloss := "apple", gender := .neuter, human := false }

end Icelandic.Gender
