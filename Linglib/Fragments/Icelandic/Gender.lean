import Linglib.Syntax.Category.Noun.Basic

/-!
# Icelandic nouns by gender and humanness

The nouns of [adamson-anagnostopoulou-2025]'s Icelandic examples with their grammatical gender
and whether they denote humans, including the fixed-gender neuter *skáld* 'poet'.

## References

* [adamson-anagnostopoulou-2025]
-/

namespace Icelandic.Gender

/-- A noun with its grammatical gender and whether it denotes a human. -/
structure Noun extends GenderedNoun _root_.Gender where
  /-- Whether the noun denotes a human; the natural-gender flag marks the humans whose gender
  is not fixed. -/
  human : Bool
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

def madur : Noun :=
  { form := "maður", gloss := "man", gender := .masculine, isNaturalGender := true, human := true }
def kona : Noun :=
  { form := "kona", gloss := "woman", gender := .feminine, isNaturalGender := true, human := true }
def jon : Noun :=
  { form := "Jón", gloss := "Jón", gender := .masculine, isNaturalGender := true, human := true }
/-- Fixed-gender human: neuter whatever the referent. -/
def skald : Noun := { form := "skáld", gloss := "poet", gender := .neuter, human := true }
def fraegd : Noun := { form := "frægð", gloss := "fame", gender := .feminine, human := false }
def frami : Noun := { form := "frami", gloss := "success", gender := .masculine, human := false }
def skeid : Noun := { form := "skeið", gloss := "spoon", gender := .feminine, human := false }
def stoll : Noun := { form := "stóll", gloss := "chair", gender := .masculine, human := false }
def epli : Noun := { form := "epli", gloss := "apple", gender := .neuter, human := false }

end Icelandic.Gender
