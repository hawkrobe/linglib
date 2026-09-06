import Linglib.Syntax.Category.Noun.Basic

/-!
# Bosnian/Croatian/Serbian nouns by gender and humanness

The nouns of [adamson-anagnostopoulou-2025]'s Bosnian/Croatian/Serbian examples with their
grammatical gender and whether they denote humans; neuter nouns are mass or collective.

## References

* [adamson-anagnostopoulou-2025]
-/

namespace Serbian.Gender

/-- A noun with its grammatical gender and whether it denotes a human. -/
structure Noun extends GenderedNoun _root_.Gender where
  /-- Whether the noun denotes a human; the natural-gender flag marks the humans whose gender
  is not fixed. -/
  human : Bool
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

def muskarac : Noun :=
  { form := "muškarac", gloss := "man", gender := .masculine,
    isNaturalGender := true, human := true }
def zena : Noun :=
  { form := "žena", gloss := "woman", gender := .feminine, isNaturalGender := true, human := true }
def covek : Noun :=
  { form := "čovek", gloss := "person, man", gender := .masculine,
    isNaturalGender := true, human := true }
def znanje : Noun := { form := "znanje", gloss := "knowledge", gender := .neuter, human := false }
def intuicija : Noun :=
  { form := "intuicija", gloss := "intuition", gender := .feminine, human := false }
def selo : Noun := { form := "selo", gloss := "village", gender := .neuter, human := false }
def brdo : Noun := { form := "brdo", gloss := "hill", gender := .neuter, human := false }
def knjiga : Noun := { form := "knjiga", gloss := "book", gender := .feminine, human := false }
def pesak : Noun := { form := "pesak", gloss := "sand", gender := .masculine, human := false }
def mleko : Noun := { form := "mleko", gloss := "milk", gender := .neuter, human := false }

end Serbian.Gender
