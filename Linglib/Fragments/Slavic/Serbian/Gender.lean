module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Bosnian/Croatian/Serbian nouns by gender and humanness

This file gives the nouns of [adamson-anagnostopoulou-2025]'s Bosnian/Croatian/Serbian examples,
each with its grammatical gender and whether it denotes humans: the conjuncts of their examples of
resolved agreement, *muškarac i žena* 'the man and the woman', *znanje i intuicija* 'knowledge and
intuition' and *selo i brdo* 'village and hill' ((68)–(70)), and the nouns of their Table 1,
*žena*, *čovek*, *mleko*, *knjiga* and *pesak*. Their analysis of the neuter as a mass gender is in
`Studies/AdamsonAnagnostopoulou2025.lean`.

## References

* [adamson-anagnostopoulou-2025]
-/

@[expose] public section

namespace Serbian.Gender

/-- A noun with its grammatical gender and whether it denotes a human. -/
structure Noun extends GenderedNoun _root_.Gender where
  /-- Whether the noun denotes humans. -/
  human : Bool
  deriving DecidableEq, Repr

/-- *muškarac* 'man'. -/
def muskarac : Noun :=
  { form := "muškarac", gloss := "man", gender := .masculine,
    naturalGender := some .masculine, human := true }

/-- *žena* 'woman'. -/
def zena : Noun :=
  { form := "žena", gloss := "woman", gender := .feminine,
    naturalGender := some .feminine, human := true }

/-- *čovek* 'person, man'. -/
def covek : Noun :=
  { form := "čovek", gloss := "person, man", gender := .masculine,
    naturalGender := some .masculine, human := true }

/-- *znanje* 'knowledge'. -/
def znanje : Noun := { form := "znanje", gloss := "knowledge", gender := .neuter, human := false }

/-- *intuicija* 'intuition'. -/
def intuicija : Noun :=
  { form := "intuicija", gloss := "intuition", gender := .feminine, human := false }

/-- *selo* 'village'. -/
def selo : Noun := { form := "selo", gloss := "village", gender := .neuter, human := false }

/-- *brdo* 'hill'. -/
def brdo : Noun := { form := "brdo", gloss := "hill", gender := .neuter, human := false }

/-- *knjiga* 'book'. -/
def knjiga : Noun := { form := "knjiga", gloss := "book", gender := .feminine, human := false }

/-- *pesak* 'sand'. -/
def pesak : Noun := { form := "pesak", gloss := "sand", gender := .masculine, human := false }

/-- *mleko* 'milk'. -/
def mleko : Noun := { form := "mleko", gloss := "milk", gender := .neuter, human := false }

end Serbian.Gender
