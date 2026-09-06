import Linglib.Syntax.Category.Noun.Basic

/-!
# Modern Greek nouns by gender and humanness

The nouns of [adamson-anagnostopoulou-2025]'s Greek examples with their grammatical gender and
whether they denote humans: conceptually gendered humans, fixed-gender humans such as
*megalofiia* 'genius' and *thima* 'victim', and inanimates of all three genders.

## References

* [adamson-anagnostopoulou-2025]
-/

namespace Greek.StandardModern.Gender

/-- A noun with its grammatical gender and whether it denotes a human. -/
structure Noun extends GenderedNoun _root_.Gender where
  /-- Whether the noun denotes a human; the natural-gender flag marks the humans whose gender
  is not fixed. -/
  human : Bool
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

def andras : Noun :=
  { form := "andras", gloss := "man", gender := .masculine, isNaturalGender := true, human := true }
def gineka : Noun :=
  { form := "gineka", gloss := "woman", gender := .feminine,
    isNaturalGender := true, human := true }
def petros : Noun :=
  { form := "Petros", gloss := "Petros", gender := .masculine,
    isNaturalGender := true, human := true }
def maria : Noun :=
  { form := "Maria", gloss := "Maria", gender := .feminine, isNaturalGender := true, human := true }
def kleftis : Noun :=
  { form := "kleftis", gloss := "thief", gender := .masculine,
    isNaturalGender := true, human := true }
def giorgos : Noun :=
  { form := "Giorgos", gloss := "Giorgos", gender := .masculine,
    isNaturalGender := true, human := true }
def adherfi : Noun :=
  { form := "adherfi", gloss := "sister", gender := .feminine,
    isNaturalGender := true, human := true }
def mitera : Noun :=
  { form := "mitera", gloss := "mother", gender := .feminine,
    isNaturalGender := true, human := true }
/-- Fixed-gender human: feminine whatever the referent. -/
def megalofiia : Noun :=
  { form := "megalofiia", gloss := "genius", gender := .feminine, human := true }
/-- Fixed-gender human: neuter whatever the referent. -/
def thima : Noun := { form := "thima", gloss := "victim", gender := .neuter, human := true }
def koritsi : Noun := { form := "koritsi", gloss := "girl", gender := .neuter, human := true }
def pinakas : Noun :=
  { form := "pinakas", gloss := "blackboard, painting", gender := .masculine, human := false }
def karekla : Noun := { form := "karekla", gloss := "chair", gender := .feminine, human := false }
def piruni : Noun := { form := "piruni", gloss := "fork", gender := .neuter, human := false }
def kutali : Noun := { form := "kutali", gloss := "spoon", gender := .neuter, human := false }
def fusta : Noun := { form := "fusta", gloss := "skirt", gender := .feminine, human := false }
def bluza : Noun := { form := "bluza", gloss := "T-shirt", gender := .feminine, human := false }
def anaptiras : Noun :=
  { form := "anaptiras", gloss := "lighter", gender := .masculine, human := false }
def fakos : Noun := { form := "fakos", gloss := "torch", gender := .masculine, human := false }
def scholio : Noun := { form := "scholio", gloss := "school", gender := .neuter, human := false }
def ekklisia : Noun :=
  { form := "ekklisia", gloss := "church", gender := .feminine, human := false }
def balkoni : Noun := { form := "balkoni", gloss := "balcony", gender := .neuter, human := false }
def dhiadhromos : Noun :=
  { form := "dhiadhromos", gloss := "corridor", gender := .masculine, human := false }
def daxtilidi : Noun := { form := "daxtilidi", gloss := "ring", gender := .neuter, human := false }
def ombrela : Noun :=
  { form := "ombrela", gloss := "umbrella", gender := .feminine, human := false }
def fotografia : Noun :=
  { form := "fotografia", gloss := "picture", gender := .feminine, human := false }
def pukamiso : Noun := { form := "pukamiso", gloss := "shirt", gender := .neuter, human := false }

end Greek.StandardModern.Gender
