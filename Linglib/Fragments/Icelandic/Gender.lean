import Linglib.Features.Gender.Basic

/-!
# Icelandic nouns by gender and humanness

The nouns of [adamson-anagnostopoulou-2025]'s Icelandic examples with their grammatical gender
and whether they denote humans, including the fixed-gender neuter *skáld* 'poet'.

## References

* [adamson-anagnostopoulou-2025]
-/

namespace Icelandic.Gender

/-- A noun with its grammatical gender and whether it denotes a human. -/
structure Noun where
  form : String
  gloss : String
  gender : _root_.Gender
  human : Bool
  deriving DecidableEq, Repr

def madur : Noun := ⟨"maður", "man", .masculine, true⟩
def kona : Noun := ⟨"kona", "woman", .feminine, true⟩
def jon : Noun := ⟨"Jón", "Jón", .masculine, true⟩
/-- Fixed-gender human: neuter whatever the referent. -/
def skald : Noun := ⟨"skáld", "poet", .neuter, true⟩
def fraegd : Noun := ⟨"frægð", "fame", .feminine, false⟩
def frami : Noun := ⟨"frami", "success", .masculine, false⟩
def skeid : Noun := ⟨"skeið", "spoon", .feminine, false⟩
def stoll : Noun := ⟨"stóll", "chair", .masculine, false⟩
def epli : Noun := ⟨"epli", "apple", .neuter, false⟩

end Icelandic.Gender
