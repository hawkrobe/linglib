import Linglib.Features.Gender.Basic

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
structure Noun where
  form : String
  gloss : String
  gender : _root_.Gender
  human : Bool
  deriving DecidableEq, Repr

def andras : Noun := ⟨"andras", "man", .masculine, true⟩
def gineka : Noun := ⟨"gineka", "woman", .feminine, true⟩
def petros : Noun := ⟨"Petros", "Petros", .masculine, true⟩
def maria : Noun := ⟨"Maria", "Maria", .feminine, true⟩
def kleftis : Noun := ⟨"kleftis", "thief", .masculine, true⟩
def giorgos : Noun := ⟨"Giorgos", "Giorgos", .masculine, true⟩
def adherfi : Noun := ⟨"adherfi", "sister", .feminine, true⟩
def mitera : Noun := ⟨"mitera", "mother", .feminine, true⟩
/-- Fixed-gender human: feminine whatever the referent. -/
def megalofiia : Noun := ⟨"megalofiia", "genius", .feminine, true⟩
/-- Fixed-gender human: neuter whatever the referent. -/
def thima : Noun := ⟨"thima", "victim", .neuter, true⟩
def koritsi : Noun := ⟨"koritsi", "girl", .neuter, true⟩
def pinakas : Noun := ⟨"pinakas", "blackboard, painting", .masculine, false⟩
def karekla : Noun := ⟨"karekla", "chair", .feminine, false⟩
def piruni : Noun := ⟨"piruni", "fork", .neuter, false⟩
def kutali : Noun := ⟨"kutali", "spoon", .neuter, false⟩
def fusta : Noun := ⟨"fusta", "skirt", .feminine, false⟩
def bluza : Noun := ⟨"bluza", "T-shirt", .feminine, false⟩
def anaptiras : Noun := ⟨"anaptiras", "lighter", .masculine, false⟩
def fakos : Noun := ⟨"fakos", "torch", .masculine, false⟩
def scholio : Noun := ⟨"scholio", "school", .neuter, false⟩
def ekklisia : Noun := ⟨"ekklisia", "church", .feminine, false⟩
def balkoni : Noun := ⟨"balkoni", "balcony", .neuter, false⟩
def dhiadhromos : Noun := ⟨"dhiadhromos", "corridor", .masculine, false⟩
def daxtilidi : Noun := ⟨"daxtilidi", "ring", .neuter, false⟩
def ombrela : Noun := ⟨"ombrela", "umbrella", .feminine, false⟩
def fotografia : Noun := ⟨"fotografia", "picture", .feminine, false⟩
def pukamiso : Noun := ⟨"pukamiso", "shirt", .neuter, false⟩

end Greek.StandardModern.Gender
