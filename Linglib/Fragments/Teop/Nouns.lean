import Linglib.Features.Gender.Basic

/-!
# Teop nouns

Gender I and gender II nouns of Teop (Oceanic, Bougainville), sampled from Mosel and Spriggs's
grammar sketch as tabulated in [adamson-2024], with the body-part and kinship nouns whose gender
alternates with inalienable possession, and the article paradigm by gender, number, and proprial
class. Gender I is the animate class; gender II the inanimate one; the proprial article marks
names, kinship terms, and other socially prominent nouns.

## References

* [adamson-2024]
-/

namespace Teop

/-- The two genders, distinguished by article agreement. -/
inductive Gender where
  | gI
  | gII
  deriving DecidableEq, Repr, Fintype

/-- The surface gender of each class. -/
def Gender.toGender : Gender → _root_.Gender
  | .gI => .animate
  | .gII => .inanimate

/-- A noun with its gloss and the gender it takes unpossessed. -/
structure Noun where
  form : String
  gloss : String
  gender : Gender
  deriving DecidableEq, Repr

/-- Gender I nouns. -/
def genderINouns : List Noun :=
  [⟨"moon", "woman", .gI⟩, ⟨"beikoo", "child", .gI⟩, ⟨"keusu", "rat", .gI⟩,
    ⟨"naovana", "bird", .gI⟩, ⟨"overe", "coconut", .gI⟩, ⟨"pauna", "banana", .gI⟩,
    ⟨"kepaa", "clay pot", .gI⟩, ⟨"anoo", "peeler (pearl shell)", .gI⟩,
    ⟨"taba'ani", "food", .gI⟩, ⟨"tahii", "sea", .gI⟩, ⟨"huan", "rain", .gI⟩,
    ⟨"uruuru", "love", .gI⟩]

/-- Gender II nouns. -/
def genderIINouns : List Noun :=
  [⟨"paka", "leaf", .gII⟩, ⟨"pus", "stump", .gII⟩, ⟨"hinahoo", "taro planting stick", .gII⟩,
    ⟨"sinivi", "canoe", .gII⟩, ⟨"overe", "coconut palm", .gII⟩, ⟨"overe", "banana tree", .gII⟩,
    ⟨"kurita", "octopus", .gII⟩, ⟨"demdem", "snail", .gII⟩, ⟨"paku", "feast", .gII⟩,
    ⟨"suraa", "fire", .gII⟩, ⟨"giigii", "shooting star", .gII⟩, ⟨"koara", "language", .gII⟩]

/-- Body-part nouns, gender II unpossessed and gender I with an inalienable possessor. -/
def bodyPartNouns : List Noun :=
  [⟨"bina", "spleen", .gII⟩, ⟨"kuri", "hand", .gII⟩, ⟨"iru", "back of head", .gII⟩,
    ⟨"vuha", "heart", .gII⟩, ⟨"ihu", "nose", .gII⟩, ⟨"revasin", "blood", .gII⟩,
    ⟨"hena", "name", .gII⟩, ⟨"moo", "leg", .gII⟩]

/-- Body-part nouns whose unpossessed form carries the suffix *-na*. -/
def derelationalized : List String := ["moo-na", "kuri-na", "ihu-na"]

/-- The features the prenominal article agrees in. -/
structure ArticleCtx where
  gender : Gender
  plural : Bool
  proprial : Bool := false
  deriving DecidableEq, Repr, Fintype

/-- The article paradigm: gender I *a* ~ *o*, gender II *o* ~ *a*, and the proprial *e* in the
singular, neutralized in the plural. -/
def articleForm : ArticleCtx → String
  | ⟨.gI, false, true⟩ => "e"
  | ⟨.gI, false, false⟩ => "a"
  | ⟨.gI, true, _⟩ => "o"
  | ⟨.gII, false, _⟩ => "o"
  | ⟨.gII, true, _⟩ => "a"

end Teop
