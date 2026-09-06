import Linglib.Syntax.Category.Noun.Basic

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

instance : HasGender Gender := ⟨λ g => ↑g.toGender⟩

/-- A noun with its gloss and the gender it takes unpossessed. -/
abbrev Noun := GenderedNoun Gender

/-- Gender I nouns. -/
def genderINouns : List Noun :=
  [⟨⟨"moon", "woman"⟩, .gI, false⟩, ⟨⟨"beikoo", "child"⟩, .gI, false⟩,
    ⟨⟨"keusu", "rat"⟩, .gI, false⟩, ⟨⟨"naovana", "bird"⟩, .gI, false⟩,
    ⟨⟨"overe", "coconut"⟩, .gI, false⟩, ⟨⟨"pauna", "banana"⟩, .gI, false⟩,
    ⟨⟨"kepaa", "clay pot"⟩, .gI, false⟩, ⟨⟨"anoo", "peeler (pearl shell)"⟩, .gI, false⟩,
    ⟨⟨"taba'ani", "food"⟩, .gI, false⟩, ⟨⟨"tahii", "sea"⟩, .gI, false⟩,
    ⟨⟨"huan", "rain"⟩, .gI, false⟩, ⟨⟨"uruuru", "love"⟩, .gI, false⟩]

/-- Gender II nouns. -/
def genderIINouns : List Noun :=
  [⟨⟨"paka", "leaf"⟩, .gII, false⟩, ⟨⟨"pus", "stump"⟩, .gII, false⟩,
    ⟨⟨"hinahoo", "taro planting stick"⟩, .gII, false⟩, ⟨⟨"sinivi", "canoe"⟩, .gII, false⟩,
    ⟨⟨"overe", "coconut palm"⟩, .gII, false⟩, ⟨⟨"overe", "banana tree"⟩, .gII, false⟩,
    ⟨⟨"kurita", "octopus"⟩, .gII, false⟩, ⟨⟨"demdem", "snail"⟩, .gII, false⟩,
    ⟨⟨"paku", "feast"⟩, .gII, false⟩, ⟨⟨"suraa", "fire"⟩, .gII, false⟩,
    ⟨⟨"giigii", "shooting star"⟩, .gII, false⟩, ⟨⟨"koara", "language"⟩, .gII, false⟩]

/-- Body-part nouns, gender II unpossessed and gender I with an inalienable possessor. -/
def bodyPartNouns : List Noun :=
  [⟨⟨"bina", "spleen"⟩, .gII, false⟩, ⟨⟨"kuri", "hand"⟩, .gII, false⟩,
    ⟨⟨"iru", "back of head"⟩, .gII, false⟩, ⟨⟨"vuha", "heart"⟩, .gII, false⟩,
    ⟨⟨"ihu", "nose"⟩, .gII, false⟩, ⟨⟨"revasin", "blood"⟩, .gII, false⟩,
    ⟨⟨"hena", "name"⟩, .gII, false⟩, ⟨⟨"moo", "leg"⟩, .gII, false⟩]

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
