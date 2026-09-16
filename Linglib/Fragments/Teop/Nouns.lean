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
  [⟨⟨"moon", "woman"⟩, .gI, none⟩, ⟨⟨"beikoo", "child"⟩, .gI, none⟩,
    ⟨⟨"keusu", "rat"⟩, .gI, none⟩, ⟨⟨"naovana", "bird"⟩, .gI, none⟩,
    ⟨⟨"overe", "coconut"⟩, .gI, none⟩, ⟨⟨"pauna", "banana"⟩, .gI, none⟩,
    ⟨⟨"kepaa", "clay pot"⟩, .gI, none⟩, ⟨⟨"anoo", "peeler (pearl shell)"⟩, .gI, none⟩,
    ⟨⟨"taba'ani", "food"⟩, .gI, none⟩, ⟨⟨"tahii", "sea"⟩, .gI, none⟩,
    ⟨⟨"huan", "rain"⟩, .gI, none⟩, ⟨⟨"uruuru", "love"⟩, .gI, none⟩]

/-- Gender II nouns. -/
def genderIINouns : List Noun :=
  [⟨⟨"paka", "leaf"⟩, .gII, none⟩, ⟨⟨"pus", "stump"⟩, .gII, none⟩,
    ⟨⟨"hinahoo", "taro planting stick"⟩, .gII, none⟩, ⟨⟨"sinivi", "canoe"⟩, .gII, none⟩,
    ⟨⟨"overe", "coconut palm"⟩, .gII, none⟩, ⟨⟨"overe", "banana tree"⟩, .gII, none⟩,
    ⟨⟨"kurita", "octopus"⟩, .gII, none⟩, ⟨⟨"demdem", "snail"⟩, .gII, none⟩,
    ⟨⟨"paku", "feast"⟩, .gII, none⟩, ⟨⟨"suraa", "fire"⟩, .gII, none⟩,
    ⟨⟨"giigii", "shooting star"⟩, .gII, none⟩, ⟨⟨"koara", "language"⟩, .gII, none⟩]

/-- Body-part nouns, gender II unpossessed and gender I with an inalienable possessor. -/
def bodyPartNouns : List Noun :=
  [⟨⟨"bina", "spleen"⟩, .gII, none⟩, ⟨⟨"kuri", "hand"⟩, .gII, none⟩,
    ⟨⟨"iru", "back of head"⟩, .gII, none⟩, ⟨⟨"vuha", "heart"⟩, .gII, none⟩,
    ⟨⟨"ihu", "nose"⟩, .gII, none⟩, ⟨⟨"revasin", "blood"⟩, .gII, none⟩,
    ⟨⟨"hena", "name"⟩, .gII, none⟩, ⟨⟨"moo", "leg"⟩, .gII, none⟩]

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
