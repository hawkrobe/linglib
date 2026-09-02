import Linglib.Semantics.Possession.Typology
import Linglib.Data.UD.Basic
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities
import Linglib.Features.Gender.Basic

/-!
# Jarawara possessed nouns

The inalienably possessed nouns of Jarawara (Arawan, Brazil) after Dixon's grammar as tabulated in
[adamson-2024]: their semantic classes with example nouns, the free and possessed forms of nouns
attested in both uses, the possessor pronouns, and the paradigm of *mano* 'arm' whose form
covaries with the person, number, and gender of its possessor. Jarawara has two genders,
masculine and feminine, the latter unmarked; possessed nouns are feminine, and the *mano* ~
*mani* alternation is agreement with the possessor.

## References

* [adamson-2024]
* [dixon-2004]
-/

namespace Jarawara

open Possession

/-- A semantic class of possessed nouns, with its size and example nouns as feminine/masculine
form pairs. -/
structure PossessedNounClass where
  label : String
  memberCount : Nat
  examples : List (String × String)
  /-- The nearest rank on the inalienability hierarchy. -/
  inalienabilityRank : InalienabilityRank
  deriving Repr

/-- Dixon's twelve classes. -/
def classes : List PossessedNounClass :=
  [⟨"Orientation", 17, [("mese/mese", "top surface of"), ("tori/toro", "inside of")],
      .spatialRelation⟩,
    ⟨"Whole and part", 14, [("boni/bono", "whole thing"), ("kote/kote", "piece"),
      ("hoti/hotone", "hole")], .partWhole⟩,
    ⟨"Body parts", 62, [("noki/noko", "eye, face"), ("tame/teme", "foot"),
      ("jifori/jifori", "tail")], .bodyPart⟩,
    ⟨"Parts of plants", 19, [("mowe/mowe", "flower"), ("mati/matone", "cord, rope")],
      .partWhole⟩,
    ⟨"Physical characteristics/properties", 18, [("kakitiri/kakitiri", "itch"),
      ("mahi/maho", "smell")], .culturalItem⟩,
    ⟨"Noise and language", 4, [("moni/moni", "noise"), ("ini/ino", "name")], .culturalItem⟩,
    ⟨"Image and dream", 5, [("hani/hano", "design/picture"), ("watari/watari(ne)", "dream")],
      .culturalItem⟩,
    ⟨"Association", 9, [("tehe/tehene", "something mixed with"),
      ("tase/tesene", "companion of")], .culturalItem⟩,
    ⟨"Containers and other artefacts", 7, [("wije/wijene", "vessel, container"),
      ("atori/atori", "ornament")], .culturalItem⟩,
    ⟨"Water, fire, and light", 11, [("jiji/jifone", "fire, firewood"),
      ("fehe/fehene", "liquid, juice, sap, water")], .culturalItem⟩,
    ⟨"Food", 3, [("tafe/tefe", "food"), ("saharine/saharine", "broth, mush")], .culturalItem⟩,
    ⟨"Place", 6, [("hawi/hawine", "path"), ("tame/temene", "grave")], .spatialRelation⟩]

/-- A noun attested in both free and possessed use, with its glosses. -/
structure FreeVsPossessed where
  free : String
  possessed : String
  gloss : String
  deriving DecidableEq, Repr

/-- Free and possessed forms; all free forms are feminine. -/
def freeVsPossessed : List FreeVsPossessed :=
  [⟨"faha", "fehe/fehe-ne", "water / liquid, juice, sap, water"⟩,
    ⟨"mato", "mati/mato-ne", "cord, rope, vine / cord, rope"⟩,
    ⟨"hawi", "hawi/hawi-ne", "path / path"⟩, ⟨"tona", "tone/tone", "bone / bone"⟩,
    ⟨"neme", "neme/neme", "sky / top part of"⟩, ⟨"bofe", "bofe/bofe", "ground / bottom part of"⟩,
    ⟨"tama", "tame/teme-ne", "grave/hole / grave/hole for"⟩]

/-- Person of a possessor. -/
inductive Person where
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

/-- The two genders. -/
inductive PossGender where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The surface gender of each class. -/
def PossGender.toGender : PossGender → Gender
  | .masc => .masculine
  | .fem => .feminine

/-- A possessor's φ-features; gender is distinguished only in the third person. -/
structure Possessor where
  person : Person
  number : UD.Number
  gender : Option PossGender := none
  deriving DecidableEq, Repr

instance : HasNumber Possessor := ⟨fun p => Number.fromUD p.number⟩

/-- Jarawara's persons in the canonical inventory. -/
def Person.toPerson : Person → _root_.Person
  | .first => .first
  | .second => .second
  | .third => .third

instance : HasPerson Possessor := ⟨fun p => some p.person.toPerson⟩

/-- The possessor pronoun's form and mora count; third-singular pronouns are unpronounced,
and only *o-* and *ti-* fall short of the two-mora minimal word. -/
def Possessor.pronoun : Possessor → Option (String × ℕ)
  | ⟨.first, .Sing, _⟩ => some ("o-", 1)
  | ⟨.second, .Sing, _⟩ => some ("ti-", 1)
  | ⟨.first, .Plur, _⟩ => some ("otaa", 3)
  | ⟨.second, .Plur, _⟩ => some ("tee", 2)
  | ⟨.third, .Plur, _⟩ => some ("mee", 2)
  | ⟨.third, _, _⟩ => none
  | _ => none

/-- The cells of the *mano* paradigm: singular and plural for first, second, third masculine, and
third feminine possessors. -/
def paradigmCells : List Possessor :=
  [⟨.first, .Sing, none⟩, ⟨.second, .Sing, none⟩, ⟨.first, .Plur, none⟩, ⟨.second, .Plur, none⟩,
    ⟨.third, .Sing, some .masc⟩, ⟨.third, .Sing, some .fem⟩, ⟨.third, .Plur, some .masc⟩,
    ⟨.third, .Plur, some .fem⟩]

/-- The two forms of a possessed noun, in Dixon's labels. -/
inductive PossessedForm where
  | mascForm
  | femForm
  deriving DecidableEq, Repr, Fintype

/-- The paradigm of *mano* 'arm': *mano* with first, second, and third masculine singular
possessors, *mani* with third feminine and third plural ones. -/
def manoParadigm : Possessor → PossessedForm
  | ⟨.third, .Sing, some .fem⟩ => .femForm
  | ⟨.third, .Plur, _⟩ => .femForm
  | ⟨.third, .Sing, none⟩ => .femForm
  | _ => .mascForm

/-- The forms of *mano* ~ *mani* and *bako* ~ *baki* 'inside'. -/
def form : PossessedForm → String × String
  | .mascForm => ("mano", "bako")
  | .femForm => ("mani", "baki")

end Jarawara
