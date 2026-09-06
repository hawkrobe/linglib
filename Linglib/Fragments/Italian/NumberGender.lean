import Linglib.Syntax.Category.Noun.Basic
import Linglib.Syntax.Category.Classifier.Basic

/-!
# Italian plurals in *-a*

The Standard Italian nouns whose plural ends in unstressed *-a* and is feminine although the
singular is masculine, after Maiden and Robustelli's list as given in [adamson-2024], beside
regular plurals in *-i* and *-e* that keep the singular's gender.

## References

* [adamson-2024]
-/

namespace Italian.NumberGender

/-- The plural class by ending: the irregular *-a* plural or the regular *-i* / *-e* one. -/
inductive PluralClass where
  | aPlural
  | regular
  deriving DecidableEq, Repr, Fintype

/-- A noun with its singular form and gender, its plural form and gender, and its plural
class. -/
structure Noun extends GenderedNoun Gender where
  /-- The plural form. -/
  formPl : String
  /-- The gender of the plural. -/
  plGender : Gender
  /-- The plural class. -/
  pluralClass : PluralClass
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

/-- The *-a* plurals. -/
def aPlurals : List Noun :=
  [⟨⟨⟨"braccio", "arm"⟩, .masculine, false⟩, "braccia", .feminine, .aPlural⟩,
    ⟨⟨⟨"budello", "intestine"⟩, .masculine, false⟩, "budella", .feminine, .aPlural⟩,
    ⟨⟨⟨"cervello", "brain"⟩, .masculine, false⟩, "cervella", .feminine, .aPlural⟩,
    ⟨⟨⟨"ciglio", "eyelash"⟩, .masculine, false⟩, "ciglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"corno", "horn"⟩, .masculine, false⟩, "corna", .feminine, .aPlural⟩,
    ⟨⟨⟨"dito", "finger"⟩, .masculine, false⟩, "dita", .feminine, .aPlural⟩,
    ⟨⟨⟨"fondamento", "foundation"⟩, .masculine, false⟩, "fondamenta", .feminine, .aPlural⟩,
    ⟨⟨⟨"ginocchio", "knee"⟩, .masculine, false⟩, "ginocchia", .feminine, .aPlural⟩,
    ⟨⟨⟨"grido", "shout"⟩, .masculine, false⟩, "grida", .feminine, .aPlural⟩,
    ⟨⟨⟨"labbro", "lip"⟩, .masculine, false⟩, "labbra", .feminine, .aPlural⟩,
    ⟨⟨⟨"lenzuolo", "sheet"⟩, .masculine, false⟩, "lenzuola", .feminine, .aPlural⟩,
    ⟨⟨⟨"membro", "limb"⟩, .masculine, false⟩, "membra", .feminine, .aPlural⟩,
    ⟨⟨⟨"miglio", "mile"⟩, .masculine, false⟩, "miglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"muro", "wall"⟩, .masculine, false⟩, "mura", .feminine, .aPlural⟩,
    ⟨⟨⟨"osso", "bone"⟩, .masculine, false⟩, "ossa", .feminine, .aPlural⟩,
    ⟨⟨⟨"paio", "pair"⟩, .masculine, false⟩, "paia", .feminine, .aPlural⟩,
    ⟨⟨⟨"riso", "laugh"⟩, .masculine, false⟩, "risa", .feminine, .aPlural⟩,
    ⟨⟨⟨"sopracciglio", "eyebrow"⟩, .masculine, false⟩, "sopracciglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"strido", "shriek"⟩, .masculine, false⟩, "strida", .feminine, .aPlural⟩,
    ⟨⟨⟨"uovo", "egg"⟩, .masculine, false⟩, "uova", .feminine, .aPlural⟩,
    ⟨⟨⟨"urlo", "howl"⟩, .masculine, false⟩, "urla", .feminine, .aPlural⟩]

/-- Regular plurals. -/
def regulars : List Noun :=
  [⟨⟨⟨"libro", "book"⟩, .masculine, false⟩, "libri", .masculine, .regular⟩,
    ⟨⟨⟨"ragazzo", "boy"⟩, .masculine, true⟩, "ragazzi", .masculine, .regular⟩,
    ⟨⟨⟨"casa", "house"⟩, .feminine, false⟩, "case", .feminine, .regular⟩,
    ⟨⟨⟨"ragazza", "girl"⟩, .feminine, true⟩, "ragazze", .feminine, .regular⟩]

end Italian.NumberGender

/-! ### Typological parameters -/

namespace Italian

/-- Gender is realized by agreement inside the head-modifier NP; the clause is a further scope. -/
def classifierLocus : Classifier.Scope := .headModifierNP

def classifierConstituent : Classifier.Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
abbrev classifierKind : Option Classifier.Kind :=
  Classifier.kind classifierLocus classifierConstituent

/-- Every environment the device operates in. -/
def classifierScopes : List Classifier.Scope := [.headModifierNP, .predicateArgument]

/-- Sex plus the morphological *-o* / *-a* endings. -/
def classifierAssignment : Classifier.Assignment := .mixed

/-- Agreement inflection on modifiers; noun classes are never free lexemes. -/
def classifierRealizations : List Classifier.Realization := [.suffix]

def classifierAgreement : Bool := true

def classifierObligatory : Bool := true

/-- Masculine is the unmarked gender. -/
def classifierDefault : Bool := true

def classifierSemantics : List Classifier.Parameter := [.sex, .animacy]

def obligatoryNumber : Bool := true

end Italian
