import Linglib.Features.Gender.Basic
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

/-- A noun with its singular and plural forms and genders. -/
structure Noun where
  formSg : String
  formPl : String
  gloss : String
  sgGender : Gender
  plGender : Gender
  pluralClass : PluralClass
  deriving DecidableEq, Repr

/-- The *-a* plurals. -/
def aPlurals : List Noun :=
  [⟨"braccio", "braccia", "arm", .masculine, .feminine, .aPlural⟩,
    ⟨"budello", "budella", "intestine", .masculine, .feminine, .aPlural⟩,
    ⟨"cervello", "cervella", "brain", .masculine, .feminine, .aPlural⟩,
    ⟨"ciglio", "ciglia", "eyelash", .masculine, .feminine, .aPlural⟩,
    ⟨"corno", "corna", "horn", .masculine, .feminine, .aPlural⟩,
    ⟨"dito", "dita", "finger", .masculine, .feminine, .aPlural⟩,
    ⟨"fondamento", "fondamenta", "foundation", .masculine, .feminine, .aPlural⟩,
    ⟨"ginocchio", "ginocchia", "knee", .masculine, .feminine, .aPlural⟩,
    ⟨"grido", "grida", "shout", .masculine, .feminine, .aPlural⟩,
    ⟨"labbro", "labbra", "lip", .masculine, .feminine, .aPlural⟩,
    ⟨"lenzuolo", "lenzuola", "sheet", .masculine, .feminine, .aPlural⟩,
    ⟨"membro", "membra", "limb", .masculine, .feminine, .aPlural⟩,
    ⟨"miglio", "miglia", "mile", .masculine, .feminine, .aPlural⟩,
    ⟨"muro", "mura", "wall", .masculine, .feminine, .aPlural⟩,
    ⟨"osso", "ossa", "bone", .masculine, .feminine, .aPlural⟩,
    ⟨"paio", "paia", "pair", .masculine, .feminine, .aPlural⟩,
    ⟨"riso", "risa", "laugh", .masculine, .feminine, .aPlural⟩,
    ⟨"sopracciglio", "sopracciglia", "eyebrow", .masculine, .feminine, .aPlural⟩,
    ⟨"strido", "strida", "shriek", .masculine, .feminine, .aPlural⟩,
    ⟨"uovo", "uova", "egg", .masculine, .feminine, .aPlural⟩,
    ⟨"urlo", "urla", "howl", .masculine, .feminine, .aPlural⟩]

/-- Regular plurals. -/
def regulars : List Noun :=
  [⟨"libro", "libri", "book", .masculine, .masculine, .regular⟩,
    ⟨"ragazzo", "ragazzi", "boy", .masculine, .masculine, .regular⟩,
    ⟨"casa", "case", "house", .feminine, .feminine, .regular⟩,
    ⟨"ragazza", "ragazze", "girl", .feminine, .feminine, .regular⟩]

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
