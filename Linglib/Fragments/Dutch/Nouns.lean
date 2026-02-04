import Linglib.Core.Basic
import Linglib.Theories.Montague.Noun.Kind.Chierchia1998

/-!
# Dutch Noun Lexicon Fragment

Dutch-specific noun entries with scrambling support. Dutch allows scrambling:
objects can move across negation/adverbs, affecting bare plural scope.

Based on Le Bruyn & de Swart (2022): scrambled BPs take wide scope but can
still be kind-referring, supporting Krifka (2004) over Chierchia (1998).
-/

namespace Fragments.Dutch.Nouns

open Montague.Noun.Kind.Chierchia1998 (BlockingPrinciple)

/-- A lexical entry for a Dutch noun. -/
structure NounEntry where
  formSg : String
  formPl : Option String := none
  countable : Bool := true
  proper : Bool := false
  formDim : Option String := none
  deriving Repr, BEq

/-- Number marking on a Dutch NP. -/
inductive NPNumber where
  | sg | pl | mass
  deriving DecidableEq, Repr, BEq

/-- Scrambling position in the Dutch middle field. -/
inductive ScramblingPosition where
  | unscrambled
  | scrambled
  deriving DecidableEq, Repr, BEq

/-- A Dutch noun phrase with scrambling information. -/
structure NP where
  noun : NounEntry
  number : NPNumber
  isBare : Bool
  determiner : Option String := none
  position : Option ScramblingPosition := none
  deriving Repr, BEq

def NP.isBarePlural (np : NP) : Bool :=
  np.isBare && np.number == .pl

def NP.isScrambled (np : NP) : Bool :=
  np.position == some .scrambled

def NP.isBareMass (np : NP) : Bool :=
  np.isBare && np.number == .mass

def NP.isBareSingular (np : NP) : Bool :=
  np.isBare && np.number == .sg

def barePlural (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true }

def barePluralScrambled (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true, position := some .scrambled }

def barePluralUnscrambled (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true, position := some .unscrambled }

def bareMass (n : NounEntry) : NP :=
  { noun := n, number := .mass, isBare := true }

def bareSingular (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := true }

def definiteNP (n : NounEntry) (det : String := "de") (num : NPNumber := .sg) : NP :=
  { noun := n, number := num, isBare := false, determiner := some det }

def eenNP (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := false, determiner := some "een" }

/-- Dutch blocking: articles block covert type shifts, bare singulars cannot occur. -/
def dutchBlocking : BlockingPrinciple :=
  { determiners := ["de", "het", "een", "alle", "geen", "sommige"]
  , iotaBlocked := true
  , existsBlocked := true
  , downBlocked := false }

/-- BP scope: unscrambled = narrow, scrambled = wide. -/
def barePluralScope (np : NP) : String :=
  if !np.isBarePlural then "N/A"
  else match np.position with
    | some .scrambled => "wide"
    | some .unscrambled => "narrow"
    | none => "underspecified"

-- Nouns from Le Bruyn & de Swart (2022)
def boek : NounEntry :=
  { formSg := "boek", formPl := some "boeken", formDim := some "boekje" }

def mens : NounEntry :=
  { formSg := "mens", formPl := some "mensen" }

def geest : NounEntry :=
  { formSg := "geest", formPl := some "geesten" }

def student : NounEntry :=
  { formSg := "student", formPl := some "studenten" }

def hond : NounEntry :=
  { formSg := "hond", formPl := some "honden", formDim := some "hondje" }

def kat : NounEntry :=
  { formSg := "kat", formPl := some "katten", formDim := some "katje" }

def film : NounEntry :=
  { formSg := "film", formPl := some "films", formDim := some "filmpje" }

def water : NounEntry :=
  { formSg := "water", formPl := none, countable := false }

def goud : NounEntry :=
  { formSg := "goud", formPl := none, countable := false }

def meel : NounEntry :=
  { formSg := "meel", formPl := none, countable := false }

def helen : NounEntry := { formSg := "Helen", formPl := none, proper := true }
def jan : NounEntry := { formSg := "Jan", formPl := none, proper := true }
def piet : NounEntry := { formSg := "Piet", formPl := none, proper := true }
def marie : NounEntry := { formSg := "Marie", formPl := none, proper := true }

def allNouns : List NounEntry := [
  boek, mens, geest, student, hond, kat, film,
  water, goud, meel,
  helen, jan, piet, marie
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? fun n =>
    n.formSg == form ||
    n.formPl == some form ||
    n.formDim == some form

def barePluralLicensed : Bool := !dutchBlocking.downBlocked
def bareMassLicensed : Bool := !dutchBlocking.downBlocked
def bareSingularLicensed : Bool := !dutchBlocking.iotaBlocked || !dutchBlocking.existsBlocked

example : barePluralLicensed = true := rfl
example : bareMassLicensed = true := rfl
example : bareSingularLicensed = false := rfl

def boekenScrambled : NP := barePluralScrambled boek
def boekenUnscrambled : NP := barePluralUnscrambled boek
def mensenScrambled : NP := barePluralScrambled mens
def geestenUnscrambled : NP := barePluralUnscrambled geest

example : boekenScrambled.isBarePlural = true := rfl
example : boekenScrambled.isScrambled = true := rfl
example : boekenUnscrambled.isScrambled = false := rfl
example : barePluralScope boekenScrambled = "wide" := rfl
example : barePluralScope boekenUnscrambled = "narrow" := rfl

end Fragments.Dutch.Nouns
