import Linglib.Core.Basic
import Linglib.Theories.Montague.Noun.Kind.Chierchia1998

/-! # French Noun Lexicon Fragment

French NP structure with gender. Bare arguments restricted (Chierchia 1998 [-arg, +pred]).
-/

namespace Fragments.French.Nouns

open Montague.Noun.Kind.Chierchia1998 (BlockingPrinciple NominalMapping)


/-- Grammatical gender -/
inductive Gender where
  | masc  -- Masculine
  | fem   -- Feminine
  deriving DecidableEq, Repr, BEq

/-- Number -/
inductive Number where
  | sg  -- Singular
  | pl  -- Plural
  deriving DecidableEq, Repr, BEq

/--
A lexical entry for a French noun.

French nouns have grammatical gender.
-/
structure NounEntry where
  /-- Singular form -/
  formSg : String
  /-- Plural form -/
  formPl : Option String := none
  /-- Grammatical gender -/
  gender : Gender
  /-- Is this a count noun? -/
  countable : Bool := true
  /-- Is this a proper name? -/
  proper : Bool := false
  deriving Repr, BEq

/-- French determiners -/
inductive Determiner where
  | le | la | les          -- Definite (the)
  | un | une               -- Indefinite singular (a)
  | des                    -- Indefinite plural (some)
  | du | dela              -- Partitive (some, for mass)
  deriving DecidableEq, Repr, BEq

/--
French NP structure.

French NPs require determiners in most contexts.
-/
structure NP where
  /-- The underlying noun -/
  noun : NounEntry
  /-- Number -/
  number : Number
  /-- Is this a bare NP (no determiner)? -/
  isBare : Bool
  /-- The determiner (if not bare) -/
  determiner : Option Determiner := none
  deriving Repr, BEq


/--
French has a rich article system that blocks most bare arguments.
-/
def frenchBlocking : BlockingPrinciple :=
  { determiners := ["le", "la", "les", "un", "une", "des", "du", "de la"]
  , iotaBlocked := true
  , existsBlocked := true  -- Even for plurals!
  , downBlocked := false }

/-- French is a [-arg, +pred] language -/
def frenchMapping : NominalMapping := .predOnly


/-- Create a definite NP (le/la/les) -/
def defNP (n : NounEntry) (num : Number := .sg) : NP :=
  let det := match num, n.gender with
    | .sg, .masc => Determiner.le
    | .sg, .fem => Determiner.la
    | .pl, _ => Determiner.les
  { noun := n, number := num, isBare := false, determiner := some det }

/-- Create an indefinite singular NP (un/une) -/
def indefNP (n : NounEntry) : NP :=
  let det := match n.gender with
    | .masc => Determiner.un
    | .fem => Determiner.une
  { noun := n, number := .sg, isBare := false, determiner := some det }

/-- Create an indefinite plural NP (des) -/
def desNP (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := false, determiner := some .des }

/-- Create a partitive NP (du/de la) for mass nouns -/
def partNP (n : NounEntry) : NP :=
  let det := match n.gender with
    | .masc => Determiner.du
    | .fem => Determiner.dela
  { noun := n, number := .sg, isBare := false, determiner := some det }

/-- Create a bare NP (restricted in French) -/
def bareNP (n : NounEntry) (num : Number := .sg) : NP :=
  { noun := n, number := num, isBare := true }


def chien : NounEntry := { formSg := "chien", formPl := some "chiens", gender := .masc }
def chat : NounEntry := { formSg := "chat", formPl := some "chats", gender := .masc }
def livre : NounEntry := { formSg := "livre", formPl := some "livres", gender := .masc }
def homme : NounEntry := { formSg := "homme", formPl := some "hommes", gender := .masc }
def garcon : NounEntry := { formSg := "garçon", formPl := some "garçons", gender := .masc }
def professeur : NounEntry := { formSg := "professeur", formPl := some "professeurs", gender := .masc }
def etudiant : NounEntry := { formSg := "étudiant", formPl := some "étudiants", gender := .masc }
def avocat : NounEntry := { formSg := "avocat", formPl := some "avocats", gender := .masc }
def cheval : NounEntry := { formSg := "cheval", formPl := some "chevaux", gender := .masc }

def fille : NounEntry := { formSg := "fille", formPl := some "filles", gender := .fem }
def femme : NounEntry := { formSg := "femme", formPl := some "femmes", gender := .fem }
def table : NounEntry := { formSg := "table", formPl := some "tables", gender := .fem }
def pomme : NounEntry := { formSg := "pomme", formPl := some "pommes", gender := .fem }
def fleur : NounEntry := { formSg := "fleur", formPl := some "fleurs", gender := .fem }

def eau : NounEntry := { formSg := "eau", formPl := none, gender := .fem, countable := false }
def vin : NounEntry := { formSg := "vin", formPl := none, gender := .masc, countable := false }
def pain : NounEntry := { formSg := "pain", formPl := none, gender := .masc, countable := false }
def lait : NounEntry := { formSg := "lait", formPl := none, gender := .masc, countable := false }


def jean : NounEntry := { formSg := "Jean", formPl := none, gender := .masc, proper := true }
def marie : NounEntry := { formSg := "Marie", formPl := none, gender := .fem, proper := true }
def pierre : NounEntry := { formSg := "Pierre", formPl := none, gender := .masc, proper := true }


def allNouns : List NounEntry := [
  chien, chat, livre, homme, garcon, professeur, etudiant, avocat, cheval,
  fille, femme, table, pomme, fleur,
  eau, vin, pain, lait,
  jean, marie, pierre
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? λ n => n.formSg == form || n.formPl == some form


/-- In French, bare plurals are NOT generally licensed -/
def barePluralLicensed : Bool := false

/-- In French, bare singulars are NOT licensed -/
def bareSingularLicensed : Bool := false

-- Verify
example : barePluralLicensed = false := rfl
example : bareSingularLicensed = false := rfl


/-- "le chien" (the dog) -/
def leChien : NP := defNP chien

/-- "les chiens" (the dogs) -/
def lesChiens : NP := defNP chien .pl

/-- "un chien" (a dog) -/
def unChien : NP := indefNP chien

/-- "des pommes" (some apples) - required where English uses bare plural -/
def desPommes : NP := desNP pomme

/-- "du vin" (some wine) - partitive -/
def duVin : NP := partNP vin

example : leChien.isBare = false := rfl
example : leChien.determiner = some .le := rfl
example : desPommes.determiner = some .des := rfl

end Fragments.French.Nouns
