import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-! # Italian Noun Lexicon Fragment

Italian NP structure with gender. Bare arguments restricted
(Chierchia 1998 [-arg, +pred]). Italian is the star witness for
Chierchia's `predOnly` parameter: nouns denote predicates and require
a determiner to be argumental.

## Determiner System

Italian has a richer article paradigm than French, with allomorphy
conditioned by gender, number, and phonological context:

- Definite: il/lo/la (sg), i/gli/le (pl)
- Indefinite: un/uno/una (sg only)
- Partitive: del/dello/della (sg mass), dei/degli/delle (pl)

The partitive articles (di + definite article) serve as the obligatory
indefinite plural — Italian has no bare plural arguments.
-/

namespace Fragments.Italian.Nouns

open Semantics.Lexical.Noun.Kind.Chierchia1998 (BlockingPrinciple NominalMapping)

-- ============================================================================
-- § 1: Gender and Number
-- ============================================================================

/-- Grammatical gender (Italian has no neuter). -/
inductive Gender where
  | masc  -- Masculine
  | fem   -- Feminine
  deriving DecidableEq, Repr, BEq

/-- Number -/
inductive Number where
  | sg  -- Singular
  | pl  -- Plural
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: Noun Entry
-- ============================================================================

/-- A lexical entry for an Italian noun. -/
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

-- ============================================================================
-- § 3: Chierchia Parameters
-- ============================================================================

/-- Italian is a [-arg, +pred] language (Chierchia 1998). -/
def italianMapping : NominalMapping := .predOnly

/-- Italian has a rich article system that blocks most bare arguments. -/
def italianBlocking : BlockingPrinciple :=
  { determiners := ["il", "lo", "la", "i", "gli", "le",
                     "un", "uno", "una",
                     "del", "dello", "della", "dei", "degli", "delle"]
  , iotaBlocked := true
  , existsBlocked := true
  , downBlocked := false }

-- ============================================================================
-- § 4: Determiners
-- ============================================================================

/-- Italian determiners (articles). -/
inductive Determiner where
  -- Definite
  | il | lo | la          -- Singular definite
  | i | gli | le          -- Plural definite
  -- Indefinite
  | un | uno | una        -- Singular indefinite
  -- Partitive (di + definite article)
  | del | dello | della   -- Singular partitive (mass)
  | dei | degli | delle   -- Plural partitive
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 5: NP Structure
-- ============================================================================

/-- Italian NP structure. Italian NPs require determiners in argument positions. -/
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

-- ============================================================================
-- § 6: NP Constructors
-- ============================================================================

/-- Create a definite NP (il/lo/la/i/gli/le).
    Uses `il` for masculine singular and `la` for feminine singular
    (the lo/gli allomorphs are phonologically conditioned and not
    modeled here). -/
def defNP (n : NounEntry) (num : Number := .sg) : NP :=
  let det := match num, n.gender with
    | .sg, .masc => Determiner.il
    | .sg, .fem => Determiner.la
    | .pl, .masc => Determiner.i
    | .pl, .fem => Determiner.le
  { noun := n, number := num, isBare := false, determiner := some det }

/-- Create an indefinite singular NP (un/una). -/
def indefNP (n : NounEntry) : NP :=
  let det := match n.gender with
    | .masc => Determiner.un
    | .fem => Determiner.una
  { noun := n, number := .sg, isBare := false, determiner := some det }

/-- Create a partitive NP (del/della for mass, dei/delle for plural). -/
def partNP (n : NounEntry) (num : Number := .sg) : NP :=
  let det := match num, n.gender with
    | .sg, .masc => Determiner.del
    | .sg, .fem => Determiner.della
    | .pl, .masc => Determiner.dei
    | .pl, .fem => Determiner.delle
  { noun := n, number := num, isBare := false, determiner := some det }

/-- Create a bare NP (restricted in Italian). -/
def bareNP (n : NounEntry) (num : Number := .sg) : NP :=
  { noun := n, number := num, isBare := true }

-- ============================================================================
-- § 7: Lexical Entries
-- ============================================================================

-- Count nouns (masculine)
def libro : NounEntry := { formSg := "libro", formPl := some "libri", gender := .masc }
def ragazzo : NounEntry := { formSg := "ragazzo", formPl := some "ragazzi", gender := .masc }
def uomo : NounEntry := { formSg := "uomo", formPl := some "uomini", gender := .masc }
def gatto : NounEntry := { formSg := "gatto", formPl := some "gatti", gender := .masc }
def cane : NounEntry := { formSg := "cane", formPl := some "cani", gender := .masc }
def tavolo : NounEntry := { formSg := "tavolo", formPl := some "tavoli", gender := .masc }

-- Count nouns (feminine)
def ragazza : NounEntry := { formSg := "ragazza", formPl := some "ragazze", gender := .fem }
def donna : NounEntry := { formSg := "donna", formPl := some "donne", gender := .fem }
def casa : NounEntry := { formSg := "casa", formPl := some "case", gender := .fem }

-- Mass nouns
def acqua : NounEntry := { formSg := "acqua", formPl := none, gender := .fem, countable := false }
def vino : NounEntry := { formSg := "vino", formPl := none, gender := .masc, countable := false }
def pane : NounEntry := { formSg := "pane", formPl := none, gender := .masc, countable := false }
def latte : NounEntry := { formSg := "latte", formPl := none, gender := .masc, countable := false }

-- Proper names
def paolo : NounEntry := { formSg := "Paolo", formPl := none, gender := .masc, proper := true }
def maria : NounEntry := { formSg := "Maria", formPl := none, gender := .fem, proper := true }

-- ============================================================================
-- § 8: Lexicon Access
-- ============================================================================

def allNouns : List NounEntry := [
  libro, ragazzo, uomo, gatto, cane, tavolo,
  ragazza, donna, casa,
  acqua, vino, pane, latte,
  paolo, maria
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? λ n => n.formSg == form || n.formPl == some form

-- ============================================================================
-- § 9: Bare Argument Licensing
-- ============================================================================

/-- In Italian, bare plurals are NOT generally licensed. -/
def barePluralLicensed : Bool := false

/-- In Italian, bare singulars are NOT licensed. -/
def bareSingularLicensed : Bool := false

example : barePluralLicensed = false := rfl
example : bareSingularLicensed = false := rfl

-- ============================================================================
-- § 10: NP Examples
-- ============================================================================

/-- "il libro" (the book) -/
def ilLibro : NP := defNP libro

/-- "la ragazza" (the girl) -/
def laRagazza : NP := defNP ragazza

/-- "un gatto" (a cat) -/
def unGatto : NP := indefNP gatto

/-- "del vino" (some wine, partitive) -/
def delVino : NP := partNP vino

/-- "dei libri" (some books, partitive plural) -/
def deiLibri : NP := partNP libro .pl

example : ilLibro.isBare = false := rfl
example : ilLibro.determiner = some .il := rfl
example : laRagazza.determiner = some .la := rfl
example : delVino.determiner = some .del := rfl
example : deiLibri.determiner = some .dei := rfl

end Fragments.Italian.Nouns
