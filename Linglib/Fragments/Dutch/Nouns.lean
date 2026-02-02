/-
# Dutch Noun Lexicon Fragment

Dutch-specific noun entries with scrambling support.

## Scrambling and Bare Plural Scope (Le Bruyn & de Swart 2022)

Dutch allows scrambling: objects can move across negation and adverbs.
This affects the scope of bare plurals:

- **Unscrambled**: BP takes narrow scope (like English)
  "Helen praat niet met geesten" = ¬∃ (Helen doesn't talk to ghosts)

- **Scrambled**: BP takes wide scope
  "ik boeken niet heb uitgelezen" = ∃x > ¬ (there are books I didn't finish)

Key finding: Scrambled bare plurals can STILL be kind-referring with
appropriate predicates like "haten" (hate).

## Dutch Nominal Mapping

Dutch is [+arg, +pred] like English:
- Bare plurals OK: "Boeken zijn interessant" (Books are interesting)
- Bare mass nouns OK: "Water is nat" (Water is wet)
- Bare singulars OUT: *"Boek is interessant"

## References

- Le Bruyn, B. & de Swart, H. (2022). Exceptional wide scope of bare nominals.
- de Hoop, H. (1996). Case Configuration and Noun Phrase Interpretation.
- Ruys, E. (2001). Dutch Scrambling and the Strong-Weak Distinction.
- Chierchia, G. (1998). Reference to Kinds Across Languages.
-/

import Linglib.Core.Basic
import Linglib.Theories.Montague.Noun.Kind.Chierchia1998

namespace Fragments.Dutch.Nouns

open Montague.Noun.Kind.Chierchia1998 (BlockingPrinciple)

-- ============================================================================
-- Dutch NP Structure
-- ============================================================================

/-- A lexical entry for a Dutch noun. -/
structure NounEntry where
  /-- Singular form -/
  formSg : String
  /-- Plural form (none for mass nouns) -/
  formPl : Option String := none
  /-- Is this a count noun? -/
  countable : Bool := true
  /-- Is this a proper name? -/
  proper : Bool := false
  /-- Diminutive form (Dutch has productive diminutives) -/
  formDim : Option String := none
  deriving Repr, BEq

/-- Number marking on a Dutch NP -/
inductive NPNumber where
  | sg    -- Singular
  | pl    -- Plural
  | mass  -- Mass (no number distinction)
  deriving DecidableEq, Repr, BEq

/-- Scrambling position in the Dutch middle field -/
inductive ScramblingPosition where
  /-- Base position: object follows negation/adverb -/
  | unscrambled
  /-- Scrambled position: object precedes negation/adverb -/
  | scrambled
  deriving DecidableEq, Repr, BEq

/-- A Dutch noun phrase with scrambling information. -/
structure NP where
  /-- The underlying noun -/
  noun : NounEntry
  /-- Number marking -/
  number : NPNumber
  /-- Is this a bare NP (no determiner)? -/
  isBare : Bool
  /-- The determiner (if not bare) -/
  determiner : Option String := none
  /-- Position in the clause (for objects) -/
  position : Option ScramblingPosition := none
  deriving Repr, BEq

/-- Is this NP a bare plural? -/
def NP.isBarePlural (np : NP) : Bool :=
  np.isBare && np.number == .pl

/-- Is this NP scrambled? -/
def NP.isScrambled (np : NP) : Bool :=
  np.position == some .scrambled

/-- Is this NP a bare mass noun? -/
def NP.isBareMass (np : NP) : Bool :=
  np.isBare && np.number == .mass

/-- Is this NP a bare singular? -/
def NP.isBareSingular (np : NP) : Bool :=
  np.isBare && np.number == .sg

-- ============================================================================
-- NP Constructors
-- ============================================================================

/-- Create a bare plural NP -/
def barePlural (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true }

/-- Create a bare plural NP in scrambled position -/
def barePluralScrambled (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true, position := some .scrambled }

/-- Create a bare plural NP in base (unscrambled) position -/
def barePluralUnscrambled (n : NounEntry) : NP :=
  { noun := n, number := .pl, isBare := true, position := some .unscrambled }

/-- Create a bare mass NP -/
def bareMass (n : NounEntry) : NP :=
  { noun := n, number := .mass, isBare := true }

/-- Create a bare singular NP (ungrammatical in Dutch) -/
def bareSingular (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := true }

/-- Create a definite NP with "de/het" -/
def definiteNP (n : NounEntry) (det : String := "de") (num : NPNumber := .sg) : NP :=
  { noun := n, number := num, isBare := false, determiner := some det }

/-- Create an indefinite singular NP with "een" -/
def eenNP (n : NounEntry) : NP :=
  { noun := n, number := .sg, isBare := false, determiner := some "een" }

-- ============================================================================
-- Dutch Blocking Configuration
-- ============================================================================

/--
Dutch has articles that block covert type shifts (like English):
- "de/het" blocks ι (definite description)
- "een" blocks ∃ for singulars
- Nothing blocks ∩ (kind formation)

Result: bare singulars cannot occur as arguments.
-/
def dutchBlocking : BlockingPrinciple :=
  { determiners := ["de", "het", "een", "alle", "geen", "sommige"]
  , iotaBlocked := true
  , existsBlocked := true
  , downBlocked := false }

-- ============================================================================
-- Scrambling and Scope
-- ============================================================================

/--
The scope of a bare plural depends on its position:
- Unscrambled: narrow scope (∃ below negation/quantifiers)
- Scrambled: wide scope (∃ above negation/quantifiers)

This supports Krifka (2004) over Chierchia (1998).
-/
def barePluralScope (np : NP) : String :=
  if !np.isBarePlural then "N/A"
  else match np.position with
    | some .scrambled => "wide"
    | some .unscrambled => "narrow"
    | none => "underspecified"

-- ============================================================================
-- Nouns from Le Bruyn & de Swart (2022)
-- ============================================================================

/-- "boek/boeken" (book/books) - Example 35 -/
def boek : NounEntry :=
  { formSg := "boek"
  , formPl := some "boeken"
  , formDim := some "boekje" }

/-- "mens/mensen" (person/people) - Example 34 -/
def mens : NounEntry :=
  { formSg := "mens"
  , formPl := some "mensen" }

/-- "geest/geesten" (ghost/ghosts) - Example 33 -/
def geest : NounEntry :=
  { formSg := "geest"
  , formPl := some "geesten" }

/-- "student/studenten" (student/students) -/
def student : NounEntry :=
  { formSg := "student"
  , formPl := some "studenten" }

/-- "hond/honden" (dog/dogs) -/
def hond : NounEntry :=
  { formSg := "hond"
  , formPl := some "honden"
  , formDim := some "hondje" }

/-- "kat/katten" (cat/cats) -/
def kat : NounEntry :=
  { formSg := "kat"
  , formPl := some "katten"
  , formDim := some "katje" }

/-- "film/films" (film/films) -/
def film : NounEntry :=
  { formSg := "film"
  , formPl := some "films"
  , formDim := some "filmpje" }

-- Mass nouns (common neuter "het" nouns)
def water : NounEntry :=
  { formSg := "water", formPl := none, countable := false }

def goud : NounEntry :=
  { formSg := "goud", formPl := none, countable := false }

def meel : NounEntry :=
  { formSg := "meel", formPl := none, countable := false }

-- ============================================================================
-- Proper Names
-- ============================================================================

def helen : NounEntry := { formSg := "Helen", formPl := none, proper := true }
def jan : NounEntry := { formSg := "Jan", formPl := none, proper := true }
def piet : NounEntry := { formSg := "Piet", formPl := none, proper := true }
def marie : NounEntry := { formSg := "Marie", formPl := none, proper := true }

-- ============================================================================
-- Lookup
-- ============================================================================

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

-- ============================================================================
-- Bare Argument Licensing
-- ============================================================================

/-- In Dutch, bare plurals are licensed -/
def barePluralLicensed : Bool := !dutchBlocking.downBlocked

/-- In Dutch, bare mass nouns are licensed -/
def bareMassLicensed : Bool := !dutchBlocking.downBlocked

/-- In Dutch, bare singulars are NOT licensed -/
def bareSingularLicensed : Bool :=
  !dutchBlocking.iotaBlocked || !dutchBlocking.existsBlocked

-- Verify our expectations
example : barePluralLicensed = true := rfl
example : bareMassLicensed = true := rfl
example : bareSingularLicensed = false := rfl

-- ============================================================================
-- Example NPs (from Le Bruyn & de Swart 2022)
-- ============================================================================

/-- "boeken" as scrambled bare plural (wide scope) -/
def boekenScrambled : NP := barePluralScrambled boek

/-- "boeken" as unscrambled bare plural (narrow scope) -/
def boekenUnscrambled : NP := barePluralUnscrambled boek

/-- "mensen" as scrambled bare plural -/
def mensenScrambled : NP := barePluralScrambled mens

/-- "geesten" as unscrambled bare plural -/
def geestenUnscrambled : NP := barePluralUnscrambled geest

-- Verify scrambling properties
example : boekenScrambled.isBarePlural = true := rfl
example : boekenScrambled.isScrambled = true := rfl
example : boekenUnscrambled.isScrambled = false := rfl
example : barePluralScope boekenScrambled = "wide" := rfl
example : barePluralScope boekenUnscrambled = "narrow" := rfl

-- ============================================================================
-- Key Theoretical Distinction
-- ============================================================================

/-!
## Why Scrambled BPs Take Wide Scope

Le Bruyn & de Swart (2022) argue this supports Krifka (2004) over Chierchia (1998):

**Chierchia (1998)**: Bare plurals denote kinds via ∩, with DKP introducing
local existential quantification. This predicts narrow scope ALWAYS.

**Problem**: Scrambled bare plurals take WIDE scope but can still be kind-referring
(with predicates like "haten").

**Krifka (2004)**: Bare plurals undergo ∃-shift, which applies at the surface
position. Scrambling moves the BP, so ∃ takes scope from the higher position.

See `Theories/Comparisons/KindReference.lean` for the formal comparison and
`Phenomena/KindReference/Data.lean` for the empirical patterns.
-/

end Fragments.Dutch.Nouns
