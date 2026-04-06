/-
# Adjective Modifier Lexicon Fragment

Lexical entries for adjectives used as modifiers (attributive position).

## Examples

- "a tall man" — attributive use
- "the taller candidate" — comparative
- "the tallest building" — superlative

## Distinction from Predicative Adjectives

- **This file (Modifiers)**: Attributive uses with morphology (taller, tallest)
- **Predicates/Adjectival.lean**: Predicative uses with degree semantics ("John is tall")

Both share scale type and antonym information, but serve different grammatical functions.

-/

import Linglib.Core.Lexical.Word
import Linglib.Core.PropertyDomain
import Linglib.Theories.Morphology.Core.Exponence
import Linglib.Theories.Morphology.DegreeContainment
import Linglib.Theories.Semantics.Lexical.Adjective.Theory

namespace Fragments.English.Modifiers.Adjectives

open Semantics.Lexical.Adjective (AntonymRelation)
open Core.Scale (Boundedness)
open Semantics.Lexical.Adjective (NegationType)

-- ============================================================================
-- Adjective Modifier Entry Structure
-- ============================================================================

/--
A lexical entry for an adjective modifier.

Includes morphological forms (comparative, superlative) and semantic properties
(scale type, antonym relation).
-/
structure AdjModifierEntry where
  /-- Positive form -/
  form : String
  /-- Comparative form -/
  formComp : Option String := none
  /-- Superlative form -/
  formSuper : Option String := none
  /-- Scale boundedness (from @cite{kennedy-2007}) -/
  scaleType : Boundedness := .open_
  /-- What dimension is being measured? -/
  dimension : Core.Dimension
  /-- Antonym form (if any) -/
  antonymForm : Option String := none
  /-- Antonym relation: contrary (gap) vs contradictory (no gap) -/
  antonymRelation : Option NegationType := none
  /-- Does this adjective select the lower endpoint of its scale?
      E.g., "short" selects the low end of height, "empty" selects the low end
      of fullness. This is scale-endpoint polarity, distinct from evaluative
      polarity (@cite{sassoon-2013}): *empty* is lower-endpoint but evaluatively
      positive (total, max-standard). -/
  isLowerEndpoint : Bool := false
  /-- Suppletive pattern across positive, comparative, and superlative
      grades (@cite{bobaljik-2012}). Default `aaa` = regular (same root
      throughout). Set to `abb` for suppletive entries like *good/better/best*.
      See `DegreeContainment.lean` for pattern definitions and the *ABA
      constraint. -/
  suppletion : Theories.Morphology.DegreeContainment.DegreePattern := ⟨0, 0, 0⟩
  deriving Repr, BEq

-- ============================================================================
-- Height Scale: tall, short
-- ============================================================================

def tall : AdjModifierEntry :=
  { form := "tall"
  , formComp := some "taller"
  , formSuper := some "tallest"
  , scaleType := .open_
  , dimension := .height
  , antonymForm := some "short"
  , antonymRelation := some .contrary }

def short : AdjModifierEntry :=
  { form := "short"
  , formComp := some "shorter"
  , formSuper := some "shortest"
  , scaleType := .open_
  , dimension := .height
  , antonymForm := some "tall"
  , antonymRelation := some .contrary
  , isLowerEndpoint := true }

-- ============================================================================
-- Happiness Scale: happy, unhappy, sad
-- ============================================================================

def happy : AdjModifierEntry :=
  { form := "happy"
  , formComp := some "happier"
  , formSuper := some "happiest"
  , scaleType := .open_
  , dimension := .happiness
  , antonymForm := some "unhappy"
  , antonymRelation := some .contrary }

def unhappy : AdjModifierEntry :=
  { form := "unhappy"
  , formComp := some "unhappier"
  , formSuper := some "unhappiest"
  , scaleType := .open_
  , dimension := .happiness
  , antonymForm := some "happy"
  , antonymRelation := some .contrary
  , isLowerEndpoint := true }

def sad : AdjModifierEntry :=
  { form := "sad"
  , formComp := some "sadder"
  , formSuper := some "saddest"
  , scaleType := .open_
  , dimension := .happiness
  , antonymForm := some "happy"
  , antonymRelation := some .contrary
  , isLowerEndpoint := true }

-- ============================================================================
-- Price Scale: expensive, cheap
-- ============================================================================

def expensive : AdjModifierEntry :=
  { form := "expensive"
  , formComp := some "more expensive"
  , formSuper := some "most expensive"
  , scaleType := .open_
  , dimension := .price
  , antonymForm := some "cheap"
  , antonymRelation := some .contrary }

def cheap : AdjModifierEntry :=
  { form := "cheap"
  , formComp := some "cheaper"
  , formSuper := some "cheapest"
  , scaleType := .open_
  , dimension := .price
  , antonymForm := some "expensive"
  , antonymRelation := some .contrary
  , isLowerEndpoint := true }

-- ============================================================================
-- Value Scale: good, bad (@cite{wolfsdorf-2019}, @cite{beltrama-2025})
-- ============================================================================

def good : AdjModifierEntry :=
  { form := "good"
  , formComp := some "better"
  , formSuper := some "best"
  , scaleType := .lowerBounded
  , dimension := .value
  , antonymForm := some "bad"
  , antonymRelation := some .contrary
  , suppletion := ⟨0, 1, 1⟩ }

def bad : AdjModifierEntry :=
  { form := "bad"
  , formComp := some "worse"
  , formSuper := some "worst"
  , scaleType := .lowerBounded
  , dimension := .value
  , antonymForm := some "good"
  , antonymRelation := some .contrary
  , isLowerEndpoint := true
  , suppletion := ⟨0, 1, 1⟩ }

-- ============================================================================
-- Intelligence Scale
-- ============================================================================

def smart : AdjModifierEntry :=
  { form := "smart"
  , formComp := some "smarter"
  , formSuper := some "smartest"
  , scaleType := .open_
  , dimension := .intelligence
  , antonymForm := some "dumb"
  , antonymRelation := some .contrary }

-- ============================================================================
-- Temperature Scale: hot, cold
-- ============================================================================

def hot : AdjModifierEntry :=
  { form := "hot"
  , formComp := some "hotter"
  , formSuper := some "hottest"
  , scaleType := .open_
  , dimension := .temperature
  , antonymForm := some "cold"
  , antonymRelation := some .contrary }

def cold : AdjModifierEntry :=
  { form := "cold"
  , formComp := some "colder"
  , formSuper := some "coldest"
  , scaleType := .open_
  , dimension := .temperature
  , antonymForm := some "hot"
  , antonymRelation := some .contrary
  , isLowerEndpoint := true }

-- ============================================================================
-- Closed Scale Adjectives (Contradictory Antonyms)
-- ============================================================================

def full : AdjModifierEntry :=
  { form := "full"
  , formComp := some "fuller"
  , formSuper := some "fullest"
  , scaleType := .closed
  , dimension := .fullness
  , antonymForm := some "empty"
  , antonymRelation := some .contradictory }  -- No gap for closed scales

def empty_ : AdjModifierEntry :=
  { form := "empty"
  , formComp := some "emptier"
  , formSuper := some "emptiest"
  , scaleType := .closed
  , dimension := .fullness
  , antonymForm := some "full"
  , antonymRelation := some .contradictory
  , isLowerEndpoint := true }

def wet : AdjModifierEntry :=
  { form := "wet"
  , formComp := some "wetter"
  , formSuper := some "wettest"
  , scaleType := .lowerBounded
  , dimension := .wetness
  , antonymForm := some "dry"
  , antonymRelation := some .contradictory }

def dry : AdjModifierEntry :=
  { form := "dry"
  , formComp := some "drier"
  , formSuper := some "driest"
  , scaleType := .upperBounded
  , dimension := .wetness
  , antonymForm := some "wet"
  , antonymRelation := some .contradictory
  , isLowerEndpoint := true }

-- ============================================================================
-- Non-Gradable / Absolute Adjectives
-- ============================================================================

def dead : AdjModifierEntry :=
  { form := "dead"
  , scaleType := .closed
  , dimension := .alive }

def pregnant : AdjModifierEntry :=
  { form := "pregnant"
  , scaleType := .closed
  , dimension := .pregnancy }

-- ============================================================================
-- Conversion to Word
-- ============================================================================

def AdjModifierEntry.toWord (a : AdjModifierEntry) : Word :=
  { form := a.form, cat := .ADJ, features := {} }

/-- Convert an adjective entry to a morphological stem with its
    comparative/superlative paradigm.

    Periphrastic adjectives (e.g., "expensive" → "more expensive")
    work naturally: the full periphrastic form is stored as the
    irregular form string. -/
def AdjModifierEntry.toStem (a : AdjModifierEntry) (σ : Type) : Core.Morphology.Stem σ :=
  { lemma_ := a.form
  , cat := .ADJ
  , baseFeatures := {}
  , paradigm :=
      (match a.formComp with
       | some comp => [Core.Morphology.Degree.comparativeRule σ (irregularForm := some comp)]
       | none => []) ++
      (match a.formSuper with
       | some super_ => [Core.Morphology.Degree.superlativeRule σ (irregularForm := some super_)]
       | none => []) }

-- ============================================================================
-- All Adjective Modifiers
-- ============================================================================

def allEntries : List AdjModifierEntry := [
  tall, short,
  happy, unhappy, sad,
  expensive, cheap,
  good, bad,
  smart,
  hot, cold,
  full, empty_, wet, dry,
  dead, pregnant
]

def lookup (form : String) : Option AdjModifierEntry :=
  allEntries.find? λ a => a.form == form

end Fragments.English.Modifiers.Adjectives
