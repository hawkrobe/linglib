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

## References

- Kennedy & McNally (2005). Scale structure, degree modification.
- Kennedy (2007). Vagueness and grammar.
-/

import Linglib.Core.Word
import Linglib.Theories.Morphology.Core.Exponence
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
  /-- Scale boundedness (from Kennedy 2007) -/
  scaleType : Boundedness := .open_
  /-- What dimension is being measured? -/
  dimension : String := ""
  /-- Antonym form (if any) -/
  antonymForm : Option String := none
  /-- Antonym relation: contrary (gap) vs contradictory (no gap) -/
  antonymRelation : Option NegationType := none
  /-- Is this a "negative" adjective on its scale? (e.g., "short" vs "tall") -/
  isNegativePole : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- Height Scale: tall, short
-- ============================================================================

def tall : AdjModifierEntry :=
  { form := "tall"
  , formComp := some "taller"
  , formSuper := some "tallest"
  , scaleType := .open_
  , dimension := "height"
  , antonymForm := some "short"
  , antonymRelation := some .contrary }

def short : AdjModifierEntry :=
  { form := "short"
  , formComp := some "shorter"
  , formSuper := some "shortest"
  , scaleType := .open_
  , dimension := "height"
  , antonymForm := some "tall"
  , antonymRelation := some .contrary
  , isNegativePole := true }

-- ============================================================================
-- Happiness Scale: happy, unhappy, sad
-- ============================================================================

def happy : AdjModifierEntry :=
  { form := "happy"
  , formComp := some "happier"
  , formSuper := some "happiest"
  , scaleType := .open_
  , dimension := "happiness"
  , antonymForm := some "unhappy"
  , antonymRelation := some .contrary }

def unhappy : AdjModifierEntry :=
  { form := "unhappy"
  , formComp := some "unhappier"
  , formSuper := some "unhappiest"
  , scaleType := .open_
  , dimension := "happiness"
  , antonymForm := some "happy"
  , antonymRelation := some .contrary
  , isNegativePole := true }

def sad : AdjModifierEntry :=
  { form := "sad"
  , formComp := some "sadder"
  , formSuper := some "saddest"
  , scaleType := .open_
  , dimension := "happiness"
  , antonymForm := some "happy"
  , antonymRelation := some .contrary
  , isNegativePole := true }

-- ============================================================================
-- Price Scale: expensive, cheap
-- ============================================================================

def expensive : AdjModifierEntry :=
  { form := "expensive"
  , formComp := some "more expensive"
  , formSuper := some "most expensive"
  , scaleType := .open_
  , dimension := "price"
  , antonymForm := some "cheap"
  , antonymRelation := some .contrary }

def cheap : AdjModifierEntry :=
  { form := "cheap"
  , formComp := some "cheaper"
  , formSuper := some "cheapest"
  , scaleType := .open_
  , dimension := "price"
  , antonymForm := some "expensive"
  , antonymRelation := some .contrary
  , isNegativePole := true }

-- ============================================================================
-- Quality Scale: good, bad
-- ============================================================================

def good : AdjModifierEntry :=
  { form := "good"
  , formComp := some "better"
  , formSuper := some "best"
  , scaleType := .open_
  , dimension := "quality"
  , antonymForm := some "bad"
  , antonymRelation := some .contrary }

def bad : AdjModifierEntry :=
  { form := "bad"
  , formComp := some "worse"
  , formSuper := some "worst"
  , scaleType := .open_
  , dimension := "quality"
  , antonymForm := some "good"
  , antonymRelation := some .contrary
  , isNegativePole := true }

-- ============================================================================
-- Intelligence Scale
-- ============================================================================

def smart : AdjModifierEntry :=
  { form := "smart"
  , formComp := some "smarter"
  , formSuper := some "smartest"
  , scaleType := .open_
  , dimension := "intelligence"
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
  , dimension := "temperature"
  , antonymForm := some "cold"
  , antonymRelation := some .contrary }

def cold : AdjModifierEntry :=
  { form := "cold"
  , formComp := some "colder"
  , formSuper := some "coldest"
  , scaleType := .open_
  , dimension := "temperature"
  , antonymForm := some "hot"
  , antonymRelation := some .contrary
  , isNegativePole := true }

-- ============================================================================
-- Closed Scale Adjectives (Contradictory Antonyms)
-- ============================================================================

def full : AdjModifierEntry :=
  { form := "full"
  , formComp := some "fuller"
  , formSuper := some "fullest"
  , scaleType := .closed
  , dimension := "fullness"
  , antonymForm := some "empty"
  , antonymRelation := some .contradictory }  -- No gap for closed scales

def empty_ : AdjModifierEntry :=
  { form := "empty"
  , formComp := some "emptier"
  , formSuper := some "emptiest"
  , scaleType := .closed
  , dimension := "fullness"
  , antonymForm := some "full"
  , antonymRelation := some .contradictory
  , isNegativePole := true }

def wet : AdjModifierEntry :=
  { form := "wet"
  , formComp := some "wetter"
  , formSuper := some "wettest"
  , scaleType := .lowerBounded
  , dimension := "wetness"
  , antonymForm := some "dry"
  , antonymRelation := some .contradictory }

def dry : AdjModifierEntry :=
  { form := "dry"
  , formComp := some "drier"
  , formSuper := some "driest"
  , scaleType := .upperBounded
  , dimension := "wetness"
  , antonymForm := some "wet"
  , antonymRelation := some .contradictory
  , isNegativePole := true }

-- ============================================================================
-- Non-Gradable / Absolute Adjectives
-- ============================================================================

def dead : AdjModifierEntry :=
  { form := "dead"
  , scaleType := .closed
  , dimension := "alive" }

def pregnant : AdjModifierEntry :=
  { form := "pregnant"
  , scaleType := .closed }

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
