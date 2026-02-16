import Linglib.Theories.Semantics.Lexical.Adjective.Theory

/-! # Adjectival Predicate Lexicon Fragment

Gradable adjective entries following Kennedy (2007). Scale type, dimension, antonyms.
-/

namespace Fragments.English.Predicates.Adjectival

open TruthConditional.Adjective (AntonymRelation GradableAdjEntry)
open Core.Scale (Boundedness)
open TruthConditional.Adjective (NegationType)


/--
An adjectival predicate entry.

This is an alias for `GradableAdjEntry` from the Theory module, re-exported
here for the Fragments organization.
-/
abbrev AdjectivalPredicateEntry := GradableAdjEntry


/-- "tall" — open scale, contrary to "short" -/
def tall : AdjectivalPredicateEntry where
  form := "tall"
  scaleType := .open_
  dimension := "height"
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "short" — open scale, contrary to "tall" -/
def short : AdjectivalPredicateEntry where
  form := "short"
  scaleType := .open_
  dimension := "height"
  antonymForm := some "tall"
  antonymRelation := some .contrary


/--
"happy" — open scale, contrary to "unhappy"

Note: This is the 1-place adjectival predicate "x is happy".
For the 2-place attitude predicate "x is happy that p", see
`Theories/Montague/Lexicon/Attitudes/Preferential.lean`.
-/
def happy : AdjectivalPredicateEntry where
  form := "happy"
  scaleType := .open_
  dimension := "happiness"
  antonymForm := some "unhappy"
  antonymRelation := some .contrary

/-- "unhappy" — open scale, contrary to "happy" -/
def unhappy : AdjectivalPredicateEntry where
  form := "unhappy"
  scaleType := .open_
  dimension := "happiness"
  antonymForm := some "happy"
  antonymRelation := some .contrary

/-- "sad" — open scale, contrary to "happy" (near-synonym of unhappy) -/
def sad : AdjectivalPredicateEntry where
  form := "sad"
  scaleType := .open_
  dimension := "happiness"
  antonymForm := some "happy"
  antonymRelation := some .contrary


/-- "full" — closed scale, contradictory to "empty" -/
def full : AdjectivalPredicateEntry where
  form := "full"
  scaleType := .closed
  dimension := "fullness"
  antonymForm := some "empty"
  antonymRelation := some .contradictory  -- Closed scales often contradictory

/-- "empty" — closed scale, contradictory to "full" -/
def empty : AdjectivalPredicateEntry where
  form := "empty"
  scaleType := .closed
  dimension := "fullness"
  antonymForm := some "full"
  antonymRelation := some .contradictory


/-- "hot" — open scale, contrary to "cold" -/
def hot : AdjectivalPredicateEntry where
  form := "hot"
  scaleType := .open_
  dimension := "temperature"
  antonymForm := some "cold"
  antonymRelation := some .contrary

/-- "cold" — open scale, contrary to "hot" -/
def cold : AdjectivalPredicateEntry where
  form := "cold"
  scaleType := .open_
  dimension := "temperature"
  antonymForm := some "hot"
  antonymRelation := some .contrary


/-- "expensive" — open scale, contrary to "cheap" -/
def expensive : AdjectivalPredicateEntry where
  form := "expensive"
  scaleType := .open_
  dimension := "cost"
  antonymForm := some "cheap"
  antonymRelation := some .contrary

/-- "cheap" — open scale, contrary to "expensive" -/
def cheap : AdjectivalPredicateEntry where
  form := "cheap"
  scaleType := .open_
  dimension := "cost"
  antonymForm := some "expensive"
  antonymRelation := some .contrary

/-- "wet" — lower-closed scale (minimum at 0) -/
def wet : AdjectivalPredicateEntry where
  form := "wet"
  scaleType := .lowerBounded
  dimension := "wetness"
  antonymForm := some "dry"
  antonymRelation := some .contradictory

/-- "dry" — upper-closed scale (maximum at top) -/
def dry : AdjectivalPredicateEntry where
  form := "dry"
  scaleType := .upperBounded
  dimension := "wetness"
  antonymForm := some "wet"
  antonymRelation := some .contradictory


/-- All adjectival predicate entries -/
def allEntries : List (AdjectivalPredicateEntry) := [
  tall, short,
  happy, unhappy, sad,
  full, empty,
  hot, cold,
  expensive, cheap,
  wet, dry
]

/-- Look up an entry by form -/
def lookup (form : String) : Option (AdjectivalPredicateEntry) :=
  allEntries.find? (·.form == form)

end Fragments.English.Predicates.Adjectival
