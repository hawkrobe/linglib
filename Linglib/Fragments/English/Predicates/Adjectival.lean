import Linglib.Theories.Montague.Adjective.Theory

/-! # Adjectival Predicate Lexicon Fragment

Gradable adjective entries following Kennedy (2007). Scale type, dimension, antonyms.
-/

namespace Fragments.English.Predicates.Adjectival

open Montague.Adjective (ScaleType AntonymRelation GradableAdjEntry)
open Montague.Domain.Degrees (NegationType)


/--
An adjectival predicate entry.

This is an alias for `GradableAdjEntry` from the Theory module, re-exported
here for the Fragments organization.

The `max` parameter is the scale maximum (for finite degree representations).
-/
abbrev AdjectivalPredicateEntry := GradableAdjEntry


/-- "tall" — open scale, contrary to "short" -/
def tall : AdjectivalPredicateEntry 10 where
  form := "tall"
  scaleType := .open_
  dimension := "height"
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "short" — open scale, contrary to "tall" -/
def short : AdjectivalPredicateEntry 10 where
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
def happy : AdjectivalPredicateEntry 10 where
  form := "happy"
  scaleType := .open_
  dimension := "happiness"
  antonymForm := some "unhappy"
  antonymRelation := some .contrary

/-- "unhappy" — open scale, contrary to "happy" -/
def unhappy : AdjectivalPredicateEntry 10 where
  form := "unhappy"
  scaleType := .open_
  dimension := "happiness"
  antonymForm := some "happy"
  antonymRelation := some .contrary

/-- "sad" — open scale, contrary to "happy" (near-synonym of unhappy) -/
def sad : AdjectivalPredicateEntry 10 where
  form := "sad"
  scaleType := .open_
  dimension := "happiness"
  antonymForm := some "happy"
  antonymRelation := some .contrary


/-- "full" — closed scale, contradictory to "empty" -/
def full : AdjectivalPredicateEntry 10 where
  form := "full"
  scaleType := .closed
  dimension := "fullness"
  antonymForm := some "empty"
  antonymRelation := some .contradictory  -- Closed scales often contradictory

/-- "empty" — closed scale, contradictory to "full" -/
def empty : AdjectivalPredicateEntry 10 where
  form := "empty"
  scaleType := .closed
  dimension := "fullness"
  antonymForm := some "full"
  antonymRelation := some .contradictory


/-- "hot" — open scale, contrary to "cold" -/
def hot : AdjectivalPredicateEntry 10 where
  form := "hot"
  scaleType := .open_
  dimension := "temperature"
  antonymForm := some "cold"
  antonymRelation := some .contrary

/-- "cold" — open scale, contrary to "hot" -/
def cold : AdjectivalPredicateEntry 10 where
  form := "cold"
  scaleType := .open_
  dimension := "temperature"
  antonymForm := some "hot"
  antonymRelation := some .contrary


/-- "expensive" — open scale, contrary to "cheap" -/
def expensive : AdjectivalPredicateEntry 10 where
  form := "expensive"
  scaleType := .open_
  dimension := "cost"
  antonymForm := some "cheap"
  antonymRelation := some .contrary

/-- "cheap" — open scale, contrary to "expensive" -/
def cheap : AdjectivalPredicateEntry 10 where
  form := "cheap"
  scaleType := .open_
  dimension := "cost"
  antonymForm := some "expensive"
  antonymRelation := some .contrary

/-- "wet" — lower-closed scale (minimum at 0) -/
def wet : AdjectivalPredicateEntry 10 where
  form := "wet"
  scaleType := .lowerClosed
  dimension := "wetness"
  antonymForm := some "dry"
  antonymRelation := some .contradictory

/-- "dry" — upper-closed scale (maximum at top) -/
def dry : AdjectivalPredicateEntry 10 where
  form := "dry"
  scaleType := .upperClosed
  dimension := "wetness"
  antonymForm := some "wet"
  antonymRelation := some .contradictory


/-- All adjectival predicate entries -/
def allEntries : List (AdjectivalPredicateEntry 10) := [
  tall, short,
  happy, unhappy, sad,
  full, empty,
  hot, cold,
  expensive, cheap,
  wet, dry
]

/-- Look up an entry by form -/
def lookup (form : String) : Option (AdjectivalPredicateEntry 10) :=
  allEntries.find? (·.form == form)

end Fragments.English.Predicates.Adjectival
