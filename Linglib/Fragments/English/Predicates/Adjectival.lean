import Linglib.Theories.Semantics.Lexical.Adjective.Theory

/-! # Adjectival Predicate Lexicon Fragment

Gradable adjective entries following @cite{kennedy-2007}. Scale type, dimension, antonyms.
-/

namespace Fragments.English.Predicates.Adjectival

open Semantics.Lexical.Adjective (AntonymRelation GradableAdjEntry)
open Core.Scale (Boundedness)
open Semantics.Lexical.Adjective (NegationType)


/-- @cite{kennedy-2007}
An adjectival predicate entry.

This is an alias for `GradableAdjEntry` from the Theory module, re-exported
here for the Fragments organization.
-/
abbrev AdjectivalPredicateEntry := GradableAdjEntry


/-- "tall" — open scale, contrary to "short" -/
def tall : AdjectivalPredicateEntry where
  form := "tall"
  scaleType := .open_
  dimension := .height
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "short" — open scale, contrary to "tall" -/
def short : AdjectivalPredicateEntry where
  form := "short"
  scaleType := .open_
  dimension := .height
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
  dimension := .happiness
  antonymForm := some "unhappy"
  antonymRelation := some .contrary

/-- "unhappy" — open scale, contrary to "happy" -/
def unhappy : AdjectivalPredicateEntry where
  form := "unhappy"
  scaleType := .open_
  dimension := .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary

/-- "sad" — open scale, contrary to "happy" (near-synonym of unhappy) -/
def sad : AdjectivalPredicateEntry where
  form := "sad"
  scaleType := .open_
  dimension := .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary


/-- "full" — closed scale, contradictory to "empty" -/
def full : AdjectivalPredicateEntry where
  form := "full"
  scaleType := .closed
  dimension := .fullness
  antonymForm := some "empty"
  antonymRelation := some .contradictory  -- Closed scales often contradictory

/-- "empty" — closed scale, contradictory to "full" -/
def empty : AdjectivalPredicateEntry where
  form := "empty"
  scaleType := .closed
  dimension := .fullness
  antonymForm := some "full"
  antonymRelation := some .contradictory


/-- "hot" — open scale, contrary to "cold" -/
def hot : AdjectivalPredicateEntry where
  form := "hot"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "cold"
  antonymRelation := some .contrary

/-- "cold" — open scale, contrary to "hot" -/
def cold : AdjectivalPredicateEntry where
  form := "cold"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "hot"
  antonymRelation := some .contrary


/-- "expensive" — open scale, contrary to "cheap" -/
def expensive : AdjectivalPredicateEntry where
  form := "expensive"
  scaleType := .open_
  dimension := .cost
  antonymForm := some "cheap"
  antonymRelation := some .contrary

/-- "cheap" — open scale, contrary to "expensive" -/
def cheap : AdjectivalPredicateEntry where
  form := "cheap"
  scaleType := .open_
  dimension := .cost
  antonymForm := some "expensive"
  antonymRelation := some .contrary

/-- "wet" — lower-closed scale (minimum at 0) -/
def wet : AdjectivalPredicateEntry where
  form := "wet"
  scaleType := .lowerBounded
  dimension := .wetness
  antonymForm := some "dry"
  antonymRelation := some .contradictory

/-- "dry" — upper-closed scale (maximum at top) -/
def dry : AdjectivalPredicateEntry where
  form := "dry"
  scaleType := .upperBounded
  dimension := .wetness
  antonymForm := some "wet"
  antonymRelation := some .contradictory


/-- "clean" — closed scale (maximally clean), contradictory to "dirty" -/
def clean : AdjectivalPredicateEntry where
  form := "clean"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "dirty"
  antonymRelation := some .contradictory

/-- "dirty" — closed scale (maximally dirty), contradictory to "clean" -/
def dirty : AdjectivalPredicateEntry where
  form := "dirty"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "clean"
  antonymRelation := some .contradictory

/-- "straight" — closed scale (maximally straight), contradictory to "bent" -/
def straight : AdjectivalPredicateEntry where
  form := "straight"
  scaleType := .closed
  dimension := .straightness
  antonymForm := some "bent"
  antonymRelation := some .contradictory

/-- "flat" — closed scale (maximally flat), contradictory to "bumpy" -/
def flat : AdjectivalPredicateEntry where
  form := "flat"
  scaleType := .closed
  dimension := .flatness
  antonymForm := some "bumpy"
  antonymRelation := some .contradictory

/-- "open" — closed scale (maximally open), contradictory to "closed" -/
def open_ : AdjectivalPredicateEntry where
  form := "open"
  scaleType := .closed
  dimension := .openness
  antonymForm := some "closed"
  antonymRelation := some .contradictory

/-- "large" — open scale, contrary to "small" -/
def large : AdjectivalPredicateEntry where
  form := "large"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "small"
  antonymRelation := some .contrary

/-- "small" — open scale, contrary to "large" -/
def small : AdjectivalPredicateEntry where
  form := "small"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "large"
  antonymRelation := some .contrary

/-- "gigantic" — open scale, contrary to "tiny", informationally stronger than "large" -/
def gigantic : AdjectivalPredicateEntry where
  form := "gigantic"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "tiny"
  antonymRelation := some .contrary

/-- "tiny" — open scale, contrary to "gigantic", informationally stronger than "small" -/
def tiny : AdjectivalPredicateEntry where
  form := "tiny"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "gigantic"
  antonymRelation := some .contrary

/-- "pristine" — closed scale, contrary to "filthy" (extreme absolute: gap exists) -/
def pristine : AdjectivalPredicateEntry where
  form := "pristine"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "filthy"
  antonymRelation := some .contrary

/-- "filthy" — closed scale, contrary to "pristine" (extreme absolute: gap exists) -/
def filthy : AdjectivalPredicateEntry where
  form := "filthy"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "pristine"
  antonymRelation := some .contrary

/-- "long" — open scale, contrary to "short" (length dimension) -/
def long : AdjectivalPredicateEntry where
  form := "long"
  scaleType := .open_
  dimension := .length
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "wide" — open scale, contrary to "narrow" -/
def wide : AdjectivalPredicateEntry where
  form := "wide"
  scaleType := .open_
  dimension := .width
  antonymForm := some "narrow"
  antonymRelation := some .contrary

/-- "cool" — open scale, contrary to "warm" -/
def cool : AdjectivalPredicateEntry where
  form := "cool"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "warm"
  antonymRelation := some .contrary

/-- "warm" — open scale, contrary to "cool" -/
def warm : AdjectivalPredicateEntry where
  form := "warm"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "cool"
  antonymRelation := some .contrary

/-- All adjectival predicate entries -/
def allEntries : List (AdjectivalPredicateEntry) := [
  tall, short,
  happy, unhappy, sad,
  full, empty,
  hot, cold,
  expensive, cheap,
  wet, dry,
  clean, dirty, straight, flat, open_,
  large, small, gigantic, tiny,
  pristine, filthy,
  long, wide, cool, warm
]

/-- Look up an entry by form -/
def lookup (form : String) : Option (AdjectivalPredicateEntry) :=
  allEntries.find? (·.form == form)

end Fragments.English.Predicates.Adjectival
