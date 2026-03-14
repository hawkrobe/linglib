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
`Theories/Semantics/Attitudes/Preferential.lean`.
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

/-- "closed" — closed scale, contradictory to "open" -/
def closed_ : AdjectivalPredicateEntry where
  form := "closed"
  scaleType := .closed
  dimension := .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory

/-- "shut" — closed scale, contradictory to "open" (near-synonym of "closed") -/
def shut : AdjectivalPredicateEntry where
  form := "shut"
  scaleType := .closed
  dimension := .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory

/-- "free" — closed scale (maximally free = unattached), contradictory to "stuck" -/
def free_ : AdjectivalPredicateEntry where
  form := "free"
  scaleType := .closed
  dimension := .freedom
  antonymForm := some "stuck"
  antonymRelation := some .contradictory

/-- "loose" — closed scale (maximally loose), contradictory to "tight" -/
def loose : AdjectivalPredicateEntry where
  form := "loose"
  scaleType := .closed
  dimension := .tightness
  antonymForm := some "tight"
  antonymRelation := some .contradictory

/-- "tight" — closed scale (maximally tight), contradictory to "loose" -/
def tight : AdjectivalPredicateEntry where
  form := "tight"
  scaleType := .closed
  dimension := .tightness
  antonymForm := some "loose"
  antonymRelation := some .contradictory

/-- "bent" — lower-closed scale (minimum at 0 = straight), contradictory to "straight" -/
def bent : AdjectivalPredicateEntry where
  form := "bent"
  scaleType := .lowerBounded
  dimension := .straightness
  antonymForm := some "straight"
  antonymRelation := some .contradictory

/-- "smooth" — closed scale, contradictory to "rough" -/
def smooth : AdjectivalPredicateEntry where
  form := "smooth"
  scaleType := .closed
  dimension := .smoothness
  antonymForm := some "rough"
  antonymRelation := some .contradictory

/-- "rough" — closed scale, contradictory to "smooth" -/
def rough : AdjectivalPredicateEntry where
  form := "rough"
  scaleType := .closed
  dimension := .smoothness
  antonymForm := some "smooth"
  antonymRelation := some .contradictory

/-- "hard" — open scale, contrary to "soft" -/
def hard : AdjectivalPredicateEntry where
  form := "hard"
  scaleType := .open_
  dimension := .hardness
  antonymForm := some "soft"
  antonymRelation := some .contrary

/-- "soft" — open scale, contrary to "hard" -/
def soft : AdjectivalPredicateEntry where
  form := "soft"
  scaleType := .open_
  dimension := .hardness
  antonymForm := some "hard"
  antonymRelation := some .contrary

/-- "pure" — closed scale (maximally pure), contradictory to "impure" -/
def pure_ : AdjectivalPredicateEntry where
  form := "pure"
  scaleType := .closed
  dimension := .purity
  antonymForm := some "impure"
  antonymRelation := some .contradictory

/-- "dead" — closed scale (absolute: maximal endpoint), contradictory to "alive" -/
def dead : AdjectivalPredicateEntry where
  form := "dead"
  scaleType := .closed
  dimension := .alive
  antonymForm := some "alive"
  antonymRelation := some .contradictory

/-- "alive" — closed scale (absolute), contradictory to "dead" -/
def alive : AdjectivalPredicateEntry where
  form := "alive"
  scaleType := .closed
  dimension := .alive
  antonymForm := some "dead"
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

/-! ## Physical dimension adjectives -/

/-- "heavy" — open scale, contrary to "light" -/
def heavy : AdjectivalPredicateEntry where
  form := "heavy"
  scaleType := .open_
  dimension := .weight
  antonymForm := some "light"
  antonymRelation := some .contrary

/-- "light" — open scale, contrary to "heavy" -/
def light : AdjectivalPredicateEntry where
  form := "light"
  scaleType := .open_
  dimension := .weight
  antonymForm := some "heavy"
  antonymRelation := some .contrary

/-- "thick" — open scale, contrary to "thin" -/
def thick : AdjectivalPredicateEntry where
  form := "thick"
  scaleType := .open_
  dimension := .thickness
  antonymForm := some "thin"
  antonymRelation := some .contrary

/-- "thin" — open scale, contrary to "thick" -/
def thin : AdjectivalPredicateEntry where
  form := "thin"
  scaleType := .open_
  dimension := .thickness
  antonymForm := some "thick"
  antonymRelation := some .contrary

/-- "deep" — open scale, contrary to "shallow" -/
def deep : AdjectivalPredicateEntry where
  form := "deep"
  scaleType := .open_
  dimension := .depth
  antonymForm := some "shallow"
  antonymRelation := some .contrary

/-- "shallow" — open scale, contrary to "deep" -/
def shallow : AdjectivalPredicateEntry where
  form := "shallow"
  scaleType := .open_
  dimension := .depth
  antonymForm := some "deep"
  antonymRelation := some .contrary

/-- "strong" — open scale, contrary to "weak" -/
def strong : AdjectivalPredicateEntry where
  form := "strong"
  scaleType := .open_
  dimension := .strength
  antonymForm := some "weak"
  antonymRelation := some .contrary

/-- "weak" — open scale, contrary to "strong" -/
def weak : AdjectivalPredicateEntry where
  form := "weak"
  scaleType := .open_
  dimension := .strength
  antonymForm := some "strong"
  antonymRelation := some .contrary

/-- "fast" — open scale, contrary to "slow" -/
def fast : AdjectivalPredicateEntry where
  form := "fast"
  scaleType := .open_
  dimension := .speed
  antonymForm := some "slow"
  antonymRelation := some .contrary

/-- "slow" — open scale, contrary to "fast" -/
def slow : AdjectivalPredicateEntry where
  form := "slow"
  scaleType := .open_
  dimension := .speed
  antonymForm := some "fast"
  antonymRelation := some .contrary

/-- "old" — open scale, contrary to "young" -/
def old : AdjectivalPredicateEntry where
  form := "old"
  scaleType := .open_
  dimension := .age
  antonymForm := some "young"
  antonymRelation := some .contrary

/-- "young" — open scale, contrary to "old" -/
def young : AdjectivalPredicateEntry where
  form := "young"
  scaleType := .open_
  dimension := .age
  antonymForm := some "old"
  antonymRelation := some .contrary

/-! ## Sensory adjectives -/

/-- "bright" — open scale, contrary to "dark" -/
def bright : AdjectivalPredicateEntry where
  form := "bright"
  scaleType := .open_
  dimension := .brightness
  antonymForm := some "dark"
  antonymRelation := some .contrary

/-- "dark" — open scale, contrary to "bright" -/
def dark : AdjectivalPredicateEntry where
  form := "dark"
  scaleType := .open_
  dimension := .brightness
  antonymForm := some "bright"
  antonymRelation := some .contrary

/-- "loud" — open scale, contrary to "quiet" -/
def loud : AdjectivalPredicateEntry where
  form := "loud"
  scaleType := .open_
  dimension := .volume
  antonymForm := some "quiet"
  antonymRelation := some .contrary

/-- "quiet" — open scale, contrary to "loud" -/
def quiet : AdjectivalPredicateEntry where
  form := "quiet"
  scaleType := .open_
  dimension := .volume
  antonymForm := some "loud"
  antonymRelation := some .contrary

/-! ## Evaluative adjectives -/

/-- "good" — open scale, contrary to "bad" -/
def good : AdjectivalPredicateEntry where
  form := "good"
  scaleType := .open_
  dimension := .quality
  antonymForm := some "bad"
  antonymRelation := some .contrary

/-- "bad" — open scale, contrary to "good" -/
def bad : AdjectivalPredicateEntry where
  form := "bad"
  scaleType := .open_
  dimension := .quality
  antonymForm := some "good"
  antonymRelation := some .contrary

/-- "beautiful" — open scale, contrary to "ugly" -/
def beautiful : AdjectivalPredicateEntry where
  form := "beautiful"
  scaleType := .open_
  dimension := .beauty
  antonymForm := some "ugly"
  antonymRelation := some .contrary

/-- "ugly" — open scale, contrary to "beautiful" -/
def ugly : AdjectivalPredicateEntry where
  form := "ugly"
  scaleType := .open_
  dimension := .beauty
  antonymForm := some "beautiful"
  antonymRelation := some .contrary

/-- "important" — open scale -/
def important : AdjectivalPredicateEntry where
  form := "important"
  scaleType := .open_
  dimension := .importance

/-- "safe" — open scale, contrary to "dangerous" -/
def safe : AdjectivalPredicateEntry where
  form := "safe"
  scaleType := .open_
  dimension := .safety
  antonymForm := some "dangerous"
  antonymRelation := some .contrary

/-- "dangerous" — open scale, contrary to "safe" -/
def dangerous : AdjectivalPredicateEntry where
  form := "dangerous"
  scaleType := .open_
  dimension := .danger
  antonymForm := some "safe"
  antonymRelation := some .contrary

/-- All adjectival predicate entries -/
def allEntries : List (AdjectivalPredicateEntry) := [
  -- Height / size
  tall, short, large, small, gigantic, tiny,
  -- Happiness / evaluative
  happy, unhappy, sad,
  -- Fullness
  full, empty,
  -- Temperature
  hot, cold, cool, warm,
  -- Cost
  expensive, cheap,
  -- Wetness
  wet, dry,
  -- State: cleanliness, shape, surface
  clean, dirty, straight, bent, flat, smooth, rough,
  -- State: openness / barrier
  open_, closed_, shut,
  -- State: attachment / fit
  free_, loose, tight,
  -- State: hardness, purity, alive
  hard, soft, pure_, dead, alive,
  -- Informationally strong
  pristine, filthy,
  -- Physical dimensions
  long, wide, heavy, light, thick, thin, deep, shallow,
  strong, weak, fast, slow, old, young,
  -- Sensory
  bright, dark, loud, quiet,
  -- Evaluative
  good, bad, beautiful, ugly, important, safe, dangerous
]

/-- Look up an entry by form -/
def lookup (form : String) : Option (AdjectivalPredicateEntry) :=
  allEntries.find? (·.form == form)

end Fragments.English.Predicates.Adjectival
