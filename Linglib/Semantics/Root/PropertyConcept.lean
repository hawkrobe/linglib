import Mathlib.Tactic.DeriveFintype

/-!
# Property-concept classes

[dixon-1982]'s seven semantic classes of property-concept lexemes, the words that
surface as adjectives in English and as verbs, nouns, or adjectives elsewhere.
[beavers-etal-2021] (5) sample all but human propensity, and
[hanink-koontz-garboden-2025] class Wá·šiw property-concept roots by them.

## Main declarations

* `PropertyConcept.Class` — Dixon's seven classes

## References

* [dixon-1982]: Where Have All the Adjectives Gone?
-/

namespace Semantics

/-- [dixon-1982]'s semantic classes of property concepts. -/
inductive PropertyConcept.Class where
  /-- large, small, long, short, deep, wide, tall. -/
  | dimension
  /-- old. -/
  | age
  /-- bad, good. -/
  | value
  /-- white, black, red, green, blue, brown. -/
  | color
  /-- cold, warm, dry, soft, smooth. -/
  | physicalProperty
  /-- angry, embarrassed. -/
  | humanPropensity
  /-- fast, slow. -/
  | speed
  deriving DecidableEq, Fintype, Repr

end Semantics
