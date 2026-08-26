import Mathlib.Tactic.DeriveFintype

/-!
# Yanyuwa gender

The seven gender classes of Yanyuwa (Pama-Nyungan, Australia) after Kirton's descriptions as
tabulated in [adamson-2024]: the agreement prefixes they take on adjectives and numerals, the
possessor prefixes borne by body-part nouns and *wini* 'name', and the fact that the female and
feminine classes share their prefix.

## References

* [adamson-2024]
-/

namespace Yanyuwa

/-- The gender classes. -/
inductive Gender where
  | female
  | male
  | feminine
  | masculine
  | food
  | arboreal
  | abstract
  deriving DecidableEq, Repr, Fintype

/-- The agreement prefix on adjectives and numerals. -/
def agreementPrefix : Gender → String
  | .female => "řa-"
  | .feminine => "řa-"
  | .male => "nja-"
  | .masculine => "∅-"
  | .food => "ma-"
  | .arboreal => "na-"
  | .abstract => "naṇu-"

/-- Third-person singular possessor prefixes on body parts, by the possessor's class. -/
def possessorPrefix : Gender → Option String
  | .female => some "nanda-"
  | .feminine => some "nanda-"
  | .male => some "niwa-"
  | .masculine => some "ni-"
  | .food => some "nu-"
  | .arboreal => some "nanu-"
  | .abstract => none

/-- Nouns that take the possessor prefixes: body parts and *wini* 'name'. -/
def prefixedNouns : List (String × String) :=
  [("malidji", "finger"), ("maṇḍa", "foot"), ("liřbi", "scales"), ("mulu", "mouth"),
    ("wini", "name")]

end Yanyuwa
