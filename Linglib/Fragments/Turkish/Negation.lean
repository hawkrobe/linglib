import Linglib.Syntax.Negation

/-!
# Turkish negation

Turkish negates a verb with the suffix *-mA-*, *-ma-* or *-me-* by vowel harmony, between the
stem and the tense suffix: *gel-di* 'came', *gel-me-di* 'did not come'. The aorist is the one
tense whose marking changes under negation: the aorist suffix *-ir* of *gel-ir* 'comes' is *-z*
in the negative of the second and third persons, *gel-me-z*, and is absent in the first person,
*gel-me-m* beside *gel-ir-im*. The examples are those of [miestamo-2005].

## Implementation notes

The negative suffix is cited as *-mA-* and the future suffix as *-ecek* in both members of a
pair; the glide of *gel-me-yecek* is phonological.

## References

* [miestamo-2005]
-/

namespace Turkish.Negation

open Syntax.Negation Morphology

/-- The negative suffix *-mA-*. -/
def mA : Marker := { pieces := [[.suff "mA"]] }

/-- The past and the future of *gel-* 'come'. -/
def nonAorist : List Pair :=
  [⟨[.root "gel", .suff "di"], [.root "gel", .suff "mA", .suff "di"]⟩,
   ⟨[.root "gel", .suff "ecek"], [.root "gel", .suff "mA", .suff "ecek"]⟩]

/-- The aorist of *gel-* 'come': third singular, first singular and third plural. -/
def aorist : List Pair :=
  [⟨[.root "gel", .suff "ir"], [.root "gel", .suff "mA", .suff "z"]⟩,
   ⟨[.root "gel", .suff "ir", .suff "im"], [.root "gel", .suff "mA", .suff "m"]⟩,
   ⟨[.root "gel", .suff "ir", .suff "ler"], [.root "gel", .suff "mA", .suff "z", .suff "ler"]⟩]

end Turkish.Negation
