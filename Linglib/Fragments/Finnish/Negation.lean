import Linglib.Syntax.Negation
import Linglib.Syntax.Person.Basic
import Linglib.Syntax.Number.Basic

/-!
# Finnish negation

Finnish negates a clause with the negative auxiliary *e-*, cited in the third person singular
as *ei*. The auxiliary takes the person and number endings of the finite verb, and the lexical
verb stands in the connegative, a form without them: *nuku-n* 'I am sleeping', *e-n nuku* 'I am
not sleeping'. In the past the lexical verb is a participle, *en laulanut* 'I did not sing'.
The examples are those of [miestamo-2005].

## References

* [miestamo-2005]
-/

namespace Finnish.Negation

open Syntax.Negation Morphology

/-- The negative auxiliary *e-*. -/
def e : Marker := { pieces := [[.root "e"]] }

/-- The person and number endings of the negative auxiliary in the present: *en*, *et*, *ei*,
*emme*, *ette*, *eivät*. -/
def ending : Person → Number → Option Morph
  | .first, .singular => some (.suff "n")
  | .second, .singular => some (.suff "t")
  | .third, .singular => some (.suff "i")
  | .first, .plural => some (.suff "mme")
  | .second, .plural => some (.suff "tte")
  | .third, .plural => some (.suff "ivät")
  | _, _ => none

/-- First person singular presents with their negatives. -/
def present : List Pair :=
  [⟨[.root "nuku", .suff "n"], [.root "e", .suff "n", .root "nuku"]⟩,
   ⟨[.root "juokse", .suff "n"], [.root "e", .suff "n", .root "juokse"]⟩]

end Finnish.Negation
