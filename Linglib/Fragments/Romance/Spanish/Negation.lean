import Linglib.Syntax.Negation

/-!
# Spanish negation

Spanish negates a clause with the preverbal particle *no*, and nothing else in the clause
changes: *canta-s* 'you sing', *no canta-s* 'you do not sing'. A preverbal n-word excludes *no*
and a postverbal one requires it; the n-words are entered in
`Fragments/Romance/Spanish/PolarityItems.lean`. The example is that of [miestamo-2005].

## References

* [miestamo-2005]
-/

open Negation Morphology

namespace Spanish.Negation

/-- *no*, the standard negator. -/
def no : Marker := { pieces := [[.free "no"]] }

/-- *canta-s* 'you sing' and its negative. -/
def pairs : List Pair :=
  [⟨[.root "canta", .suff "s"], [.free "no", .root "canta", .suff "s"]⟩]

end Spanish.Negation
