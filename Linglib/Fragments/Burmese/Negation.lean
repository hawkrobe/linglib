module

public import Linglib.Syntax.Negation

/-!
# Burmese negation

Burmese negates a verb with a discontinuous marker: the prefix *ma-* and a suffix, *-bû* in
*ma-θwâ-bû* '(he) does not go', which stands in the slot of the postverbal markers of the
affirmative. Those markers distinguish the actual *θwâ-dé* '(he) goes, went', the potential
*θwâ-mé* '(he) will go' and the perfect *θwâ-bí* '(he) has gone', and the one negative form
answers to all three. The examples are those of [miestamo-2005], from Cornyn's grammar.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation Morphology

namespace Burmese.Negation

/-- The discontinuous negator *ma-…-bû*, whose suffix [miestamo-2005] cites as *-phû*. -/
def maBu : Marker := { pieces := [[.pref "ma"], [.suff "bû"]] }

/-- The actual, potential and perfect of *θwâ* 'go', with their common negative. -/
def goParadigm : List Pair :=
  [⟨[.root "θwâ", .suff "dé"], [.pref "ma", .root "θwâ", .suff "bû"]⟩,
   ⟨[.root "θwâ", .suff "mé"], [.pref "ma", .root "θwâ", .suff "bû"]⟩,
   ⟨[.root "θwâ", .suff "bí"], [.pref "ma", .root "θwâ", .suff "bû"]⟩]

end Burmese.Negation
