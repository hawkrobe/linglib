module

public import Linglib.Syntax.Negation

/-!
# German negation

This file defines German standard negation, the particle *nicht*, which follows the finite verb of
a main clause: *ich singe* 'I sing', *ich singe nicht* 'I do not sing'. Nothing else in the
clause changes, in any person or tense. The examples are Miestamo's.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace German.Negation

/-- *Nicht* is the standard negator. -/
def nicht : Marker := { pieces := [[.free "nicht"]] }

/-- The first person singular present and past of *singen* 'sing' pair with their negations. -/
def pairs : List Pair :=
  [⟨nicht, ["ich", "singe"].map .free, ["ich", "singe", "nicht"].map .free⟩,
   ⟨nicht, ["ich", "sang"].map .free, ["ich", "sang", "nicht"].map .free⟩]

end German.Negation
