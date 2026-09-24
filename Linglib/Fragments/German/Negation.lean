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

open Negation Morphology

namespace German.Negation

/-- *Nicht* is the standard negator. -/
def nicht : Marker := { pieces := [[.free "nicht"]] }

/-- `words ws` is the sentence `ws` as a list of free words. -/
def words (ws : List String) : List Morph := ws.map .free

/-- The first person singular present and past of *singen* 'sing' pair with their negations. -/
def pairs : List Pair :=
  [⟨words ["ich", "singe"], words ["ich", "singe", "nicht"]⟩,
   ⟨words ["ich", "sang"], words ["ich", "sang", "nicht"]⟩]

end German.Negation
