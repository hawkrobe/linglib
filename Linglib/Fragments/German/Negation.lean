import Linglib.Syntax.Negation

/-!
# German negation

German negates a clause with the particle *nicht*, which follows the finite verb of a main
clause: *ich singe* 'I sing', *ich singe nicht* 'I do not sing'. Nothing else in the clause
changes, in any person or tense. The examples are those of [miestamo-2005].

## References

* [miestamo-2005]
-/

open Negation Morphology

namespace German.Negation

/-- *nicht*, the standard negator. -/
def nicht : Marker := { pieces := [[.free "nicht"]] }

private def words (ws : List String) : List Morph := ws.map .free

/-- The first person singular present and past of *singen* 'sing'. -/
def pairs : List Pair :=
  [⟨words ["ich", "singe"], words ["ich", "singe", "nicht"]⟩,
   ⟨words ["ich", "sang"], words ["ich", "sang", "nicht"]⟩]

end German.Negation
