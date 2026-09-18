import Linglib.Syntax.Negation

/-!
# Maori negation

Maori negates a clause with the negative verb *kāore*, which stands first and takes the negated
clause as its complement; the subject usually follows *kāore* directly, ahead of the tense
particle and the verb: *e haere ana ia* 'he is going', *kāore ia e haere ana* 'he is not going'.
The perfect particle *kua* of the affirmative is *kia* under *kāore*, as in complement clauses
generally. The examples are those of [miestamo-2005], from Harlow's grammar.

## References

* [miestamo-2005]
-/

namespace Maori.Negation

open Syntax.Negation Morphology

/-- The negative verb *kāore*. -/
def kaore : Marker := { pieces := [[.free "kāore"]] }

private def words (ws : List String) : List Morph := ws.map .free

/-- The progressive and the past of *haere* 'go'. -/
def pairs : List Pair :=
  [⟨words ["e", "haere", "ana", "ia"], words ["kāore", "ia", "e", "haere", "ana"]⟩,
   ⟨words ["i", "haere", "ia"], words ["kāore", "ia", "i", "haere"]⟩]

end Maori.Negation
