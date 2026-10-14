module

public import Linglib.Syntax.Negation

/-!
# Maori negation

Maori negates a clause with the negative verb *kāore*, which stands first and takes the negated
clause as its complement; the subject usually follows *kāore* directly, ahead of the tense
particle and the verb: *e haere ana ia* 'he is going', *kāore ia e haere ana* 'he is not going'.
The perfect particle *kua* of the affirmative is *kia* under *kāore*, as in complement clauses
generally. The examples are Miestamo's, from Harlow's grammar.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace Maori.Negation

/-- The negative verb *kāore*. -/
def kaore : Marker := { pieces := [[.free "kāore"]] }

/-- The progressive and the past of *haere* 'go'. -/
def pairs : List Pair :=
  [⟨kaore, ["e", "haere", "ana", "ia"].map .free,
    ["kāore", "ia", "e", "haere", "ana"].map .free⟩,
   ⟨kaore, ["i", "haere", "ia"].map .free, ["kāore", "ia", "i", "haere"].map .free⟩]

end Maori.Negation
