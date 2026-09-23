module

public import Linglib.Syntax.Negation

/-!
# Imbabura Quechua negation

Imbabura Quechua negates a clause with the particle *mana* before the verb together with the
enclitic *-chu* on a constituent of the clause, and both are obligatory: *ñuka wawki mana jatun
wasi-ta chari-n-chu* 'my brother does not have a big house'. The enclitic is not itself
negative. It also marks polar questions, *kan-paj wawki jatun wasi-ta chari-n-chu* 'does your
brother have a big house?', and does not occur in affirmative declaratives, so a negative
without *mana* is a question. The examples are those of [miestamo-2005], from Cole's grammar.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace Quechua.Negation

/-- *mana … -chu*, the standard negator: the particle with the enclitic it requires. -/
def manaChu : Marker := { pieces := [[.free "mana"], [.encl "chu"]] }

/-- *-chu*, the enclitic of negatives and polar questions. -/
def chu : Morphology.Morph := .encl "chu"

end Quechua.Negation
