module

public import Linglib.Syntax.Negation

/-!
# Imbabura Quechua negation

Imbabura Quechua negates a clause with the particle *mana* before the verb together with the
enclitic *-chu* on a constituent of the clause, and both are obligatory: *ñuka wawki mana jatun
wasi-ta chari-n-chu* 'my brother does not have a big house'. The enclitic is not itself
negative. It also marks polar questions, *kan-paj wawki jatun wasi-ta chari-n-chu* 'does your
brother have a big house?', and does not occur in affirmative declaratives, *juzi iskay
kaballu-ta chari-n* 'José has two horses', so a negative without *mana* is a question. The
examples are Miestamo's, from Cole's grammar.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation Morphology

namespace Quechua.Negation

/-- *mana*, the negative particle. -/
def mana : Marker := ⟨[[.free "mana"]]⟩

/-- *-chu*, the enclitic of negatives and polar questions. -/
def chu : Morph := .encl "chu"

/-- *juzi iskay kaballu-ta chari-n* 'José has two horses', an affirmative declarative. -/
def declarative : List Morph :=
  [.free "juzi", .free "iskay", .root "kaballu", .suff "ta", .root "chari", .suff "n"]

/-- *ñuka wawki mana jatun wasi-ta chari-n-chu* 'my brother does not have a big house'. -/
def negative : List Morph :=
  [.free "ñuka", .free "wawki", .free "mana", .free "jatun", .root "wasi", .suff "ta",
    .root "chari", .suff "n", chu]

/-- *kan-paj wawki jatun wasi-ta chari-n-chu* 'does your brother have a big house?'. -/
def interrogative : List Morph :=
  [.root "kan", .suff "paj", .free "wawki", .free "jatun", .root "wasi", .suff "ta",
    .root "chari", .suff "n", chu]

end Quechua.Negation
