module

public import Linglib.Fragments.Turkish.Morphotactics

/-!
# Turkish possession

This file defines the Turkish possessive existential sentence as Göksel and Kerslake describe
it, the construction Stassen classes as a genitive possessive and Heine derives from the
genitive schema. The possessor is a genitive noun phrase and the possessee carries the
possessive suffix that agrees with it in person, the two forming the genitive-possessive
construction of attributive possession, and the predicate is *var* 'existent' or *yok*
'non-existent', with a copular marker outside the present tense: *Mehmed'in parası var*
'Mehmet has money' and *Mehmed'in parası yok* 'Mehmet has no money'. Lewis's observation,
which Stassen takes up, is that the possessor is a sentence topic and not the modifier of the
possessee, since adverbials may come between them. The locative existential *bende bir kitap
var* 'I have a book' is the same predicate on a locative phrase.

## Main definitions

* `Turkish.Possession.Existential`: *var* and *yok*, with `Existential.form`
* `Turkish.Possession.possessor`, `Turkish.Possession.possessee`: the genitive, and the noun
  with the possessive suffix of a cell, as surface forms
* `Turkish.Possession.sentence`: the possessive existential sentence of a possessor, a possessee
  and a predicate

## Main results

* `Turkish.Possession.mehmet`: the surface forms of Lewis's two sentences

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [B. Heine, *Possession: Cognitive Sources, Forces, and Grammaticalization*
  (1997)][heine-1997]
* [L. Stassen, *Predicative Possession* (2009)][stassen-2009]
-/

@[expose] public section

open Phonology Turkish Turkish.Phonology Turkish.Nominal

namespace Turkish.Possession

/-- The existential predicates *var* 'existent' and *yok* 'non-existent', which take the
copular markers and person markers of a nominal predicate. -/
inductive Existential where
  | var
  | yok
  deriving DecidableEq, Repr, Fintype

/-- The form of a predicate. -/
def Existential.form : Existential → List Segment
  | .var => [v, a, r]
  | .yok => [y, o, k]

/-- The possessor is the genitive of its stem. -/
def possessor (w : List Segment) : List Segment := realize w [Exponent.genitive.form]

/-- The possessee carries the possessive suffix of the possessor's person and number. -/
def possessee (w : List Segment) (c : Agreement.Bundle) : List Segment :=
  realize w [(Exponent.possessive c).form]

/-- The possessive existential sentence of a possessor, a possessee and a predicate. -/
def sentence (pr pe : List Segment) (c : Agreement.Bundle) (e : Existential) :
    List (List Segment) :=
  [possessor pr, possessee pe c, e.form]

/-- *Mehmed'in parası var* 'Mehmet has money' and *Mehmed'in parası yok* 'Mehmet has no
money'. -/
theorem mehmet :
    sentence [m, e, h, m, e, d] [p, a, r, a] (.pn .third .singular) .var =
        [[m, e, h, m, e, d, i, n], [p, a, r, a, s, ı], [v, a, r]] ∧
      sentence [m, e, h, m, e, d] [p, a, r, a] (.pn .third .singular) .yok =
        [[m, e, h, m, e, d, i, n], [p, a, r, a, s, ı], [y, o, k]] := by
  decide

end Turkish.Possession
