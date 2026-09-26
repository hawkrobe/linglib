module

public import Linglib.Syntax.Reciprocal
public import Linglib.Fragments.Romance.Portuguese.Verbs

/-!
# Portuguese reciprocals

Brazilian Portuguese marks reciprocity with the clitic *se*, which is also the reflexive and
yields a monovalent predicate, and with the bipartite *um o outro* 'one the other'. Beside these
a class of transitive verbs has a lexical reciprocal entry: with *abraçar* 'hug' and its
siblings the reciprocal reading also arises without *se*, in Brazilian Portuguese both in finite
clauses, *X e Y abraçaram*, and in analytic causatives, *eu fiz X e Y abraçarem*, the two
environments of Palmieri's table where the clitic may be omitted. The lexical reciprocals are
entries of `Portuguese.Verbs`, and their two-entry analysis is the matter of
`Studies/Palmieri2024.lean`.

## Main definitions

* `Portuguese.Reciprocals.seClitic`, `Portuguese.Reciprocals.bipartite`,
  `Portuguese.Reciprocals.markers`: the reciprocal markers.
* `Portuguese.Reciprocals.lexicalReciprocals`: the verbs with a lexical reciprocal entry.

## References

* [palmieri-2024]
-/

@[expose] public section

namespace Portuguese.Reciprocals

open Reciprocal

/-- The clitic *se* in its reciprocal use, also the reflexive. -/
def seClitic : Marker :=
  { form := "se", strategy := .recipClitic, readings := {.reciprocal, .reflexive} }

/-- The bipartite *um o outro* 'one the other'. -/
def bipartite : Marker := { form := "um o outro", strategy := .bipartiteNP }

/-- The reciprocal markers. -/
def markers : Finset Marker := {seClitic, bipartite}

/-- The verbs with a lexical reciprocal entry, whose reciprocal reading survives without *se*
in finite clauses and analytic causatives. -/
def lexicalReciprocals : List Verb :=
  [Verbs.abracar, Verbs.beijar, Verbs.casar, Verbs.consultar, Verbs.cumprimentar,
    Verbs.encontrar, Verbs.namorar]

end Portuguese.Reciprocals
