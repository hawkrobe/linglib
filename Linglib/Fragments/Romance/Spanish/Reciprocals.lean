import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Romance.Spanish.Verbs

/-!
# Spanish reciprocals

Spanish marks reciprocity with the clitic *se*, shared with the reflexive, and with the periphrastic
*el uno al otro*, beside a class of lexical reciprocal verbs whose reciprocal reading also emerges
without *se* in language-specific environments ([palmieri-2024] ch. 2, Table 2.2;
`lexicalReciprocals` is the verb list of Appendix A).

## References

* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
-/

namespace Spanish.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { form := "se", strategy := .recipClitic
  , readings := {.reciprocal, .reflexive} }

/-- el uno al otro — periphrastic bipartite reciprocal (consensus periphrastic). -/
def bipartite : Marker :=
  { form := "el uno al otro", strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {seClitic, bipartite}

/-- The verbs carrying lexical reciprocal entries ([palmieri-2024],
    Appendix A), referenced as ordinary verb entries — the lexical
    strategy marks predicates, not forms. The transitive alternate is
    the entry itself (homophonous in Romance). -/
def lexicalReciprocals : List Verb :=
  [Verbs.abrazar, Verbs.acurrucar, Verbs.besar, Verbs.casar, Verbs.consultar, Verbs.cruzar,
    Verbs.dejar, Verbs.encontrar]

end Spanish.Reciprocals
