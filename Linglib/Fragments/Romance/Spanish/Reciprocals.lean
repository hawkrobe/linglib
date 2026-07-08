import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Romance.Spanish.Predicates

/-!
# Spanish Reciprocal Fragment
[palmieri-2024]

Spanish encodes reciprocity with the reflexive-identical clitic *se*
(the grammatical strategy) and the periphrastic *el uno al otro*, alongside a
class of lexical reciprocal verbs — verbs with a transitive entry whose
reciprocal reading also emerges without *se* in language-specific
environments ([palmieri-2024] ch. 2, Table 2.2; Appendix A carries the
verb list formalized in `lexicalReciprocals`).
-/

namespace Spanish.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { form := "se", strategy := .recipClitic
  , readings := [.reciprocal, .reflexive] }

/-- el uno al otro — periphrastic bipartite reciprocal (consensus periphrastic). -/
def bipartite : Marker :=
  { form := "el uno al otro", strategy := .bipartiteNP }

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [seClitic, bipartite]

/-- The verbs carrying lexical reciprocal entries ([palmieri-2024],
    Appendix A), referenced as ordinary verb entries — the lexical
    strategy marks predicates, not forms. The transitive alternate is
    the entry itself (homophonous in Romance). -/
def lexicalReciprocals : List Verb :=
  [Predicates.abrazar, Predicates.acurrucar, Predicates.besar, Predicates.casar, Predicates.consultar, Predicates.cruzar, Predicates.dejar, Predicates.encontrar]

end Spanish.Reciprocals
