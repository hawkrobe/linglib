import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Romance.BrazilianPortuguese.Predicates

/-!
# Brazilian Portuguese Reciprocal Fragment
[palmieri-2024]

Brazilian Portuguese encodes reciprocity with the reflexive-identical clitic *se*
(the grammatical strategy) and the periphrastic *um o outro*, alongside a
class of lexical reciprocal verbs — verbs with a transitive entry whose
reciprocal reading also emerges without *se* in language-specific
environments ([palmieri-2024] ch. 2, Table 2.2; Appendix A carries the
verb list formalized in `lexicalReciprocals`).
-/

namespace BrazilianPortuguese.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { form := "se", strategy := .recipClitic
  , readings := [.reciprocal, .reflexive] }

/-- um o outro — periphrastic bipartite reciprocal (attested in [palmieri-2024] ch. 2 (se-omission licensor in finite clauses)). -/
def bipartite : Marker :=
  { form := "um o outro", strategy := .bipartiteNP }

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [seClitic, bipartite]

/-- The verbs carrying lexical reciprocal entries ([palmieri-2024],
    Appendix A), referenced as ordinary verb entries — the lexical
    strategy marks predicates, not forms. The transitive alternate is
    the entry itself (homophonous in Romance). -/
def lexicalReciprocals : List Verb :=
  [Predicates.abracar, Predicates.beijar, Predicates.casar, Predicates.consultar, Predicates.cumprimentar, Predicates.encontrar, Predicates.namorar]

end BrazilianPortuguese.Reciprocals
