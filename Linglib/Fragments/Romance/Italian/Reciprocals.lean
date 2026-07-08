import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Romance.Italian.Predicates

/-!
# Italian Reciprocal Fragment
[palmieri-2024]

Italian encodes reciprocity with the reflexive-identical clitic *si*
(the grammatical strategy) and the periphrastic *l'un l'altro*, alongside a
class of lexical reciprocal verbs — verbs with a transitive entry whose
reciprocal reading also emerges without *si* in language-specific
environments ([palmieri-2024] ch. 2, Table 2.2; Appendix A carries the
verb list formalized in `lexicalReciprocals`).
-/

namespace Italian.Reciprocals

open Reciprocal

/-- si — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { form := "si", strategy := .recipClitic
  , readings := [.reciprocal, .reflexive] }

/-- l'un l'altro — periphrastic bipartite reciprocal (consensus periphrastic; cf. the French sibling entry). -/
def bipartite : Marker :=
  { form := "l'un l'altro", strategy := .bipartiteNP }

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [seClitic, bipartite]

/-- The verbs carrying lexical reciprocal entries ([palmieri-2024],
    Appendix A), referenced as ordinary verb entries — the lexical
    strategy marks predicates, not forms. The transitive alternate is
    the entry itself (homophonous in Romance). -/
def lexicalReciprocals : List Verb :=
  [Predicates.abbracciare, Predicates.baciare, Predicates.coccolare, Predicates.conoscere, Predicates.consultare, Predicates.frequentare, Predicates.incontrare, Predicates.incrociare, Predicates.lasciare, Predicates.sposare, Predicates.trovare, Predicates.vedere]

end Italian.Reciprocals
