import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Romance.Catalan.Predicates

/-!
# Catalan Reciprocal Fragment
[palmieri-2024]

Catalan encodes reciprocity with the reflexive-identical clitic *es*
(the grammatical strategy) and the periphrastic *l'un a l'altre*, alongside a
class of lexical reciprocal verbs — verbs with a transitive entry whose
reciprocal reading also emerges without *es* in language-specific
environments ([palmieri-2024] ch. 2, Table 2.2; Appendix A carries the
verb list formalized in `lexicalReciprocals`).
-/

namespace Catalan.Reciprocals

open Reciprocal

/-- es — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { form := "es", strategy := .recipClitic
  , readings := [.reciprocal, .reflexive] }

/-- l'un a l'altre — periphrastic bipartite reciprocal (consensus periphrastic). -/
def bipartite : Marker :=
  { form := "l'un a l'altre", strategy := .bipartiteNP }

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [seClitic, bipartite]

/-- The verbs carrying lexical reciprocal entries ([palmieri-2024],
    Appendix A), referenced as ordinary verb entries — the lexical
    strategy marks predicates, not forms. The transitive alternate is
    the entry itself (homophonous in Romance). -/
def lexicalReciprocals : List Verb :=
  [Predicates.abracar, Predicates.casar, Predicates.deixar, Predicates.petonejar, Predicates.topar, Predicates.trobar]

end Catalan.Reciprocals
