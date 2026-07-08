import Linglib.Syntax.Reciprocal

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

/-- Lexical reciprocal verbs with a transitive alternate
    ([palmieri-2024], Appendix A). The alternate is homophonous with the
    reciprocal entry in Romance. -/
def lexicalReciprocals : List LexicalVerb :=
  [ { form := "abbracciare", gloss := "hug", transitiveAlternate := some "abbracciare" }
  , { form := "baciare", gloss := "kiss", transitiveAlternate := some "baciare" }
  , { form := "coccolare", gloss := "cuddle", transitiveAlternate := some "coccolare" }
  , { form := "conoscere", gloss := "know (of)", transitiveAlternate := some "conoscere" }
  , { form := "consultare", gloss := "consult/confer", transitiveAlternate := some "consultare" }
  , { form := "frequentare", gloss := "date", transitiveAlternate := some "frequentare" }
  , { form := "incontrare", gloss := "meet", transitiveAlternate := some "incontrare" }
  , { form := "incrociare", gloss := "run into, meet accidentally", transitiveAlternate := some "incrociare" }
  , { form := "lasciare", gloss := "leave/break up", transitiveAlternate := some "lasciare" }
  , { form := "sposare", gloss := "marry", transitiveAlternate := some "sposare" }
  , { form := "trovare", gloss := "find/meet", transitiveAlternate := some "trovare" }
  , { form := "vedere", gloss := "see/meet", transitiveAlternate := some "vedere" } ]

end Italian.Reciprocals
