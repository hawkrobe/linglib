import Linglib.Syntax.Reciprocal

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

/-- Lexical reciprocal verbs with a transitive alternate
    ([palmieri-2024], Appendix A). The alternate is homophonous with the
    reciprocal entry in Romance. -/
def lexicalReciprocals : List LexicalVerb :=
  [ { form := "abraçar", gloss := "hug", transitiveAlternate := some "abraçar" }
  , { form := "beijar", gloss := "kiss", transitiveAlternate := some "beijar" }
  , { form := "casar", gloss := "marry", transitiveAlternate := some "casar" }
  , { form := "consultar", gloss := "consult/confer", transitiveAlternate := some "consultar" }
  , { form := "cumprimentar", gloss := "greet", transitiveAlternate := some "cumprimentar" }
  , { form := "encontrar", gloss := "meet", transitiveAlternate := some "encontrar" }
  , { form := "namorar", gloss := "date, be partners", transitiveAlternate := some "namorar" } ]

end BrazilianPortuguese.Reciprocals
