import Linglib.Syntax.Reciprocal

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

/-- Lexical reciprocal verbs with a transitive alternate
    ([palmieri-2024], Appendix A). The alternate is homophonous with the
    reciprocal entry in Romance. -/
def lexicalReciprocals : List LexicalVerb :=
  [ { form := "abrazar", gloss := "hug", transitiveAlternate := some "abrazar" }
  , { form := "acurrucar", gloss := "cuddle", transitiveAlternate := some "acurrucar" }
  , { form := "besar", gloss := "kiss", transitiveAlternate := some "besar" }
  , { form := "casar", gloss := "marry", transitiveAlternate := some "casar" }
  , { form := "consultar", gloss := "consult/confer", transitiveAlternate := some "consultar" }
  , { form := "cruzar", gloss := "run into, meet accidentally", transitiveAlternate := some "cruzar" }
  , { form := "dejar", gloss := "leave/break up", transitiveAlternate := some "dejar" }
  , { form := "encontrar", gloss := "find/meet", transitiveAlternate := some "encontrar" } ]

end Spanish.Reciprocals
