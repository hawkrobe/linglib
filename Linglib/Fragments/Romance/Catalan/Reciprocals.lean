import Linglib.Syntax.Reciprocal

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

/-- Lexical reciprocal verbs with a transitive alternate
    ([palmieri-2024], Appendix A). The alternate is homophonous with the
    reciprocal entry in Romance. -/
def lexicalReciprocals : List LexicalVerb :=
  [ { form := "abraçar", gloss := "hug", transitiveAlternate := some "abraçar" }
  , { form := "casar", gloss := "marry", transitiveAlternate := some "casar" }
  , { form := "deixar", gloss := "leave/break up", transitiveAlternate := some "deixar" }
  , { form := "petonejar", gloss := "kiss", transitiveAlternate := some "petonejar" }
  , { form := "topar", gloss := "run into, meet accidentally", transitiveAlternate := some "topar" }
  , { form := "trobar", gloss := "find/meet", transitiveAlternate := some "trobar" } ]

end Catalan.Reciprocals
