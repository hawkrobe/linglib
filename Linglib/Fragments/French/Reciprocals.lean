import Linglib.Core.Lexical.Pronouns

/-!
# French Reciprocal Fragment
@cite{nordlinger-2023} @cite{siloni-2008}

French has two reciprocal strategies:

1. **"se"** — reflexive clitic, also used for reciprocal (monovalent).
   Syntactically formed per @cite{siloni-2008}: CANNOT form discontinuous
   reciprocals (@cite{nordlinger-2023} ex. 39).

2. **"l'un l'autre"** — bipartite NP (bivalent, literally 'the one the other').
   Preserves transitivity. Often co-occurs with "se" for disambiguation.

The identity of "se" in reflexive and reciprocal uses is captured by
WALS Ch 106 classifying French as "mixed."
-/

namespace Fragments.French.Reciprocals

open Core.Pronouns

/-- se — reflexive/reciprocal clitic (monovalent strategy). -/
def se : PronounEntry :=
  { form := "se", person := some .third }

/-- l'un l'autre — bipartite reciprocal NP (bivalent strategy). -/
def lunLautre : PronounEntry :=
  { form := "l'un l'autre", person := some .third, number := some .pl }

/-- The bipartite NP form is distinct from the clitic. -/
theorem bipartite_distinct_from_clitic :
    lunLautre.form ≠ se.form := by decide

end Fragments.French.Reciprocals
