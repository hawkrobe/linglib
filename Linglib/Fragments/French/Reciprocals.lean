import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Reciprocal

/-!
# French Reciprocal Fragment
[nordlinger-2023] [siloni-2008]

French has two reciprocal strategies:

1. **"se"** — reflexive clitic, also used for reciprocal (monovalent).
   Syntactically formed per [siloni-2008]: CANNOT form discontinuous
   reciprocals ([nordlinger-2023] ex. 39).

2. **"l'un l'autre"** — bipartite NP (bivalent, literally 'the one the other').
   Preserves transitivity. Often co-occurs with "se" for disambiguation.

The identity of "se" in reflexive and reciprocal uses is captured by
WALS Ch 106 classifying French as "mixed."
-/

namespace French.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([nordlinger-2023] ex. 28, 47). -/
def se : Marker :=
  { form := "se", strategy := .recipClitic
  , readings := [.reciprocal, .reflexive] }

/-- l'un l'autre — bipartite reciprocal NP. -/
def lunLautre : Marker :=
  { form := "l'un l'autre", strategy := .bipartiteNP }

/-- The bipartite NP form is distinct from the clitic. -/
theorem bipartite_distinct_from_clitic :
    lunLautre.form ≠ se.form := by decide

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [se, lunLautre]

end French.Reciprocals
