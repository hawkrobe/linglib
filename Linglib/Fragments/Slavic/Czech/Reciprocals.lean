import Linglib.Syntax.Pronoun.Basic
import Linglib.Syntax.Reciprocal

/-!
# Czech Reciprocal Fragment
[nordlinger-2023] [siloni-2008] [siloni-2012]

Czech uses the reflexive clitic "se" for reciprocal meaning (monovalent),
syntactically formed per [siloni-2008]/[siloni-2012]: it cannot form
discontinuous reciprocals ([nordlinger-2023] ex. 29, p. 86).

Alongside "se", Czech has the periphrastic bipartite "jeden druhého"
('one the-other'), attested in [siloni-2012]'s Czech examples (comparative
ellipsis, depictives) — so the reciprocal-reflexive relation is the WALS
"mixed" configuration (WALS Ch 106 itself has no Czech row).
-/

namespace Czech.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([nordlinger-2023] ex. 29). -/
def se : Marker :=
  { form := "se", strategy := .recipClitic
  , readings := [.reciprocal, .reflexive] }

/-- jeden druhého — bipartite periphrastic reciprocal 'one the-other'
    ([siloni-2012]'s Czech examples). -/
def jedenDruheho : Marker :=
  { form := "jeden druhého", strategy := .bipartiteNP }

/-- The periphrastic reciprocal is distinct from the clitic. -/
theorem bipartite_distinct_from_clitic :
    jedenDruheho.form ≠ se.form := by decide

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [se, jedenDruheho]

end Czech.Reciprocals
