import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Reciprocal

/-!
# Russian Reciprocal Fragment
[nordlinger-2023] [konig-kokutani-2006]

Russian uses the bipartite NP "drug druga" (друг друга, 'other other-ACC'),
grouped with English *each other* as the bipartite quantifier strategy in
[nordlinger-2023] §3.1 (ex. 9). It occupies the object position and
preserves transitivity, and is formally distinct from the reflexive
"sebja" (себя). The first element "drug" stays uninflected (nominative)
while "druga" takes the case assigned by the verb.

The verbal postfix "-sja" (-ся) additionally carries reflexive-identical
reciprocal uses (monovalent; [nordlinger-2023] ex. 31).
-/

namespace Russian.Reciprocals

open Pronoun Reciprocal

/-- друг друга *drug druga* — bipartite reciprocal 'other other-ACC'
    ([nordlinger-2023] ex. 9). -/
def drugDruga : Marker :=
  { form := "drug druga", script := some "друг друга"
  , strategy := .bipartiteNP }

/-- -ся *-sja* — verbal postfix, reflexive-identical reciprocal uses
    ([nordlinger-2023] ex. 31). -/
def sja : Marker :=
  { form := "-sja", script := some "-ся", strategy := .verbalAffix
  , readings := [.reciprocal, .reflexive] }

/-- себя *sebja* — reflexive pronoun (for contrast). -/
def sebja : PersonalPronoun :=
  { form := "sebja", script := some "себя"
  , person := some .third }

/-- Russian reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    drugDruga.form ≠ sebja.form := by decide

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [drugDruga, sja]

end Russian.Reciprocals
