import Linglib.Syntax.Category.Pronoun.Reflexive
import Linglib.Syntax.Reciprocal

/-!
# Icelandic Reciprocal Fragment
[nordlinger-2023]

Icelandic uses a bipartite NP strategy: "hvort annað" ('each other',
neuter forms as in [nordlinger-2023] ex. 17a), where each part
independently inflects for case — the quantifier agrees with the
antecedent while the *annað* part takes the case assigned by its
argument position ([hurst-nordlinger-2021]).

This is a bivalent strategy: the bipartite NP fills the object position,
preserving transitivity. Formally distinct from the reflexive "sig".

[nordlinger-2023] ex. 17 (citing [hurst-nordlinger-2021]).
-/

namespace Icelandic.Reciprocals

open Pronoun Reciprocal

/-- hvort annað — bipartite reciprocal NP 'each other' (neuter citation
    forms; both parts inflect independently for case and gender). -/
def hvorAnnad : Marker :=
  { form := "hvort annað", strategy := .bipartiteNP }

/-- sig — reflexive pronoun (for contrast). -/
-- UNVERIFIED: *sig* is also bound at a distance out of subjunctive clauses; the role that
-- licenses it there is not recorded.
def sig : ReflexivePronoun :=
  { form := "sig", person := some .third }

/-- Icelandic reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    hvorAnnad.form ≠ sig.form := by decide

/-- Marker inventory. -/
def markers : List Marker := [hvorAnnad]

end Icelandic.Reciprocals
