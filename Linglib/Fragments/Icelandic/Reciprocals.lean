import Linglib.Syntax.Category.Pronoun.Reflexive
import Linglib.Syntax.Reciprocal

/-!
# Icelandic reciprocals

Icelandic marks reciprocity with the two-part noun phrase *hvort annað* 'each other', cited in
its neuter forms as in [nordlinger-2023]'s (17a). The noun phrase fills the object position, so
the clause stays transitive, and its two parts inflect for case independently: the quantifier
*hvor* agrees in case with the antecedent, and *annað* takes the case of its argument position
([hurst-nordlinger-2021]). The reciprocal is distinct in form from the reflexive *sig*.

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [P. Hurst and R. Nordlinger, *An LFG Approach to Icelandic Reciprocal Constructions*
  (2021)][hurst-nordlinger-2021]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

namespace Icelandic.Reciprocals

open Reciprocal

/-- hvort annað — bipartite reciprocal NP 'each other' (neuter citation
    forms; both parts inflect independently for case and gender). -/
def hvorAnnad : Marker :=
  { form := "hvort annað", strategy := .bipartiteNP }

/-- sig — reflexive pronoun (for contrast). It is also bound from outside its clause, out of
    a subjunctive complement, by an antecedent that is a self ([sells-1987]). -/
def sig : ReflexivePronoun :=
  { form := "sig", person := some .third, requiredRole := some .self }

/-- Icelandic reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    hvorAnnad.form ≠ sig.form := by decide

/-- Marker inventory. -/
def markers : List Marker := [hvorAnnad]

end Icelandic.Reciprocals
