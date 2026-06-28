import Linglib.Phonology.Constraints.Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# List-lift constraint constructors

A constraint whose candidate is a *list* of forms — a paradigm, a candidate set,
a tier — typically scores by summing a per-element or per-ordered-pair cost over
the list. The two combinators here package that lift; the cost callback carries
all the theory-specific content, so the same lift serves markedness and
faithfulness alike.

`liftPairwise` is the symmetric all-ordered-pairs lift: it sums a comparison
over every pair of members. This is the generic operation behind
paradigm-uniformity / Base-Identity faithfulness — output-output identity summed
over related wordforms — but the combinator itself is theory-neutral; the
paper-specific anchoring disciplines live in their study files (`Studies/`).

## Main definitions

* `liftPerMember` — lift a per-element cost over the members of a `List`.
* `liftPairwise` — lift a per-ordered-pair cost over all pairs of a `List`.
-/

namespace Constraints

variable {α : Type*}

/-- Lift a per-element cost `viol` to a constraint over `List α` by summing it
    across the members. -/
def liftPerMember (viol : α → Nat) : Constraint (List α) :=
  fun xs => (xs.map viol).sum

/-- Lift a per-ordered-pair cost `compare` to a constraint over `List α` by
    summing it over every ordered pair — the symmetric all-pairs lift behind
    paradigm-uniformity faithfulness. -/
def liftPairwise (compare : α → α → Nat) : Constraint (List α) :=
  fun xs => ((xs.product xs).map (fun (a, b) => compare a b)).sum

end Constraints
