module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs

/-!
# Stratal Optimality Theory

Stratal OT evaluates phonology cyclically, at successive levels of morphological structure (stem,
word, phrase), the output of each level being the input to the next. Each level, or stratum, has
its own constraint ranking, and the same constraint can be ranked differently at different strata.
A stratum's ranking is its constraint order, a list of labels most dominant first, which
`OptimalityTheory.Tableau.ofOrder` evaluates. One constraint outranks another at a stratum when it
comes earlier in the order, `[a, b] <+ order`, which requires both to be active there.

## Main definitions

* `OptimalityTheory.Stratal.Reranked`: the reversal of a domination between two strata.

## References

* [kiparsky-2000]
-/

@[expose] public section

namespace OptimalityTheory.Stratal

open List

variable {L : Type*}

/-- `a` and `b` are reranked between the strata with orders `r₁` and `r₂` when `a` outranks `b`
in `r₁` and `b` outranks `a` in `r₂`. -/
def Reranked (a b : L) (r₁ r₂ : List L) : Prop := [a, b] <+ r₁ ∧ [b, a] <+ r₂

instance [DecidableEq L] (a b : L) (r₁ r₂ : List L) : Decidable (Reranked a b r₁ r₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

end OptimalityTheory.Stratal
