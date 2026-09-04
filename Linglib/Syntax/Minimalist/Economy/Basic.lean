import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Tactic.DeriveFintype

/-!
# Derivational economy

Economy of derivation ([chomsky-1991], [chomsky-1995]) compares the derivations that converge on
the same string with the same interpretation and keeps the least costly. A cost is a count per
dimension: the lexical items drawn and the Merge operations, which are the distinct terms of the
object built, its lexical leaves and its internal vertices each once, so that a shared constituent
is built once; and the Agree operations and applications of ellipsis that
[citko-gracanin-yuksek-2025] weigh alongside them. Costs are ordered pointwise: a derivation is
more economical than another when it is no worse on every dimension and better on one. The order
is well-founded (Dickson's lemma, `Pi.wellFoundedLT`), so every reference set has a winner
(`WellFoundedLT.exists_minimal`). The cost of a planar object is read off its terms by
`Minimalist.planarCost` in `Linearization/Chain.lean`.

## Main definitions

* `CostDimension`, `DerivationCost`: the dimensions and a count per dimension.

## References

* [N. Chomsky, *Some notes on economy of derivation and representation* (1991)][chomsky-1991]
* [N. Chomsky, *The Minimalist Program* (1995)][chomsky-1995]
* [B. Citko and M. Gračanin-Yuksek, *Economy in PF reduction* (2025)][citko-gracanin-yuksek-2025]
-/

namespace Minimalist

/-- The dimensions of derivational cost. -/
inductive CostDimension
  | lexicalItems
  | mergeOps
  | agreeOps
  | ellipsisOps
  deriving DecidableEq, Fintype, Repr

/-- The cost of a derivation: a count per dimension, ordered pointwise. -/
abbrev DerivationCost := CostDimension → ℕ

instance : DecidableLE DerivationCost := λ a b => inferInstanceAs (Decidable (∀ i, a i ≤ b i))

instance : DecidableLT DerivationCost := λ a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

end Minimalist
