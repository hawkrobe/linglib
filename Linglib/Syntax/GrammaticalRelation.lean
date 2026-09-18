import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.Interval.Finset.Defs

/-!
# Grammatical relations

The grammatical relations an argument bears to its clause, from the subject down to the object
of comparison, ordered by the relational hierarchy with the subject on top. Keenan and Comrie
established the chain as the Accessibility Hierarchy of relativization, and the same chain
orders the agreement controllers and the forward-looking centers of centering theory, the
latter as a coarsening (`Discourse.Centering.GrammaticalRole.ofRelation`).

## Main declarations

* `Syntax.GrammaticalRelation`: the six relations, a bounded linear order with the subject on
  top, lifted from `GrammaticalRelation.rank`.

## References

* [keenan-comrie-1977]
-/

namespace Syntax

/-- The grammatical relations of [keenan-comrie-1977]'s Accessibility Hierarchy,
subject > direct object > indirect object > oblique > genitive > object of comparison. -/
inductive GrammaticalRelation where
  | subject
  | directObject
  | indirectObject
  | oblique
  | genitive
  /-- The object of comparison, "the person [that I am taller than _]". -/
  | objComparison
  deriving DecidableEq, Repr, Fintype

namespace GrammaticalRelation

/-- The rank of a relation, higher for the more accessible. -/
def rank : GrammaticalRelation → ℕ
  | .subject => 5
  | .directObject => 4
  | .indirectObject => 3
  | .oblique => 2
  | .genitive => 1
  | .objComparison => 0

theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]

/-- The relational hierarchy, `p ≤ q` when `p` is no more accessible than `q`. -/
instance : LinearOrder GrammaticalRelation := LinearOrder.lift' rank rank_injective

/-- The subject is the top of the hierarchy, the object of comparison its bottom. -/
instance : BoundedOrder GrammaticalRelation where
  top := .subject
  le_top := by decide
  bot := .objComparison
  bot_le := by decide

instance : LocallyFiniteOrder GrammaticalRelation := Fintype.toLocallyFiniteOrder

end GrammaticalRelation

end Syntax
