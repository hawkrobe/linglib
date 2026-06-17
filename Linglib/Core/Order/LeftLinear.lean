import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Interval.Set.Basic

/-!
# Left-linear orders

A partial order is **left-linear** when the predecessors of every element are linearly
ordered: `a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a`. Equivalently, every principal down-set `Iic m`
is a chain. This is the order-theoretic notion of a *tree*: the order may branch upward
but never downward.

Left-linearity is the shared kernel of two linglib substrates: the **Connected Ancestor
Condition** of [barker-pullum-1990] syntactic trees (`Core.Order.TreeOrder`) and the
**no-backward-branching** axiom of Prior–Thomason branching time. Both consume
`IsLeftLinear`; "ancestors are linearly ordered" (c-command) and "the past is linear"
(branching time) are literally the same statement, `IsLeftLinear.isChain_Iio`.

## Main definitions

* `IsLeftLinear M` — the predecessors of every element are linearly ordered.

## Main results

* `IsLeftLinear.isChain_Iic`, `IsLeftLinear.isChain_Iio` — every principal down-set is a chain.
-/

/-- A partial order is **left-linear** when the predecessors of every element are linearly
ordered (no backward branching). The order-theoretic notion of a tree order. -/
class IsLeftLinear (M : Type*) [PartialOrder M] : Prop where
  /-- The predecessors of any element are pairwise comparable. -/
  comparable_of_le_common : ∀ ⦃a b c : M⦄, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

namespace IsLeftLinear

variable {M : Type*} [PartialOrder M] [IsLeftLinear M]

/-- In a left-linear order the principal down-set `Iic m` is a chain. -/
theorem isChain_Iic (m : M) : IsChain (· ≤ ·) (Set.Iic m) := by
  intro a ha b hb _
  exact comparable_of_le_common (Set.mem_Iic.mp ha) (Set.mem_Iic.mp hb)

/-- In a left-linear order the strict past `Iio m` is a chain: the predecessors of any
moment are linearly ordered. -/
theorem isChain_Iio (m : M) : IsChain (· ≤ ·) (Set.Iio m) := by
  intro a ha b hb _
  exact comparable_of_le_common (le_of_lt (Set.mem_Iio.mp ha)) (le_of_lt (Set.mem_Iio.mp hb))

end IsLeftLinear
