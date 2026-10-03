module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Left-linear orders

A partial order is **left-linear** when the predecessors of every element are linearly
ordered: `a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a`. Equivalently, every principal down-set `Iic m`
is a chain. This is the order-theoretic notion of a tree: the order may branch upward but
never downward.

Linear orders are left-linear, and so is every rooted tree in the sense of
`Mathlib/Order/SuccPred/Tree.lean`: a `PredOrder` with archimedean predecessor is left-linear by
mathlib's `le_total_of_directed`. Branching-time frames, which need not have predecessors, assume
left-linearity directly.

## Main definitions

* `IsLeftLinear M`: the predecessors of every element are linearly ordered.

## Main results

* `IsLeftLinear.isChain_Iic`, `IsLeftLinear.isChain_Iio`: every principal down-set is a chain.
-/

@[expose] public section

/-- A partial order is **left-linear** when the predecessors of every element are linearly
ordered, so that it never branches backward. -/
class IsLeftLinear (M : Type*) [PartialOrder M] : Prop where
  /-- The predecessors of any element are pairwise comparable. -/
  comparable_of_le_common : ∀ ⦃a b c : M⦄, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

/-- A linear order is left-linear. -/
instance (priority := 100) {M : Type*} [LinearOrder M] : IsLeftLinear M :=
  ⟨fun a b _ _ _ ↦ le_total a b⟩

/-- A `PredOrder` with archimedean predecessor, such as a rooted tree, is left-linear. -/
instance (priority := 100) {M : Type*} [PartialOrder M] [PredOrder M] [IsPredArchimedean M] :
    IsLeftLinear M :=
  ⟨fun _ _ _ ha hb ↦ (le_total_of_directed ha hb).symm⟩

namespace IsLeftLinear

variable {M : Type*} [PartialOrder M] [IsLeftLinear M]

/-- In a left-linear order the principal down-set `Iic m` is a chain. -/
theorem isChain_Iic (m : M) : IsChain (· ≤ ·) (Set.Iic m) := by
  intro a ha b hb _
  exact comparable_of_le_common (Set.mem_Iic.mp ha) (Set.mem_Iic.mp hb)

/-- In a left-linear order the strict down-set `Iio m` is a chain. -/
theorem isChain_Iio (m : M) : IsChain (· ≤ ·) (Set.Iio m) := by
  intro a ha b hb _
  exact comparable_of_le_common (le_of_lt (Set.mem_Iio.mp ha)) (le_of_lt (Set.mem_Iio.mp hb))

end IsLeftLinear
