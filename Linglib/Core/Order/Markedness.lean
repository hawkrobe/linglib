import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Markedness cutoffs on a scale

The order-theoretic core of differential-marking cutoffs, generic over any
scale (any `[Preorder S]`). A cutoff marks one end of the scale; the marked
region is an `Set.Ici`/`Set.Iic`, hence an upper/lower set — the "staircase"
monotonicity ([aissen-2003]) that every prominence scale (animacy,
definiteness, person, …) shares. Stated once here over the order **mixin**,
so each scale instantiates it rather than re-proving by `decide`.

## Main declarations

* `Core.Order.atOrAbove` / `atOrBelow` — the cutoff predicates (`c ≤ ·` / `· ≤ c`)
* `Core.Order.atOrAbove_isUpperSet` / `atOrBelow_isLowerSet` — monotonicity,
  for any scale
-/

namespace Core.Order

variable {S : Type*}

/-- The "marked above a cutoff" predicate on a scale: at or above `c`. The
    prominent-end cutoff shared by every differential-marking scale. -/
def atOrAbove [Preorder S] (c s : S) : Prop := c ≤ s

/-- The "marked below a cutoff" predicate: at or below `c` (the anti-monotone
    cutoff, for high-default roles). -/
def atOrBelow [Preorder S] (c s : S) : Prop := s ≤ c

/-- **Marking the prominent end is monotone**: the marked region of an
    `atOrAbove` cutoff is an upper set, for ANY scale. Replaces per-scale
    `decide` proofs of the staircase property. -/
theorem atOrAbove_isUpperSet [Preorder S] (c : S) :
    IsUpperSet {s | atOrAbove c s} := fun _ _ hab h => le_trans h hab

/-- Marking the non-prominent end is anti-monotone: a lower set, any scale. -/
theorem atOrBelow_isLowerSet [Preorder S] (c : S) :
    IsLowerSet {s | atOrBelow c s} := fun _ _ hab h => le_trans hab h

end Core.Order
