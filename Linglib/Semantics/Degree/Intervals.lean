import Linglib.Semantics.Degree.Extent
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Degree.Comparative
import Mathlib.Order.Interval.Basic

/-!
# Schwarzschild's Interval Semantics
[schwarzschild-2005] [schwarzschild-2008] [schwarzschild-wilkinson-2002]

[schwarzschild-2008] reifies degrees as **intervals** on a scale rather than
points: "tall" is `[⊥, μ x]`, "short" is `[μ x, ⊤]`, and degree morphology
manipulates these intervals. Intervals are mathlib's `NonemptyInterval` (the same
type the time-interval substrate uses). The comparative asserts the matrix
interval extends past the standard's; subcomparatives compare intervals from
commensurable scales; differentials specify the interval gap.

## Main declarations

* `positiveInterval` / `negativeInterval` — the `[⊥, μ x]` / `[μ x, ⊤]` extents.
* `intervalComparative` — upper-bound comparison; *is* the consensus
  `comparativeSem` (`interval_eq_comparativeSem`).
* `subcomparative` — cross-dimensional comparison ([schwarzschild-wilkinson-2002]).
-/

namespace Degree.Intervals

open Degree

/-! ### Intervals as degrees -/

/-- The positive interval for `x`: `[⊥, μ x]` — the extent to which `x` is tall. -/
def positiveInterval {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (x : Entity) : NonemptyInterval D :=
  ⟨(⊥, μ x), bot_le⟩

/-- The negative interval for `x`: `[μ x, ⊤]` — the extent to which `x` is short
([buring-2007] §4: ⟦short⟧ = ⟦LITTLE tall⟧, which inverts the positive interval). -/
def negativeInterval {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (x : Entity) : NonemptyInterval D :=
  ⟨(μ x, ⊤), le_top⟩

/-! ### Comparative as interval comparison -/

/-- Schwarzschild's comparative: the matrix interval extends past the standard's,
i.e. its upper bound is greater. -/
def intervalComparative {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  (positiveInterval μ b).snd < (positiveInterval μ a).snd

/-- Schwarzschild's interval comparative **is** the consensus point comparative
([kennedy-1999], [rett-2026]): for positive intervals `[⊥, μ x]`, comparing upper
bounds is comparing degrees. -/
theorem interval_eq_comparativeSem {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) :
    intervalComparative μ a b ↔ comparativeSem μ a b .positive :=
  Iff.rfl

/-! ### Differential comparatives -/

/-- The differential interval `[μ b, μ a]` — the gap between standard and matrix
("A is d-much taller than B" specifies its extent). -/
def differentialInterval {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) (h : μ b ≤ μ a) : NonemptyInterval D :=
  ⟨(μ b, μ a), h⟩

/-! ### Subcomparatives -/

/-- Subcomparative ("longer than it is wide"): two **commensurable** scales
compared in shared units ([schwarzschild-wilkinson-2002]). -/
def subcomparative {Entity D : Type*} [LinearOrder D]
    (μ₁ μ₂ : Entity → D) (a b : Entity) : Prop :=
  μ₁ a > μ₂ b

/-! ### Bridge to extent functions -/

/-- The positive interval's membership is exactly `posExt`: `d ∈ [⊥, μ x]` iff
`d ∈ posExt μ x`. Connects Schwarzschild's intervals to the extent algebra. -/
theorem positiveInterval_iff_posExt {Entity D : Type*}
    [LinearOrder D] [BoundedOrder D] (μ : Entity → D) (x : Entity) (d : D) :
    (positiveInterval μ x).fst ≤ d ∧ d ≤ (positiveInterval μ x).snd ↔
      d ∈ posExt μ x := by
  simp [positiveInterval, posExt]

/-! ### Negative intervals and LITTLE -/

/-- LITTLE inverts the positive interval `[⊥, μ x]` into the negative interval
`[μ x, ⊤]` ([buring-2007] §4). -/
theorem little_inverts_interval {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (x : Entity) :
    negativeInterval μ x = ⟨((positiveInterval μ x).snd, ⊤), le_top⟩ :=
  rfl

/-- "Shorter than" via negative intervals: `a` is shorter than `b` iff `a`'s
negative interval reaches further down, i.e. `μ a < μ b`. -/
theorem negativeInterval_comparative {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) :
    (negativeInterval μ a).fst < (negativeInterval μ b).fst ↔ μ a < μ b :=
  Iff.rfl

/-- The negative interval starts at `μ x`. -/
theorem negativeInterval_membership {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (x : Entity) (d : D) :
    (negativeInterval μ x).fst ≤ d ↔ μ x ≤ d :=
  Iff.rfl

end Degree.Intervals
