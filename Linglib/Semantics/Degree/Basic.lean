import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Bounds.Basic
import Linglib.Core.Order.Comparison
import Linglib.Semantics.Degree.Defs
import Linglib.Core.Order.Boundedness

/-!
# Degree comparison: the point-standard core
[kennedy-1999] [rett-2026] [schwarzschild-2008] [von-stechow-1984] [hoeksema-1983]

Comparative semantics shared across all degree frameworks: the binary
`comparativeSem` / `equativeSem`, antonymy as scale reversal, and
downward-entailingness of *than*-clauses. Both binary comparators are
measure-pullback predications of the reified `Core.Order.Comparison`
(`over` at a point standard, `overSet` at a set standard);
`comparativeSem_positive_eq_over` makes that an identity. The set-of-degrees
S-comparative ([hoeksema-1983]) *is* `Comparison.gt.overSet μ` directly — there is
no separate clausal-comparison definition; its properties are stated about `overSet`
here (anti-additivity) and reuse the `Comparison.overSet`/`over` API for the rest.
Framework-specific content for [rett-2026] (MAX, ambidirectionality, manner
implicature) lives in `Studies/Rett2026.lean`; [hoeksema-1983]'s polarity-asymmetry
consumers in `Studies/Hoeksema1983.lean`.

## Main declarations

* `comparativeSem` / `equativeSem` — "A is Adj-er / as-Adj-as B" via a directed
  measure on a scale.
* `gtOverSet_isAntiAdditive` — the S-comparative `Comparison.gt.overSet μ`
  ([hoeksema-1983]) is anti-additive in its standard: the algebraic source of
  *than*-clause NPI licensing.
* `mem_gtOverSet_iff_subset_Iio` — the set-of-degrees comparative as `Set.Iio`
  interval inclusion (strict mirror of mathlib's `mem_upperBounds_iff_subset_Iic`),
  collapsing to the binary comparator at a singleton via `Comparison.overSet_singleton`.
* `gtOverSet_eq_singleton_of_isGreatest` — a than-clause with a greatest degree
  reduces to that degree ([bhatt-pancheva-2004], order-theoretic form).
* `maxComparative` — the max-quantified clausal comparative ([von-stechow-1984],
  [rullmann-1995]): independent matrix/than witness predicates over `thanDegrees`,
  with the unique-witness collapse `maxComparative_unique`.
* `taller_shorter_antonymy` — antonymy is argument swap plus direction reversal.
* `comparative_iff_Iic_ssubset` — comparison as extent inclusion ([kennedy-1999]).
* `antonymy_biconditional` / `not_crossExtentInclusion` — the antonymy
  biconditional derived from extent complementarity, and cross-polar anomaly
  as unsatisfiable extent inclusion ([kennedy-1999]).
-/

namespace Degree

open Core.Order (ScalePolarity Comparison maxOnScale maxOnScale_singleton maxOnScale_ge_eq
  maxOnScale_ge_atMost maxOnScale_atLeast_singleton)

/-! ### Comparative and equative semantics -/

section Direct
variable {Entity : Type*} {α : Type*} [Preorder α]

/-- Comparative semantics over a measure function ([kennedy-1999];
[rett-2026], [schwarzschild-2008]): "A is Adj-er than B" iff `μ a` exceeds
`μ b` on the directed scale. Only `[Preorder α]`
— connectedness-agnostic background orderings (CSW confidence states)
are in scope. -/
def comparativeSem (μ : Entity → α) (a b : Entity) (dir : ScalePolarity) : Prop :=
  match dir with
  | .positive => μ a > μ b
  | .negative => μ a < μ b

/-- Equative semantics: "A is as Adj as B" iff `μ a ≥ μ b` on the directed scale. -/
def equativeSem (μ : Entity → α) (a b : Entity) (dir : ScalePolarity) : Prop :=
  match dir with
  | .positive => μ a ≥ μ b
  | .negative => μ a ≤ μ b

/-- **Grounding**: the positive binary comparative is the strict-`>` point
predication of `Core.Order.Comparison` at the standard `μ b` — not a reinvention. -/
theorem comparativeSem_positive_eq_over (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ a ∈ Comparison.gt.over μ (μ b) := by
  simp only [comparativeSem, Comparison.mem_over, Comparison.rel]

/-- **Grounding**: the positive equative is the `≥` point predication of
`Core.Order.Comparison` at the standard `μ b`. -/
theorem equativeSem_positive_eq_over (μ : Entity → α) (a b : Entity) :
    equativeSem μ a b .positive ↔ a ∈ Comparison.ge.over μ (μ b) := by
  simp only [equativeSem, Comparison.mem_over, Comparison.rel]

/-- **MAX–direct bridge**: the direct comparison `μ a > μ b` is equivalent to
the MAX-based formulation. -/
theorem comparativeSem_eq_MAX {β : Type*} [LinearOrder β] (μ : Entity → β)
    (a b : Entity) :
    comparativeSem μ a b .positive ↔
      ∃ m ∈ maxOnScale .gt ({μ b} : Set β), μ a > m := by
  simp only [comparativeSem, maxOnScale_singleton, Set.mem_singleton_iff, exists_eq_left]

/-! ### Antonymy as scale reversal -/

/-- "A taller than B" ↔ "B shorter than A" — antonymy is argument swap plus
direction reversal. -/
theorem taller_shorter_antonymy (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ comparativeSem μ b a .negative :=
  Iff.rfl

/-- Equative antonymy: "A as tall as B" ↔ "B as short as A". -/
theorem equative_antonymy (μ : Entity → α) (a b : Entity) :
    equativeSem μ a b .positive ↔ equativeSem μ b a .negative :=
  Iff.rfl

end Direct

/-! ### Boundary dependence -/

section Boundary
variable {α : Type*} [LinearOrder α]

/-- The comparative depends only on the boundary `μ_b`. -/
theorem comparative_boundary (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale .ge {d | d ≤ μ_b}, μ_a > m) ↔ μ_a > μ_b := by
  rw [maxOnScale_ge_atMost]
  simp only [Set.mem_singleton_iff, exists_eq_left]

/-- The equative depends only on the boundary `μ_b`. -/
theorem equative_boundary (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale .ge {d | d ≤ μ_b}, μ_a ≥ m) ↔ μ_a ≥ μ_b := by
  rw [maxOnScale_ge_atMost]
  simp only [Set.mem_singleton_iff, exists_eq_left]

end Boundary

/-! ### Comparison as extent inclusion

Kennedy's positive/negative extents are `Set.Iic (μ x)` / `Set.Ioi (μ x)`
directly ([kennedy-1999]); the binary comparator equals strict extent
inclusion, and antonymy follows from extent complementarity rather than
being stipulated. Boundary convention: the paper's eqs (30)–(31) define both
extents with `≤` (a cover); the strict `Ioi` here is a strict partition, and
the antonymy biconditional (eq (54)) is convention-independent. -/

section Extent

/-- Cross-polar inclusion: one entity's positive extent inside another's
negative extent — the LF a cross-polar equative ("as tall as Lee is short")
would assign ([kennedy-1999]). -/
def crossExtentInclusion {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  Set.Iic (μ a) ⊆ Set.Ioi (μ b)

variable {Entity D : Type*} [LinearOrder D]

/-- Bridge: the atomic S-comparative `Comparison.gt.overSet μ {μ b}` coincides with
the binary `comparativeSem` on a `LinearOrder`. The set-of-degrees schema strictly
generalizes the binary comparator, collapsing at a singleton via
`Comparison.overSet_singleton`. -/
theorem gtOverSet_atomic_eq_comparativeSem (μ : Entity → D) (a b : Entity) :
    a ∈ Comparison.gt.overSet μ {μ b} ↔ comparativeSem μ a b .positive := by
  rw [Comparison.overSet_singleton, ← comparativeSem_positive_eq_over]

/-- "A is taller than B" iff A's positive extent (`Set.Iic (μ a)`,
[kennedy-1999]) strictly contains B's. -/
theorem comparative_iff_Iic_ssubset (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ Set.Iic (μ b) ⊂ Set.Iic (μ a) :=
  Set.Iic_ssubset_Iic.symm

/-- "A taller than B" iff "B shorter than A" on the negative extents
(`Set.Ioi`), derived rather than stipulated ([kennedy-1999]). -/
theorem comparative_iff_Ioi_ssubset (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ Set.Ioi (μ a) ⊂ Set.Ioi (μ b) :=
  Set.Ioi_ssubset_Ioi_iff.symm

/-- Antonymy biconditional ([kennedy-1999] eq (54)): "A is taller than B" iff
"B is shorter than A", derived from extent complementarity. -/
theorem antonymy_biconditional (μ : Entity → D) (a b : Entity) :
    Set.Iic (μ b) ⊂ Set.Iic (μ a) ↔ Set.Ioi (μ a) ⊂ Set.Ioi (μ b) :=
  (comparative_iff_Iic_ssubset μ a b).symm.trans (comparative_iff_Ioi_ssubset μ a b)

/-- Weak-inclusion antonymy: the Galois-antitone face of the biconditional. -/
theorem extent_galois_antitone (μ : Entity → D) (a b : Entity) :
    Set.Iic (μ a) ⊆ Set.Iic (μ b) ↔ Set.Ioi (μ b) ⊆ Set.Ioi (μ a) :=
  Set.Iic_subset_Iic.trans Set.Ioi_subset_Ioi_iff.symm

/-- Cross-polar inclusion never holds on a linear order — the lattice-algebraic
shadow of [kennedy-1999]'s sortal cross-polar anomaly argument (§3.1.7). -/
theorem not_crossExtentInclusion (μ : Entity → D) (a b : Entity) :
    ¬ crossExtentInclusion μ a b :=
  fun h => absurd (h (min_le_left (μ a) (μ b))) (not_lt.mpr (min_le_right _ _))

end Extent

/-! ### Strengthened, negated, and extent-theoretic equatives
[kennedy-2007] [rett-2020] [schwarzschild-2008] [thomas-deo-2020]

The literal equative is "at least as" (`equativeSem .positive`); the "exactly
as" reading is derived by scalar implicature (choosing *as tall as* over the
stronger *taller than*). A granularity-based alternative is in
`Degree.Granularity`. -/

section Equative
variable {Entity D : Type*}

/-- Equative strengthened semantics: "A is as tall as B" iff `μ a = μ b` — the
"exactly as" reading, derived by implicature. -/
def equativeStrengthened [Preorder D] (μ : Entity → D) (a b : Entity) : Prop :=
  μ a = μ b

/-- The strengthened reading entails the literal `≥` reading. -/
theorem equativeStrengthened_entails_sem [LinearOrder D] (μ : Entity → D) (a b : Entity)
    (h : equativeStrengthened μ a b) : equativeSem μ a b .positive :=
  le_of_eq h.symm

/-- Negated equative: "A is not as tall as B" iff `μ a < μ b`. -/
def negatedEquative [LinearOrder D] (μ : Entity → D) (a b : Entity) : Prop :=
  μ a < μ b

/-- Negated equative is the negation of the literal equative. -/
theorem negatedEquative_iff_not_sem [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negatedEquative μ a b ↔ ¬ equativeSem μ a b .positive := by
  simp only [negatedEquative, equativeSem, ge_iff_le, not_le]

/-- Equative as positive extent inclusion ([kennedy-1999]): "A is as tall as B"
iff every degree B has (`Set.Iic (μ b)`), A also has. -/
theorem equativeSem_iff_Iic_subset [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    equativeSem μ a b .positive ↔ Set.Iic (μ b) ⊆ Set.Iic (μ a) :=
  Set.Iic_subset_Iic.symm

/-- Equative antonymy on negative extents: "A is as tall as B" iff "B is as
short as A" (`Set.Ioi` inclusion in the reversed direction). -/
theorem equativeSem_iff_Ioi_subset [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    equativeSem μ a b .positive ↔ Set.Ioi (μ a) ⊆ Set.Ioi (μ b) :=
  (equativeSem_iff_Iic_subset μ a b).trans (extent_galois_antitone μ b a)

/-- Negated equative as strict extent inclusion: B has strictly more degrees
than A. -/
theorem negatedEquative_iff_Iic_ssubset [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negatedEquative μ a b ↔ Set.Iic (μ a) ⊂ Set.Iic (μ b) :=
  Set.Iic_ssubset_Iic.symm

end Equative

/-! ### Subcomparatives
[schwarzschild-wilkinson-2002] -/

/-- Subcomparative ("longer than it is wide"): two commensurable measure
functions compared in shared units. -/
def subcomparative {Entity D : Type*} [LinearOrder D]
    (μ₁ μ₂ : Entity → D) (a b : Entity) : Prop :=
  μ₁ a > μ₂ b

end Degree
