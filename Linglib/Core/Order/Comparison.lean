import Mathlib.Order.Interval.Set.Basic
import Linglib.Core.Order.StrictBounds

/-!
# Core/Scales/Comparison.lean — reified degree comparison

`Comparison` reifies the five ways a measured value relates to a threshold —
`=`, `≥`, `>`, `≤`, `<` — as data (cf. core `Ordering`, reified for `compare`).
It is the shared, theory-neutral primitive behind numeral modifiers, measure
phrases, and (the measure-derived case of) gradable comparatives, per the
joint degree-semantic treatment of [kennedy-2015] and [rett-2014].

It interprets two ways, both bottoming out in mathlib's order API so downstream
proofs reduce into `Set.mem_Ici` & friends rather than a bespoke lemma set:

* `Comparison.rel`      — the order relation (`[kennedy-2015]`'s `REL`).
* `Comparison.interval` — the order-interval (`Set.Ici`/`Ioi`/`Iic`/`Iio`/`{·}`).
* `Comparison.over μ n` — the predication `μ ⁻¹' (c.interval n)`: the entities
  whose measure lands in the interval. Bare cardinals are `over .eq id`, measure
  phrases `over c μ` for a `MeasureFn`, classifier counting `over .eq (atom-count)`.
* `Comparison.overSet μ Δ` — the *set-standard* generalization `μ ⁻¹' (c.bounds Δ)`:
  the entities whose measure bounds the whole standard set `Δ`. The point predication
  `over` is the singleton case (`overSet_singleton`); this is the order-theoretic core
  of [hoeksema-1983]'s S-comparative, with the binary NP-comparative its singleton face.

## Main declarations

* `Core.Order.Comparison` — the reified comparison.
* `Comparison.isStrict` — Class A (`>`,`<`) vs. non-strict (`=`,`≥`,`≤`).
* `Comparison.over` / `Comparison.overSet` — point- and set-standard predications.
* `Comparison.boundary_mem` — Class A/B as interval-endpoint membership.
-/

namespace Core.Order

/-- [kennedy-2015]'s `REL` reified: the relation a degree modifier draws
    between a measured value and a threshold. -/
inductive Comparison where
  /-- Exact / bare: `μ x = n`. -/
  | eq
  /-- "At least `n`": `μ x ≥ n`. -/
  | ge
  /-- "More than `n`": `μ x > n`. -/
  | gt
  /-- "At most `n`": `μ x ≤ n`. -/
  | le
  /-- "Fewer than `n`": `μ x < n`. -/
  | lt
  deriving DecidableEq, Repr, Inhabited

/-- Strict (Class A: `>`, `<`) vs. non-strict (bare `=`, Class B `≥`, `≤`). The
    modifier-level Class A/B split ([geurts-nouwen-2007], [nouwen-2010])
    is `isStrict` restricted to the four modified forms. -/
def Comparison.isStrict : Comparison → Prop
  | .gt | .lt => True
  | _         => False

instance : DecidablePred Comparison.isStrict := fun c => by
  cases c <;> unfold Comparison.isStrict <;> infer_instance

/-- The order relation a `Comparison` stands for. -/
def Comparison.rel {α : Type*} [Preorder α] : Comparison → α → α → Prop
  | .eq => (· = ·) | .ge => (· ≥ ·) | .gt => (· > ·)
  | .le => (· ≤ ·) | .lt => (· < ·)

/-- The order-interval a comparison selects, in mathlib terms:
    `{n}` / `[n,∞)` / `(n,∞)` / `(-∞,n]` / `(-∞,n)`. -/
def Comparison.interval {α : Type*} [Preorder α] : Comparison → α → Set α
  | .eq => fun n => {n}
  | .ge => Set.Ici
  | .gt => Set.Ioi
  | .le => Set.Iic
  | .lt => Set.Iio

/-- **The unifying predication**: the entities whose measure `μ` lands in the
    comparison's interval. The measure varies — `id` for bare cardinals, a
    dimensional `MeasureFn` for measure phrases, an atom-count for classifiers. -/
def Comparison.over {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (n : α) : Set E :=
  μ ⁻¹' c.interval n

@[simp] theorem Comparison.mem_interval {α : Type*} [Preorder α]
    (c : Comparison) (a n : α) : a ∈ c.interval n ↔ c.rel a n := by
  cases c <;> simp [Comparison.interval, Comparison.rel]

@[simp] theorem Comparison.mem_over {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (n : α) (x : E) :
    x ∈ c.over μ n ↔ c.rel (μ x) n := by
  simp [Comparison.over]

instance Comparison.relDecidable {α : Type*} [Preorder α] [DecidableEq α] [DecidableLE α]
    [DecidableLT α] (c : Comparison) (a n : α) : Decidable (c.rel a n) := by
  cases c <;> simp only [Comparison.rel, ge_iff_le, gt_iff_lt] <;> infer_instance

instance Comparison.overDecidable {E α : Type*} [Preorder α] [DecidableEq α] [DecidableLE α]
    [DecidableLT α] (c : Comparison) (μ : E → α) (n : α) (x : E) : Decidable (x ∈ c.over μ n) :=
  decidable_of_iff _ (Comparison.mem_over c μ n x).symm

/-- **Class A/B is interval-endpoint membership.** A non-strict comparison
    (bare `=`, Class B `≥`/`≤`) keeps the boundary `n`; a strict one (Class A
    `>`/`<`) drops it — the whole Class A/B distinction
    ([geurts-nouwen-2007], [nouwen-2010]) in one lemma. -/
@[simp] theorem Comparison.boundary_mem {α : Type*} [Preorder α]
    (c : Comparison) (n : α) : n ∈ c.interval n ↔ ¬ c.isStrict := by
  cases c <;> simp [Comparison.interval, Comparison.isStrict]

/-! ### Set-standard comparison

The than-clause of a comparative supplies not a point but a *set* of degrees.
`Comparison.bounds` lifts `Comparison.interval` from a point `n` to a standard set
`Δ` — the (strict) upper/lower bounds matching the comparison's relation — and
`Comparison.overSet` is the corresponding measure-pullback predication. The point
predication `over` is exactly the singleton case (`overSet_singleton`). -/

/-- The standard-set a comparison imposes: the bounds of `Δ` matching the
comparison's relation (`upperBounds`/`strictUpperBounds`/… per case). Generalizes
`Comparison.interval` from a point `n` (≡ `{n}`) to a standard set `Δ`. -/
def Comparison.bounds {α : Type*} [Preorder α] : Comparison → Set α → Set α
  | .eq => fun Δ => {x | ∀ a ∈ Δ, x = a}
  | .ge => upperBounds
  | .gt => strictUpperBounds
  | .le => lowerBounds
  | .lt => strictLowerBounds

/-- **Set-standard predication**: the entities whose measure bounds the whole
standard set `Δ`. The set-standard generalization of `Comparison.over` and the
order-theoretic core of [hoeksema-1983]'s S-comparative; the binary NP-comparative
is the singleton case (`overSet_singleton`). -/
def Comparison.overSet {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (Δ : Set α) : Set E :=
  μ ⁻¹' c.bounds Δ

/-- `bounds` at a singleton standard collapses to the point `interval`. -/
theorem Comparison.bounds_singleton {α : Type*} [Preorder α] (c : Comparison) (n : α) :
    c.bounds {n} = c.interval n := by
  cases c
  case eq =>
    ext x; simp only [Comparison.bounds, Comparison.interval, Set.mem_setOf_eq,
      Set.mem_singleton_iff, forall_eq]
  case ge => simp only [Comparison.bounds, Comparison.interval]; exact upperBounds_singleton
  case gt => simp only [Comparison.bounds, Comparison.interval, strictUpperBounds_singleton]
  case le => simp only [Comparison.bounds, Comparison.interval]; exact lowerBounds_singleton
  case lt => simp only [Comparison.bounds, Comparison.interval, strictLowerBounds_singleton]

@[simp] theorem Comparison.mem_overSet {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (Δ : Set α) (x : E) :
    x ∈ c.overSet μ Δ ↔ μ x ∈ c.bounds Δ := Iff.rfl

/-- **The NP ⊂ S bridge**: the set-standard predication at a singleton standard is
the point predication. Makes [hoeksema-1983]'s NP↔S equivalence definitional. -/
@[simp] theorem Comparison.overSet_singleton {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (n : α) : c.overSet μ {n} = c.over μ n := by
  simp only [Comparison.overSet, Comparison.over, Comparison.bounds_singleton]

/-! ### Threshold and measure monotonicity

The shared content of every threshold-semantics face (Kennedy positive
form, CSW positive region, credence thresholds): raising a non-strict
lower threshold shrinks the extension, raising the measure preserves
membership, and on a linear order the positive/negative poles are
complementary and comparison reduces to a separating threshold (Klein). -/

section ThresholdMonotone

variable {E α : Type*} [Preorder α] (μ : E → α)

/-- Raising an `at least` threshold shrinks the extension. -/
theorem Comparison.antitone_ge_over : Antitone (Comparison.ge.over μ) :=
  fun _ _ h _ hx => le_trans h hx

/-- Raising a `more than` threshold shrinks the extension. -/
theorem Comparison.antitone_gt_over : Antitone (Comparison.gt.over μ) :=
  fun _ _ h _ hx => lt_of_le_of_lt h hx

/-- Raising an `at most` threshold grows the extension. -/
theorem Comparison.monotone_le_over : Monotone (Comparison.le.over μ) :=
  fun _ _ h _ hx => le_trans hx h

/-- Raising a `less than` threshold grows the extension. -/
theorem Comparison.monotone_lt_over : Monotone (Comparison.lt.over μ) :=
  fun _ _ h _ hx => lt_of_lt_of_le hx h

/-- Membership in an `at least` extension transports up the measure. -/
theorem Comparison.mem_ge_over_of_le {θ : α} {x y : E}
    (hx : x ∈ Comparison.ge.over μ θ) (hxy : μ x ≤ μ y) :
    y ∈ Comparison.ge.over μ θ :=
  le_trans hx hxy

end ThresholdMonotone

section ThresholdLinear

variable {E α : Type*} [LinearOrder α] (μ : E → α)

/-- Polarity duality: clearing the threshold is exactly not falling
    below it. -/
theorem Comparison.mem_ge_over_iff_not_mem_lt_over {θ : α} {x : E} :
    x ∈ Comparison.ge.over μ θ ↔ x ∉ Comparison.lt.over μ θ := by
  simp [Comparison.mem_over, Comparison.rel, not_lt]

/-- The Klein reduction: strict comparison holds iff some threshold
    separates the two measures. -/
theorem Comparison.lt_iff_separating_threshold {x y : E} :
    μ y < μ x ↔ ∃ θ, x ∈ Comparison.ge.over μ θ ∧ y ∉ Comparison.ge.over μ θ := by
  constructor
  · exact fun h => ⟨μ x, le_refl _, not_le.mpr h⟩
  · rintro ⟨θ, hx, hy⟩
    exact lt_of_lt_of_le (not_le.mp hy) hx

end ThresholdLinear

end Core.Order
