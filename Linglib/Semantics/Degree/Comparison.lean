module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Core.Order.StrictBounds

/-!
# Reified degree comparison

A `Comparison` is one of the five ways a measured value can relate to a threshold, `=`, `≥`, `>`,
`≤` and `<`, kept as data so that numeral modifiers, measure phrases and comparatives can share
it, as in the joint treatment of Kennedy and Rett. A comparison selects an order interval, and
`Comparison.over μ n` is the set of entities whose measure lies in it; `Comparison.overSet μ Δ`
generalizes the threshold to a set of degrees, the clausal standard of Hoeksema's comparative.
The point-standard comparative *a is taller than b* is `a ∈ Comparison.gt.over μ (μ b)`, that is
`μ b < μ a`, and the equative is `Comparison.ge`.

The antonym of a comparison is its order dual, `Comparison.dual`: *a is shorter than b* is the
dual comparison, which holds exactly when *b is taller than a* does and is the same comparison
read on the reversed scale, Kennedy's account of antonymy. Comparisons are invariant under a
strictly monotone change of scale.

## Main definitions

* `Degree.Comparison`, with `Comparison.rel`, `Comparison.interval` and `Comparison.over`.
* `Degree.Comparison.overSet`: the set-standard predication.
* `Degree.Comparison.dual`: the antonymous comparison.
* `Degree.maxOnScale`: Rett's order-sensitive maximality.
* `Degree.ThresholdSignificant`: some member of the comparison class clears the threshold, the
  presupposition Uegaki and Sudo attribute to degree constructions.

## Main results

* `Degree.Comparison.overSet_singleton`: a singleton standard is a point standard.
* `Degree.Comparison.rel_dual`, `Degree.Comparison.over_dual`: antonymy as argument exchange and
  as scale reversal.
* `Degree.Comparison.over_comp`: invariance under a strictly monotone change of scale.
* `Degree.Comparison.boundary_mem`: the Class A/B distinction as endpoint membership.

## References

* [kennedy-2015]
* [rett-2014]
* [hoeksema-1983]
* [kennedy-2007]
* [geurts-nouwen-2007]
* [nouwen-2010]
* [rett-2026]
* [uegaki-sudo-2019]
-/

@[expose] public section

namespace Degree

/-- A comparison is the relation a degree modifier draws between a measured value and a threshold,
[kennedy-2015]'s `REL` reified. -/
inductive Comparison where
  /-- The exact comparison `μ x = n` of a bare numeral. -/
  | eq
  /-- The comparison `μ x ≥ n` of *at least `n`*. -/
  | ge
  /-- The comparison `μ x > n` of *more than `n`*. -/
  | gt
  /-- The comparison `μ x ≤ n` of *at most `n`*. -/
  | le
  /-- The comparison `μ x < n` of *fewer than `n`*. -/
  | lt
  deriving DecidableEq, Repr, Inhabited

/-- A comparison is strict when it excludes its threshold, as `>` and `<` do; the Class A/B split of
modified numerals ([geurts-nouwen-2007], [nouwen-2010]) is strictness restricted to the four
modified forms. -/
def Comparison.isStrict : Comparison → Prop
  | .gt | .lt => True
  | _         => False

instance : DecidablePred Comparison.isStrict := fun c => by
  cases c <;> unfold Comparison.isStrict <;> infer_instance

/-- The order relation a `Comparison` stands for. -/
def Comparison.rel {α : Type*} [Preorder α] : Comparison → α → α → Prop
  | .eq => (· = ·) | .ge => (· ≥ ·) | .gt => (· > ·)
  | .le => (· ≤ ·) | .lt => (· < ·)

/-- The order interval a comparison selects is `{n}`, `[n, ∞)`, `(n, ∞)`, `(-∞, n]` or `(-∞, n)`. -/
def Comparison.interval {α : Type*} [Preorder α] : Comparison → α → Set α
  | .eq => fun n => {n}
  | .ge => Set.Ici
  | .gt => Set.Ioi
  | .le => Set.Iic
  | .lt => Set.Iio

/-- The predication of a comparison is the set of entities whose measure lies in its interval; the
measure is `id` for bare cardinals, a dimensioned measure for measure phrases, and an atom count for
classifiers. -/
def Comparison.over {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (n : α) : Set E :=
  μ ⁻¹' c.interval n

section

variable {α : Type*} [Preorder α] (a n : α)

@[simp] theorem Comparison.interval_eq : Comparison.eq.interval n = {n} := rfl
@[simp] theorem Comparison.interval_ge : Comparison.ge.interval n = Set.Ici n := rfl
@[simp] theorem Comparison.interval_gt : Comparison.gt.interval n = Set.Ioi n := rfl
@[simp] theorem Comparison.interval_le : Comparison.le.interval n = Set.Iic n := rfl
@[simp] theorem Comparison.interval_lt : Comparison.lt.interval n = Set.Iio n := rfl

@[simp] theorem Comparison.rel_eq : Comparison.eq.rel a n ↔ a = n := Iff.rfl
@[simp] theorem Comparison.rel_ge : Comparison.ge.rel a n ↔ n ≤ a := Iff.rfl
@[simp] theorem Comparison.rel_gt : Comparison.gt.rel a n ↔ n < a := Iff.rfl
@[simp] theorem Comparison.rel_le : Comparison.le.rel a n ↔ a ≤ n := Iff.rfl
@[simp] theorem Comparison.rel_lt : Comparison.lt.rel a n ↔ a < n := Iff.rfl

end

@[simp] theorem Comparison.mem_interval {α : Type*} [Preorder α]
    (c : Comparison) (a n : α) : a ∈ c.interval n ↔ c.rel a n := by
  cases c <;> simp [Comparison.interval, Comparison.rel]

/-- The interval of a comparison is convex. -/
instance Comparison.ordConnected_interval {α : Type*} [PartialOrder α] (c : Comparison) (n : α) :
    (c.interval n).OrdConnected := by
  cases c <;> simp only [interval_eq, interval_ge, interval_gt, interval_le, interval_lt] <;>
    infer_instance

/-- Over the identity measure a comparison selects its interval. -/
@[simp] theorem Comparison.over_id {α : Type*} [Preorder α] (c : Comparison) (n : α) :
    c.over id n = c.interval n := rfl

@[simp] theorem Comparison.mem_over {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (n : α) (x : E) :
    x ∈ c.over μ n ↔ c.rel (μ x) n := by
  simp [Comparison.over]

instance Comparison.relDecidable {α : Type*} [Preorder α] [DecidableEq α] [DecidableLE α]
    [DecidableLT α] (c : Comparison) (a n : α) : Decidable (c.rel a n) := by
  cases c <;> simp only [Comparison.rel, ge_iff_le, gt_iff_lt] <;> infer_instance

instance Comparison.intervalDecidable {α : Type*} [Preorder α] [DecidableEq α] [DecidableLE α]
    [DecidableLT α] (c : Comparison) (a n : α) : Decidable (a ∈ c.interval n) :=
  decidable_of_iff _ (Comparison.mem_interval c a n).symm

instance Comparison.overDecidable {E α : Type*} [Preorder α] [DecidableEq α] [DecidableLE α]
    [DecidableLT α] (c : Comparison) (μ : E → α) (n : α) (x : E) : Decidable (x ∈ c.over μ n) :=
  decidable_of_iff _ (Comparison.mem_over c μ n x).symm

/-- A comparison keeps its threshold exactly when it is not strict, so the Class A/B distinction
([geurts-nouwen-2007], [nouwen-2010]) is membership of the interval's endpoint. -/
@[simp] theorem Comparison.boundary_mem {α : Type*} [Preorder α]
    (c : Comparison) (n : α) : n ∈ c.interval n ↔ ¬ c.isStrict := by
  cases c <;> simp [Comparison.interval, Comparison.isStrict]

/-! ### Threshold significance

A degree construction whose threshold `θ C` depends on a comparison class `C` presupposes that
some member of the class exceeds the threshold; otherwise the construction draws no distinction
in the class. -/

/-- A threshold function `θ` is significant on the comparison class `C` when some member of `C`
measures above `θ C`. -/
def ThresholdSignificant {E α : Type*} [Preorder α] (μ : E → α) (θ : Set E → α)
    (C : Set E) : Prop :=
  (C ∩ Comparison.gt.over μ (θ C)).Nonempty

theorem thresholdSignificant_iff {E α : Type*} [Preorder α] {μ : E → α} {θ : Set E → α}
    {C : Set E} : ThresholdSignificant μ θ C ↔ ∃ y ∈ C, θ C < μ y :=
  ⟨fun ⟨y, hy, h⟩ ↦ ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ ↦ ⟨y, hy, h⟩⟩

/-! ### Set-standard comparison

The than-clause of a comparative supplies not a point but a *set* of degrees.
`Comparison.bounds` lifts `Comparison.interval` from a point `n` to a standard set
`Δ` — the (strict) upper/lower bounds matching the comparison's relation — and
`Comparison.overSet` is the corresponding measure-pullback predication. The point
predication `over` is exactly the singleton case (`overSet_singleton`). -/

/-- The bounds a comparison imposes on a standard set `Δ` are its upper, strict upper, lower or
strict lower bounds, generalizing `Comparison.interval` from a point to a set. -/
def Comparison.bounds {α : Type*} [Preorder α] : Comparison → Set α → Set α
  | .eq => fun Δ => {x | ∀ a ∈ Δ, x = a}
  | .ge => upperBounds
  | .gt => strictUpperBounds
  | .le => lowerBounds
  | .lt => strictLowerBounds

/-- The set-standard predication is the set of entities whose measure bounds the whole standard set
`Δ`, the order-theoretic core of [hoeksema-1983]'s clausal comparative. -/
def Comparison.overSet {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (Δ : Set α) : Set E :=
  μ ⁻¹' c.bounds Δ

/-- `bounds` at a singleton standard collapses to the point `interval`. -/
theorem Comparison.bounds_singleton {α : Type*} [Preorder α] (c : Comparison) (n : α) :
    c.bounds {n} = c.interval n := by
  cases c
  case eq =>
    ext x; simp only [Comparison.bounds, Comparison.interval, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, forall_eq]
  case ge => simp only [Comparison.bounds, Comparison.interval]; exact upperBounds_singleton
  case gt => simp only [Comparison.bounds, Comparison.interval, strictUpperBounds_singleton]
  case le => simp only [Comparison.bounds, Comparison.interval]; exact lowerBounds_singleton
  case lt => simp only [Comparison.bounds, Comparison.interval, strictLowerBounds_singleton]

@[simp] theorem Comparison.mem_overSet {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (Δ : Set α) (x : E) :
    x ∈ c.overSet μ Δ ↔ μ x ∈ c.bounds Δ := Iff.rfl

/-- At a singleton standard the set-standard predication is the point predication, so
[hoeksema-1983]'s phrasal and clausal comparatives coincide there. -/
@[simp] theorem Comparison.overSet_singleton {E α : Type*} [Preorder α]
    (c : Comparison) (μ : E → α) (n : α) : c.overSet μ {n} = c.over μ n := by
  simp only [Comparison.overSet, Comparison.over, Comparison.bounds_singleton]

/-! ### The antonymous comparison -/

/-- The dual of a comparison reads it on the reversed scale, turning `>` into `<` and `≥` into `≤`
and fixing `=`. -/
def Comparison.dual : Comparison → Comparison
  | .eq => .eq
  | .ge => .le
  | .gt => .lt
  | .le => .ge
  | .lt => .gt

@[simp] theorem Comparison.dual_eq : Comparison.eq.dual = .eq := rfl
@[simp] theorem Comparison.dual_ge : Comparison.ge.dual = .le := rfl
@[simp] theorem Comparison.dual_gt : Comparison.gt.dual = .lt := rfl
@[simp] theorem Comparison.dual_le : Comparison.le.dual = .ge := rfl
@[simp] theorem Comparison.dual_lt : Comparison.lt.dual = .gt := rfl

theorem Comparison.dual_involutive : Function.Involutive Comparison.dual := fun c ↦ by
  cases c <;> rfl

@[simp] theorem Comparison.dual_dual (c : Comparison) : c.dual.dual = c :=
  Comparison.dual_involutive c

/-- Antonymy preserves strictness, so *fewer than* is Class A as *more than* is. -/
@[simp] theorem Comparison.isStrict_dual (c : Comparison) : c.dual.isStrict ↔ c.isStrict := by
  cases c <;> exact Iff.rfl

section Dual

variable {E α : Type*} [Preorder α] (c : Comparison)

/-- The dual comparison exchanges its arguments, so *a is shorter than b* exactly when *b is
taller than a*. -/
theorem Comparison.rel_dual (a b : α) : c.dual.rel a b ↔ c.rel b a := by
  cases c <;> simp only [Comparison.dual, Comparison.rel, eq_comm]

/-- The dual comparison on a scale is the comparison on the dual scale. -/
theorem Comparison.rel_dual_toDual (a b : α) :
    c.dual.rel a b ↔ c.rel (OrderDual.toDual a) (OrderDual.toDual b) := by
  cases c <;> exact Iff.rfl

/-- The dual predication is the predication on the dual scale. -/
theorem Comparison.over_dual (μ : E → α) (n : α) :
    c.dual.over μ n = c.over (OrderDual.toDual ∘ μ) (OrderDual.toDual n) := by
  cases c <;> rfl

/-- The bounds of a standard set for the dual comparison are the bounds of the dual set for the
comparison on the dual scale. -/
theorem Comparison.bounds_dual (Δ : Set α) :
    c.dual.bounds Δ = OrderDual.toDual ⁻¹' c.bounds (OrderDual.toDual '' Δ) := by
  cases c <;> ext x <;>
    simp [Comparison.bounds, upperBounds, lowerBounds, strictUpperBounds, strictLowerBounds]

/-- The dual set-standard predication is the set-standard predication on the dual scale. -/
theorem Comparison.overSet_dual (μ : E → α) (Δ : Set α) :
    c.dual.overSet μ Δ = c.overSet (OrderDual.toDual ∘ μ) (OrderDual.toDual '' Δ) := by
  ext x
  simp only [Comparison.mem_overSet, Comparison.bounds_dual, Set.mem_preimage, Function.comp]

end Dual

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

/-- Clearing the threshold is exactly not falling below it. -/
theorem Comparison.mem_ge_over_iff_not_mem_lt_over {θ : α} {x : E} :
    x ∈ Comparison.ge.over μ θ ↔ x ∉ Comparison.lt.over μ θ := by
  simp [Comparison.mem_over, Comparison.rel, not_lt]

/-- When every degree is realized, raising an `at least` threshold strictly shrinks the
    extension. -/
theorem Comparison.strictAnti_ge_over (hμ : Function.Surjective μ) :
    StrictAnti (Comparison.ge.over μ) := by
  intro a b hab
  refine ⟨Comparison.antitone_ge_over μ hab.le, fun h => ?_⟩
  obtain ⟨w, rfl⟩ := hμ a
  exact not_le.2 hab (h (le_refl (μ w)))

/-- When every degree is realized, raising a `more than` threshold strictly shrinks the
    extension. -/
theorem Comparison.strictAnti_gt_over (hμ : Function.Surjective μ) :
    StrictAnti (Comparison.gt.over μ) := by
  intro a b hab
  refine ⟨Comparison.antitone_gt_over μ hab.le, fun h => ?_⟩
  obtain ⟨w, rfl⟩ := hμ b
  exact lt_irrefl _ (h hab)

/-- When every degree is realized, raising an `at most` threshold strictly grows the
    extension. -/
theorem Comparison.strictMono_le_over (hμ : Function.Surjective μ) :
    StrictMono (Comparison.le.over μ) := by
  intro a b hab
  refine ⟨Comparison.monotone_le_over μ hab.le, fun h => ?_⟩
  obtain ⟨w, rfl⟩ := hμ b
  exact not_le.2 hab (h (le_refl (μ w)))

/-- When every degree is realized, raising a `less than` threshold strictly grows the
    extension. -/
theorem Comparison.strictMono_lt_over (hμ : Function.Surjective μ) :
    StrictMono (Comparison.lt.over μ) := by
  intro a b hab
  refine ⟨Comparison.monotone_lt_over μ hab.le, fun h => ?_⟩
  obtain ⟨w, rfl⟩ := hμ a
  exact lt_irrefl _ (h hab)

/-- Strict comparison holds exactly when some threshold separates the two measures, Klein's
reduction of the comparative. -/
theorem Comparison.lt_iff_separating_threshold {x y : E} :
    μ y < μ x ↔ ∃ θ, x ∈ Comparison.ge.over μ θ ∧ y ∉ Comparison.ge.over μ θ := by
  constructor
  · exact fun h => ⟨μ x, le_refl _, not_le.mpr h⟩
  · rintro ⟨θ, hx, hy⟩
    exact lt_of_lt_of_le (not_le.mp hy) hx

/-- A comparison is invariant under a strictly monotone change of scale. -/
theorem Comparison.over_comp {β : Type*} [Preorder β] {f : α → β} (hf : StrictMono f)
    (c : Comparison) (n : α) : c.over (f ∘ μ) (f n) = c.over μ n := by
  ext x
  cases c <;> simp [Comparison.over, Comparison.interval, hf.lt_iff_lt, hf.le_iff_le,
    hf.injective.eq_iff]

end ThresholdLinear

/-! ### Scale-sensitive maximality

[rett-2026]: MAX_c(X) picks the element(s) of X that c-dominate all other members. For the
`<` scale (`.lt`) this is the GLB (earliest / smallest), for `>` (`.gt`) the LUB (latest /
largest). The same operator underlies both temporal connectives (*before* / *after*) and
degree comparatives. `maxOnScale_lt_eq` / `maxOnScale_ge_eq` / `maxOnScale_gt_eq` ground the
operator in mathlib's `IsLeast` / `IsGreatest`, and the interval evaluations are corollaries. -/

/-- Order-sensitive maximality, [rett-2026] (44), picks the elements of `X` that dominate every
other element under the comparison `c`. -/
def maxOnScale {α : Type*} [Preorder α] (c : Comparison) (X : Set α) : Set α :=
  { x | x ∈ X ∧ ∀ x' ∈ X, x' ≠ x → c.rel x x' }

/-- Maximality on a singleton returns the singleton, for any comparison. -/
theorem maxOnScale_singleton {α : Type*} [Preorder α] (c : Comparison) (x : α) :
    maxOnScale c {x} = {x} := by
  ext y
  simp only [maxOnScale, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl, _⟩; rfl
  · rintro rfl
    exact ⟨rfl, fun x' hx' hne => absurd hx' hne⟩

/-- Maximality under `≥` picks the greatest element. -/
theorem maxOnScale_ge_eq {α : Type*} [Preorder α] (X : Set α) :
    maxOnScale .ge X = {x | IsGreatest X x} := by
  ext x
  simp only [maxOnScale, Comparison.rel, Set.mem_ofPred_eq, IsGreatest,
    upperBounds, ge_iff_le]
  refine ⟨fun ⟨hx, hdom⟩ => ⟨hx, fun y hy => ?_⟩,
    fun ⟨hx, hub⟩ => ⟨hx, fun y hy _ => hub hy⟩⟩
  rcases eq_or_ne y x with rfl | hne
  · exact le_refl _
  · exact hdom y hy hne

/-- Maximality under `<` picks the least element, since on a partial order strictly dominating
the other elements of `X` on the `<` scale is being the least. -/
theorem maxOnScale_lt_eq {α : Type*} [PartialOrder α] (X : Set α) :
    maxOnScale .lt X = {x | IsLeast X x} := by
  ext x
  simp only [maxOnScale, Comparison.rel, Set.mem_ofPred_eq, IsLeast, lowerBounds]
  refine ⟨fun ⟨hx, hdom⟩ => ⟨hx, fun y hy => ?_⟩, fun ⟨hx, hlb⟩ => ⟨hx, fun y hy hne => ?_⟩⟩
  · rcases eq_or_ne y x with rfl | hne
    · exact le_refl _
    · exact (hdom y hy hne).le
  · exact lt_of_le_of_ne (hlb hy) (Ne.symm hne)

/-- Maximality under `>` picks the greatest element. -/
theorem maxOnScale_gt_eq {α : Type*} [PartialOrder α] (X : Set α) :
    maxOnScale .gt X = {x | IsGreatest X x} := by
  ext x
  simp only [maxOnScale, Comparison.rel, Set.mem_ofPred_eq, IsGreatest, upperBounds,
    gt_iff_lt]
  refine ⟨fun ⟨hx, hdom⟩ => ⟨hx, fun y hy => ?_⟩, fun ⟨hx, hub⟩ => ⟨hx, fun y hy hne => ?_⟩⟩
  · rcases eq_or_ne y x with rfl | hne
    · exact le_refl _
    · exact (hdom y hy hne).le
  · exact lt_of_le_of_ne (hub hy) hne

/-- Maximality under `<` on a closed interval is its left endpoint. -/
theorem maxOnScale_lt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale .lt { x : α | s ≤ x ∧ x ≤ f } = {s} := by
  rw [maxOnScale_lt_eq]
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨isLeast_Icc hsf, fun _ h => h.unique (isLeast_Icc hsf)⟩

/-- Maximality under `>` on a closed interval is its right endpoint. -/
theorem maxOnScale_gt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale .gt { x : α | s ≤ x ∧ x ≤ f } = {f} := by
  rw [maxOnScale_gt_eq]
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨isGreatest_Icc hsf, fun _ h => h.unique (isGreatest_Icc hsf)⟩

/-- A scalar construction `f` is ambidirectional at `B` when it returns the same result on `B` and
on its complement, as maximality does when it picks the same boundary from both; this is the
mechanism behind expletive negation. -/
def isAmbidirectional {α : Type*} (f : Set α → Prop) (B : Set α) : Prop :=
  f B ↔ f Bᶜ

end Degree
