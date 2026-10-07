module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Order.Interval.Set.LinearOrder
public import Linglib.Core.Order.UpperLower.Closure
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Logic.Natural.Additivity

/-!
# Degree quantifiers

This file defines the denotations of degree phrases as quantifiers over degrees and their scope
relative to a quantifier over entities or worlds. A degree phrase says that the maximum of its
degree predicate lies in an interval, `MaxIn U P`; under a quantifier `Q` it scopes low, applied
to each entity's own degrees, or high, applied to `scopeDegrees Q μ`, the degrees at which `Q`
holds. Under `some` the degree set is the lower closure of the measures, the than-clause degree
set, and the max-quantified comparative `MaxComparative c` compares a matrix witness with its
greatest measure by the comparison `c`.

## Main definitions

* `MaxIn U P`: the greatest element of `P` lies in `U`.
* `scopeDegrees Q μ`: the degrees `d` such that `Q` holds of the entities measuring at least `d`.
* `LowScope 𝒟 Q μ`, `HighScope 𝒟 Q μ`: the degree quantifier `𝒟` under and over `Q`.
* `MaxComparative c P Q μ`: the max-quantified comparative, the equative at `c = .ge`.
* `AbsoluteSuperlative μ C x`: `x` measures above every other member of `C`.

## Main results

* `highScope_maxIn_iff_lowScope`: over a monotone quantifier on a finite domain, a degree
  quantifier at an upper set takes scope without truth-conditional effect.
* `not_isGreatest_scopeDegrees`: under an antitone quantifier the degree set has no maximum.
* `highScope_maxIn_singleton_every`, `highScope_maxIn_singleton_some`: the exact degree
  quantifier over `every` names the infimum of the measures and over `some` their greatest.
* `isGreatest_scopeDegrees_of_inf`: under a meet with an antitone quantifier the maximum is the
  other conjunct's.
* `maxComparative_iff_of_unique`: with unique witnesses the max-quantified comparative is direct
  measure comparison.

## References

* [heim-2001]
* [von-stechow-1984]
* [rullmann-1995]
* [hoeksema-1983]
* [bhatt-pancheva-2004]
* [heim-1999]
-/

@[expose] public section

namespace Degree

open NaturalLogic Quantifier Quantifier.GQ Set

variable {α D : Type*}

/-! ### Degree quantifiers and their scope -/

section Preorder
variable [Preorder D] {Q : NP α} {μ : α → D} {d : D}

/-- The greatest element of `P` lies in `U`. These are the degree quantifiers of [heim-2001],
*-er than `t`* at `U = Ioi t`, *less than `t`* at `Iio t`, *exactly `δ` -er than `t`* at
`{t + δ}`, and the equative at `Ici t`. -/
def MaxIn (U P : Set D) : Prop := ∃ m ∈ U, IsGreatest P m

theorem maxIn_singleton {P : Set D} {a : D} : MaxIn {a} P ↔ IsGreatest P a := exists_eq_left

/-- The degrees at which `Q` holds of the entities reaching them, the degree predicate abstracted
over the scope of `Q`. Membership at `d` is `Q (μ ⁻¹' Set.Ici d)`. -/
def scopeDegrees (Q : NP α) (μ : α → D) : Set D := {d | Q fun x ↦ d ≤ μ x}

theorem mem_scopeDegrees : d ∈ scopeDegrees Q μ ↔ Q fun x ↦ d ≤ μ x := Iff.rfl

/-- A degree quantifier `𝒟` scoping under `Q`, applied to each entity's own degrees. -/
def LowScope (𝒟 : Set D → Prop) (Q : NP α) (μ : α → D) : Prop :=
  Q fun x ↦ 𝒟 (Iic (μ x))

/-- A degree quantifier `𝒟` scoping over `Q`. -/
def HighScope (𝒟 : Set D → Prop) (Q : NP α) (μ : α → D) : Prop :=
  𝒟 (scopeDegrees Q μ)

/-- `some R` yields the lower closure of the measures of `R`, the than-clause degree set. -/
theorem scopeDegrees_some (R : α → Prop) (μ : α → D) :
    scopeDegrees (GQ.some R) μ = lowerClosure (μ '' {x | R x}) := by
  ext d
  simp [mem_scopeDegrees, GQ.some, mem_lowerClosure]

/-- `every R` yields the lower bounds of the measures of `R`. -/
theorem scopeDegrees_every (R : α → Prop) (μ : α → D) :
    scopeDegrees (every R) μ = lowerBounds (μ '' {x | R x}) := by
  ext d
  exact (mem_lowerBounds.trans forall_mem_image).symm

/-- `no R` yields the degrees no `R`-witness reaches. -/
theorem scopeDegrees_no (R : α → Prop) (μ : α → D) :
    scopeDegrees (no R) μ = (scopeDegrees (GQ.some R) μ)ᶜ := by
  ext d
  exact (not_exists.trans (forall_congr' fun _ ↦ not_and)).symm

theorem isLowerSet_scopeDegrees (hQ : Monotone Q) (μ : α → D) : IsLowerSet (scopeDegrees Q μ) :=
  fun _ _ h hd ↦ hQ (fun _ hx ↦ h.trans hx) hd

theorem isUpperSet_scopeDegrees (hQ : Antitone Q) (μ : α → D) : IsUpperSet (scopeDegrees Q μ) :=
  fun _ _ h hd ↦ hQ (fun _ hx ↦ h.trans hx) hd

/-- Under an antitone quantifier, negation, *at most n* or *refuse*, the degree set has no
maximum on a scale without a top, so the high-scope reading is a presupposition failure. -/
theorem not_isGreatest_scopeDegrees [NoMaxOrder D] (hQ : Antitone Q) (μ : α → D) :
    ¬ ∃ m, IsGreatest (scopeDegrees Q μ) m :=
  fun ⟨_, hm⟩ ↦ (isUpperSet_scopeDegrees hQ μ).not_bddAbove ⟨_, hm.1⟩ hm.bddAbove

/-- The degree set of a monotone quantifier with a maximum is the principal lower set of the
maximum, the degrees to which the shortest girl is tall. -/
theorem scopeDegrees_eq_Iic (hQ : Monotone Q) {m : D} (hm : IsGreatest (scopeDegrees Q μ) m) :
    scopeDegrees Q μ = Iic m :=
  (mem_upperBounds_iff_subset_Iic.1 hm.2).antisymm
    ((isLowerSet_scopeDegrees hQ μ).Iic_subset hm.1)

end Preorder

section PartialOrder
variable [PartialOrder D] {U P : Set D} {Q : NP α} {μ : α → D}

theorem maxIn_Iic {a : D} : MaxIn U (Iic a) ↔ a ∈ U :=
  ⟨fun ⟨_, hm, h⟩ ↦ h.unique isGreatest_Iic ▸ hm, fun h ↦ ⟨a, h, isGreatest_Iic⟩⟩

/-- The degree quantifier at the complementary interval is the negated one under the
presupposition that the maximum exists, the scope splitting of *less than t* as *not as … as
t*. -/
theorem maxIn_compl : MaxIn Uᶜ P ↔ (∃ m, IsGreatest P m) ∧ ¬ MaxIn U P :=
  ⟨fun ⟨m, hm, h⟩ ↦ ⟨⟨m, h⟩, fun ⟨_, hm', h'⟩ ↦ hm (h'.unique h ▸ hm')⟩,
    fun ⟨⟨m, h⟩, hn⟩ ↦ ⟨m, fun hm ↦ hn ⟨m, hm, h⟩, h⟩⟩

/-- The low scope of an interval degree quantifier is `Q` of the entities measuring into the
interval, the preimage of that interval. -/
theorem lowScope_maxIn : LowScope (MaxIn U) Q μ ↔ Q fun x ↦ μ x ∈ U := by
  simp only [LowScope, maxIn_Iic]

/-- The high scope at an upper set entails the low one over a monotone quantifier, since if the
shortest girl is taller than `t` every girl is. -/
theorem lowScope_of_highScope (hQ : Monotone Q) (hU : IsUpperSet U)
    (h : HighScope (MaxIn U) Q μ) : LowScope (MaxIn U) Q μ :=
  let ⟨_, hmU, hm⟩ := h; lowScope_maxIn.2 (hQ (fun _ hx ↦ hU hx hmU) hm.1)

/-- The low scope entails the high one under `every` at every interval when the restrictor has
a least-measuring member, since if every girl's height lies in the interval so does the
shortest girl's. -/
theorem highScope_every_of_lowScope {R : α → Prop} (hR : ∃ x, R x ∧ ∀ y, R y → μ x ≤ μ y)
    (h : LowScope (MaxIn U) (every R) μ) : HighScope (MaxIn U) (every R) μ := by
  rw [lowScope_maxIn] at h
  obtain ⟨x₀, hx₀, hmin⟩ := hR
  exact ⟨μ x₀, h x₀ hx₀, hmin, fun _ hd ↦ hd x₀ hx₀⟩

/-- Over `every R` the greatest degree every `R`-witness reaches is the infimum of their measures.
-/
theorem highScope_maxIn_singleton_every {R : α → Prop} {m : D} :
    HighScope (MaxIn {m}) (every R) μ ↔ IsGLB (μ '' {x | R x}) m := by
  rw [HighScope, maxIn_singleton, scopeDegrees_every]; rfl

/-- Over `some R` the greatest degree some `R`-witness reaches is the greatest of their measures. -/
theorem highScope_maxIn_singleton_some {R : α → Prop} {m : D} :
    HighScope (MaxIn {m}) (GQ.some R) μ ↔ IsGreatest (μ '' {x | R x}) m := by
  rw [HighScope, maxIn_singleton, scopeDegrees_some, isGreatest_lowerClosure_iff]

/-- The high scope entails the low one under `some` at every interval, the tallest witness being
a witness. -/
theorem lowScope_some_of_highScope {R : α → Prop} (h : HighScope (MaxIn U) (GQ.some R) μ) :
    LowScope (MaxIn U) (GQ.some R) μ := by
  obtain ⟨m, hmU, ⟨x, hx, hmx⟩, hub⟩ := h
  exact lowScope_maxIn.2 ⟨x, hx, show μ x ∈ U from hmx.antisymm (hub ⟨x, hx, le_rfl⟩) ▸ hmU⟩

end PartialOrder

section LinearOrder
variable [LinearOrder D] {U : Set D} {Q Q' : NP α} {μ : α → D}

/-- On a finite domain the degree set of a monotone quantifier that fails on the empty
predicate has a maximum as soon as it is nonempty, attained by an entity, the shortest girl
under *every girl* and the tallest under *some girl*. -/
theorem exists_isGreatest_scopeDegrees [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (h : (scopeDegrees Q μ).Nonempty) : ∃ x, IsGreatest (scopeDegrees Q μ) (μ x) := by
  -- every degree of the set lies below a measured degree of the set
  have step : ∀ d ∈ scopeDegrees Q μ, ∃ x, d ≤ μ x ∧ μ x ∈ scopeDegrees Q μ := by
    intro d hd
    have : Nonempty {x // d ≤ μ x} :=
      not_isEmpty_iff.1 fun h ↦ hQ₀ (hQ (fun x hx ↦ h.false ⟨x, hx⟩) hd)
    obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min fun x : {x // d ≤ μ x} ↦ μ x.1
    exact ⟨x₀, hx₀, hQ (fun x hx ↦ hmin ⟨x, hx⟩) hd⟩
  obtain ⟨d, hd⟩ := h
  obtain ⟨x₀, -, hx₀⟩ := step d hd
  have : Nonempty {x // μ x ∈ scopeDegrees Q μ} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨⟨m, hm⟩, hmax⟩ := Finite.exists_max fun x : {x // μ x ∈ scopeDegrees Q μ} ↦ μ x.1
  refine ⟨m, hm, fun d hd ↦ ?_⟩
  obtain ⟨y, hdy, hy⟩ := step d hd
  exact hdy.trans (hmax ⟨y, hy⟩)

/-- The low scope at an upper set entails the high one over a monotone quantifier on a finite
domain, since if every girl is taller than `t` so is the shortest. -/
theorem highScope_of_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥) (hU : IsUpperSet U)
    (h : LowScope (MaxIn U) Q μ) : HighScope (MaxIn U) Q μ := by
  rw [lowScope_maxIn] at h
  have : Nonempty {x // μ x ∈ U} :=
    not_isEmpty_iff.1 fun h' ↦ hQ₀ (hQ (fun x hx ↦ h'.false ⟨x, hx⟩) h)
  obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min fun x : {x // μ x ∈ U} ↦ μ x.1
  have hd₀ : μ x₀ ∈ scopeDegrees Q μ := hQ (fun x hx ↦ hmin ⟨x, hx⟩) h
  obtain ⟨m, hm⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ ⟨_, hd₀⟩
  exact ⟨μ m, hU (hm.2 hd₀) hx₀, hm⟩

/-- Over a monotone quantifier on a finite domain, a degree quantifier at an upper set,
comparative or equative, takes scope without truth-conditional effect. -/
theorem highScope_maxIn_iff_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hU : IsUpperSet U) : HighScope (MaxIn U) Q μ ↔ LowScope (MaxIn U) Q μ :=
  ⟨lowScope_of_highScope hQ hU, highScope_of_lowScope hQ hQ₀ hU⟩

/-- *Less than `t`* over a monotone quantifier, high, is *not as … as `t`*, low, the
scope-splitting reading `NEG + as … as`. -/
theorem highScope_maxIn_Iio_iff [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hne : (scopeDegrees Q μ).Nonempty) {t : D} :
    HighScope (MaxIn (Iio t)) Q μ ↔ ¬ Q fun x ↦ t ≤ μ x := by
  have h := highScope_maxIn_iff_lowScope (μ := μ) hQ hQ₀ (isUpperSet_Ici t)
  simp only [lowScope_maxIn, mem_Ici] at h
  rw [← compl_Ici, ← h]
  obtain ⟨x, hx⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ hne
  exact maxIn_compl.trans (and_iff_right ⟨_, hx⟩)

/-- Under the meet of a quantifier with an antitone one, *exactly n* as *at least n* and *at
most n*, the maximum of the degree set, when defined, is that of the other conjunct, so
high-scope *exactly two girls are taller than t* means *at least two*. -/
theorem isGreatest_scopeDegrees_of_inf (hQ' : Antitone Q') {m : D}
    (h : IsGreatest (scopeDegrees (Q ⊓ Q') μ) m) : IsGreatest (scopeDegrees Q μ) m :=
  ⟨h.1.1, fun _ hd ↦ le_of_not_gt fun hmd ↦
    (h.2 ⟨hd, hQ' (fun _ hx ↦ hmd.le.trans hx) h.1.2⟩).not_gt hmd⟩

/-- On a dense scale the maximum of a degree set with a maximum is the greatest lower bound of
its complement, so the maximum of [heim-2001]'s trivalent entry agrees with the bivalent one. -/
theorem isGLB_compl_scopeDegrees [DenselyOrdered D] (hQ : Monotone Q) {m : D}
    (hm : IsGreatest (scopeDegrees Q μ) m) : IsGLB (scopeDegrees Q μ)ᶜ m := by
  rw [scopeDegrees_eq_Iic hQ hm, compl_Iic]
  exact isGLB_Ioi

/-- When the maximum exists, the greatest lower bound of the complement is it. -/
theorem isGLB_compl_scopeDegrees_iff [DenselyOrdered D] (hQ : Monotone Q) {m : D}
    (h : ∃ m, IsGreatest (scopeDegrees Q μ) m) :
    IsGLB (scopeDegrees Q μ)ᶜ m ↔ IsGreatest (scopeDegrees Q μ) m :=
  let ⟨_, hm'⟩ := h
  ⟨fun hg ↦ hg.unique (isGLB_compl_scopeDegrees hQ hm') ▸ hm', isGLB_compl_scopeDegrees hQ⟩

end LinearOrder

/-! ### The max-quantified comparative

The clausal comparative of von Stechow and Rullmann: some matrix witness stands in a comparison to
the greatest measure of the than-clause witnesses, *more P than Q* at `.gt` and *as P as Q* at
`.ge`. Matrix and than-clause restrictions are independent predicates over a witness sort, so
heterogeneous comparatives are the general case. -/

section MaxComparative
variable [Preorder D] {c : Comparison} {P Q R : α → Prop} {μ : α → D}

/-- The max-quantified comparative under the comparison `c` holds when the measures of the
`Q`-witnesses have a greatest element `δ` and the measure of some `P`-witness stands in `c` to
`δ`. -/
def MaxComparative (c : Comparison) (P Q : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (μ '' {x | Q x}) δ ∧ ∃ x, P x ∧ c.Rel (μ x) δ

/-- A max-quantified comparative entails the comparatives with weaker comparisons, the equative
from the strict comparative in particular. -/
theorem MaxComparative.mono {c' : Comparison} (hc : ∀ a b : D, c.Rel a b → c'.Rel a b)
    (h : MaxComparative c P Q μ) : MaxComparative c' P Q μ :=
  let ⟨δ, hδ, x, hx, hr⟩ := h
  ⟨δ, hδ, x, hx, hc _ _ hr⟩

/-- Every than-clause witness is exceeded by some matrix witness. -/
theorem MaxComparative.exists_lt (h : MaxComparative .gt P Q μ) {x : α} (hx : Q x) :
    ∃ y, P y ∧ μ x < μ y :=
  let ⟨_, hδ, y, hy, hlt⟩ := h
  ⟨y, hy, (hδ.2 ⟨x, hx, rfl⟩).trans_lt hlt⟩

/-- The max-quantified comparative is transitive, so *more P than Q* and *more Q than R* give
*more P than R* with no uniqueness assumption on any of the three sides. -/
theorem MaxComparative.trans (h₁ : MaxComparative .gt P Q μ) (h₂ : MaxComparative .gt Q R μ) :
    MaxComparative .gt P R μ :=
  let ⟨_, hδ, _, hy, hlt⟩ := h₂
  let ⟨z, hz, hlt'⟩ := h₁.exists_lt hy
  ⟨_, hδ, z, hz, hlt.trans hlt'⟩

/-- Under unique matrix and than-clause witnesses, the max-quantified comparative compares their
measures directly. -/
theorem maxComparative_iff_of_unique {xa xb : α} (ha : P xa) (ha_unique : ∀ x, P x → x = xa)
    (hb : Q xb) (hb_unique : ∀ x, Q x → x = xb) :
    MaxComparative c P Q μ ↔ c.Rel (μ xa) (μ xb) := by
  have hQ : {x | Q x} = {xb} := Set.ext fun x ↦ ⟨hb_unique x, fun h ↦ h ▸ hb⟩
  refine ⟨fun ⟨δ, hδ, x, hx, hr⟩ ↦ ?_, fun hr ↦ ⟨_, hQ ▸ image_singleton ▸ isGreatest_singleton,
    xa, ha, hr⟩⟩
  rw [hQ, image_singleton] at hδ
  exact hδ.1 ▸ ha_unique x hx ▸ hr

/-- Comparing two individuals is comparing their measures. -/
theorem maxComparative_eq_iff (μ : α → D) (xa xb : α) :
    MaxComparative c (· = xa) (· = xb) μ ↔ c.Rel (μ xa) (μ xb) :=
  maxComparative_iff_of_unique rfl (fun _ h ↦ h) rfl (fun _ h ↦ h)

/-- With greatest witnesses on both sides and measures monotone on each side, the
max-quantified comparative compares the greatest witnesses' measures. -/
theorem maxComparative_gt_iff_of_isGreatest [Preorder α] {xa xb : α}
    (ha : IsGreatest {x | P x} xa) (hμa : MonotoneOn μ {x | P x})
    (hb : IsGreatest {x | Q x} xb) (hμb : MonotoneOn μ {x | Q x}) :
    MaxComparative .gt P Q μ ↔ μ xb < μ xa :=
  ⟨fun ⟨_, hδ, _, hx, hlt⟩ ↦
      (hδ.2 ⟨xb, hb.1, rfl⟩).trans_lt (hlt.trans_le (hμa hx ha.1 (ha.2 hx))),
    fun hlt ↦ ⟨_, hμb.map_isGreatest hb, xa, ha.1, hlt⟩⟩

end MaxComparative

section MaxComparativeLinearOrder
variable [LinearOrder D] {P Q : α → Prop} {μ : α → D} {a b : D}

/-- The max-quantified equative is antisymmetric. When each side is at least as great as the
other, the greatest measures coincide. -/
theorem MaxComparative.antisymm (ha : IsGreatest (μ '' {x | P x}) a)
    (hb : IsGreatest (μ '' {x | Q x}) b) (h₁ : MaxComparative .ge P Q μ)
    (h₂ : MaxComparative .ge Q P μ) : a = b := by
  obtain ⟨b', hb', y, hy, hby⟩ := h₁
  obtain ⟨a', ha', x, hx, hax⟩ := h₂
  rw [ha.unique ha', hb.unique hb']
  exact (hax.trans (hb'.2 ⟨x, hx, rfl⟩)).antisymm (hby.trans (ha'.2 ⟨y, hy, rfl⟩))

/-- On a linear scale the max-quantified equative is total whenever both sides have a greatest
measure. -/
theorem maxComparative_ge_total (ha : IsGreatest (μ '' {x | P x}) a)
    (hb : IsGreatest (μ '' {x | Q x}) b) :
    MaxComparative .ge P Q μ ∨ MaxComparative .ge Q P μ := by
  obtain ⟨x, hx, rfl⟩ := ha.1
  obtain ⟨y, hy, rfl⟩ := hb.1
  exact (le_total (μ y) (μ x)).imp (fun h ↦ ⟨_, hb, x, hx, h⟩) fun h ↦ ⟨_, ha, y, hy, h⟩

/-- On a linear scale, when both sides have a greatest measure, one side exceeds the other or the
greatest measures coincide. -/
theorem maxComparative_gt_trichotomy (ha : IsGreatest (μ '' {x | P x}) a)
    (hb : IsGreatest (μ '' {x | Q x}) b) :
    MaxComparative .gt P Q μ ∨ a = b ∨ MaxComparative .gt Q P μ := by
  obtain ⟨x, hx, rfl⟩ := ha.1
  obtain ⟨y, hy, rfl⟩ := hb.1
  rcases lt_trichotomy (μ y) (μ x) with h | h | h
  · exact .inl ⟨_, hb, x, hx, h⟩
  · exact .inr (.inl h.symm)
  · exact .inr (.inr ⟨_, ha, y, hy, h⟩)

end MaxComparativeLinearOrder

/-! ### Set-of-degrees comparative

The S-comparative of [hoeksema-1983] generalizes the point-standard comparative from a single
standard to a degree-set standard. Its extension is `μ ⁻¹' strictUpperBounds Δ`, the entities
measuring above every standard degree, and the binary comparator is its singleton case
(`Comparison.bounds_singleton`). -/

section SetOfDegrees
variable [Preorder D] (μ : α → D) {Δ : Set D}

/-- The set-of-degrees comparative as a strict-interval inclusion, the strict mirror of
`mem_upperBounds_iff_subset_Iic`. An entity `y` clears the than-clause iff every standard
degree lies strictly below `μ y`. -/
theorem mem_gtOverSet_iff_subset_Iio (y : α) : y ∈ μ ⁻¹' strictUpperBounds Δ ↔ Δ ⊆ Iio (μ y) :=
  Iff.rfl

/-- The S-comparative is anti-additive in its degree-set argument ([hoeksema-1983]), the
algebraic source of NPI licensing in clausal than-comparatives. -/
theorem gtOverSet_isAntiAdditive : IsAntiAdditive (μ ⁻¹' strictUpperBounds ·) :=
  isAntiAdditive_forall_mem fun d y ↦ d < μ y

/-- The S-comparative is determined by the greatest element of its degree-set argument
([bhatt-pancheva-2004]). -/
theorem gtOverSet_eq_singleton_of_isGreatest {m : D} (hm : IsGreatest Δ m) :
    μ ⁻¹' strictUpperBounds Δ = μ ⁻¹' strictUpperBounds {m} := by
  ext y
  simp only [mem_gtOverSet_iff_subset_Iio, singleton_subset_iff, mem_Iio]
  exact ⟨(· hm.1), fun h _ hd ↦ (hm.2 hd).trans_lt h⟩

/-- When the than-clause measures have a greatest element, a matrix witness clears it iff it
clears them all. -/
theorem maxComparative_gt_iff_gtOverSet (P Q : α → Prop) :
    MaxComparative .gt P Q μ ↔
      (∃ δ, IsGreatest (μ '' {x | Q x}) δ) ∧
        ∃ x, P x ∧ x ∈ μ ⁻¹' strictUpperBounds (μ '' {x | Q x}) :=
  ⟨fun ⟨δ, hδ, x, hx, hlt⟩ ↦ ⟨⟨δ, hδ⟩, x, hx, fun _ hd ↦ (hδ.2 hd).trans_lt hlt⟩,
    fun ⟨⟨δ, hδ⟩, x, hx, hclear⟩ ↦ ⟨δ, hδ, x, hx, hclear hδ.1⟩⟩

end SetOfDegrees

/-! ### Superlatives

*-est* universally quantifies the comparative over a comparison class ([heim-1999]), the
semantic reflex of [bobaljik-2012]'s containment `[[[ADJ] CMPR] SPRL]`. -/

section Superlative
variable [LinearOrder D] {μ : α → D} {C : Set α} {x y : α}

/-- The absolute superlative holds of `x` when `x` is in the comparison class `C` and beats every
other member on the comparative. -/
def AbsoluteSuperlative (μ : α → D) (C : Set α) (x : α) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → μ y < μ x

/-- At most one entity satisfies the absolute superlative. -/
theorem absoluteSuperlative_unique (hx : AbsoluteSuperlative μ C x)
    (hy : AbsoluteSuperlative μ C y) : x = y :=
  by_contra fun hne ↦ lt_asymm (hx.2 y hy.1 (Ne.symm hne)) (hy.2 x hx.1 hne)

/-- The absolute superlative makes `μ x` the greatest element of the degree image `μ '' C`; the
converse fails under ties. -/
theorem absoluteSuperlative_isGreatest (h : AbsoluteSuperlative μ C x) :
    IsGreatest (μ '' C) (μ x) :=
  ⟨mem_image_of_mem μ h.1, forall_mem_image.2 fun y hy ↦
    (eq_or_ne y x).elim (fun e ↦ e ▸ le_rfl) fun hne ↦ (h.2 y hy hne).le⟩

end Superlative

end Degree
