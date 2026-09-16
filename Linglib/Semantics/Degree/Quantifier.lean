import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.UpperLower.Basic
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Quantification.Basic
import Linglib.Logic.Natural.Additivity

/-!
# Degree quantifiers

This file defines the denotations of degree phrases as quantifiers over degrees and their scope
relative to a quantifier over entities or worlds. A degree phrase says that the maximum of its
degree predicate lies in an interval, `maxIn U P`; under a quantifier `Q` it scopes low, applied
to each entity's own degrees, or high, applied to `scopeDegrees Q μ`, the degrees at which `Q`
holds. The than-clause degree set `thanDegrees` is the existential case, and the max-quantified
comparative `maxComparative` compares a matrix witness with its maximum.

## Main definitions

* `maxIn U P`: the greatest element of `P` lies in `U`.
* `scopeDegrees Q μ`: the degrees `d` such that `Q` holds of the entities measuring at least `d`.
* `lowScope 𝒟 Q μ`, `highScope 𝒟 Q μ`: the degree quantifier `𝒟` under and over `Q`.
* `thanDegrees P μ`, `maxComparative`, `maxEquative`: the than-clause degree set and the
  max-quantified comparative and equative over it.
* `absoluteSuperlative μ C x`: `x` measures above every other member of `C`.

## Main results

* `highScope_maxIn_iff_lowScope`: over a monotone quantifier on a finite domain, a degree
  quantifier at an upper set takes scope without truth-conditional effect.
* `not_isGreatest_scopeDegrees`: under an antitone quantifier the degree set has no maximum.
* `highScope_maxIn_singleton_every`, `highScope_maxIn_singleton_some`: the exact degree
  quantifier over `every` names the infimum of the measures and over `some` their greatest.
* `isGreatest_scopeDegrees_of_inf`: under a meet with an antitone quantifier the maximum is the
  other conjunct's.
* `maxComparative_unique`: with unique witnesses the max-quantified comparative is direct
  measure comparison.
* `gtOverSet_isAntiAdditive`: the set-standard comparative is anti-additive in its standard.

## References

* [heim-2001]
* [von-stechow-1984]
* [rullmann-1995]
* [hoeksema-1983]
* [bhatt-pancheva-2004]
* [heim-1999]
-/

namespace Degree

open NaturalLogic Quantification Set

variable {α D : Type*}

/-! ### Degree quantifiers and their scope -/

section Preorder
variable [Preorder D] {Q : Quantifier α} {μ : α → D} {d : D}

/-- The greatest element of `P` lies in `U`. These are the degree quantifiers of [heim-2001],
*-er than `t`* at `U = Ioi t`, *less than `t`* at `Iio t`, *exactly `δ` -er than `t`* at
`{t + δ}`, and the equative at `Ici t`. -/
def maxIn (U P : Set D) : Prop := ∃ m ∈ U, IsGreatest P m

theorem maxIn_singleton {P : Set D} {a : D} : maxIn {a} P ↔ IsGreatest P a := exists_eq_left

/-- The degrees at which `Q` holds of the entities reaching them, the degree predicate abstracted
over the scope of `Q`. Membership at `d` is `Q (Comparison.ge.over μ d)`. -/
def scopeDegrees (Q : Quantifier α) (μ : α → D) : Set D := {d | Q λ x => d ≤ μ x}

theorem mem_scopeDegrees : d ∈ scopeDegrees Q μ ↔ Q λ x => d ≤ μ x := Iff.rfl

/-- A degree quantifier `𝒟` scoping under `Q`, applied to each entity's own degrees. -/
def lowScope (𝒟 : Set D → Prop) (Q : Quantifier α) (μ : α → D) : Prop :=
  Q λ x => 𝒟 (Iic (μ x))

/-- A degree quantifier `𝒟` scoping over `Q`. -/
def highScope (𝒟 : Set D → Prop) (Q : Quantifier α) (μ : α → D) : Prop :=
  𝒟 (scopeDegrees Q μ)

/-- The than-clause degree set, the degrees reached by some `P`-witness. -/
def thanDegrees (P : α → Prop) (μ : α → D) : Set D := scopeDegrees (some_sem P) μ

theorem mem_thanDegrees {P : α → Prop} : d ∈ thanDegrees P μ ↔ ∃ x, P x ∧ d ≤ μ x := Iff.rfl

/-- A unique witness collapses the than-clause degree set to the principal lower set of its
measure, the phrasal standard. -/
theorem thanDegrees_singleton (μ : α → D) (b : α) : thanDegrees (· = b) μ = Iic (μ b) := by
  ext d; simp [mem_thanDegrees]

/-- `every R` yields the lower bounds of the measures of `R`. -/
theorem scopeDegrees_every (R : α → Prop) (μ : α → D) :
    scopeDegrees (every_sem R) μ = lowerBounds (μ '' {x | R x}) := by
  ext d
  exact (mem_lowerBounds.trans forall_mem_image).symm

/-- `no R` yields the degrees no `R`-witness reaches. -/
theorem scopeDegrees_no (R : α → Prop) (μ : α → D) :
    scopeDegrees (no_sem R) μ = (thanDegrees R μ)ᶜ := by
  ext d
  exact (not_exists.trans (forall_congr' λ _ => not_and)).symm

theorem isLowerSet_scopeDegrees (hQ : Monotone Q) (μ : α → D) : IsLowerSet (scopeDegrees Q μ) :=
  λ _ _ h hd => hQ (λ _ hx => h.trans hx) hd

theorem isUpperSet_scopeDegrees (hQ : Antitone Q) (μ : α → D) : IsUpperSet (scopeDegrees Q μ) :=
  λ _ _ h hd => hQ (λ _ hx => h.trans hx) hd

/-- Under an antitone quantifier, negation, *at most n* or *refuse*, the degree set has no
maximum on a scale without a top, so the high-scope reading is a presupposition failure. -/
theorem not_isGreatest_scopeDegrees [NoMaxOrder D] (hQ : Antitone Q) (μ : α → D) :
    ¬ ∃ m, IsGreatest (scopeDegrees Q μ) m :=
  λ ⟨_, hm⟩ => (isUpperSet_scopeDegrees hQ μ).not_bddAbove ⟨_, hm.1⟩ hm.bddAbove

/-- The degree set of a monotone quantifier with a maximum is the principal lower set of the
maximum, the degrees to which the shortest girl is tall. -/
theorem scopeDegrees_eq_Iic (hQ : Monotone Q) {m : D} (hm : IsGreatest (scopeDegrees Q μ) m) :
    scopeDegrees Q μ = Iic m :=
  (mem_upperBounds_iff_subset_Iic.1 hm.2).antisymm
    ((isLowerSet_scopeDegrees hQ μ).Iic_subset hm.1)

end Preorder

section PartialOrder
variable [PartialOrder D] {U P : Set D} {Q : Quantifier α} {μ : α → D}

theorem maxIn_Iic {a : D} : maxIn U (Iic a) ↔ a ∈ U :=
  ⟨λ ⟨_, hm, h⟩ => h.unique isGreatest_Iic ▸ hm, λ h => ⟨a, h, isGreatest_Iic⟩⟩

/-- The degree quantifier at the complementary interval is the negated one under the
presupposition that the maximum exists, the scope splitting of *less than t* as *not as … as
t*. -/
theorem maxIn_compl : maxIn Uᶜ P ↔ (∃ m, IsGreatest P m) ∧ ¬ maxIn U P :=
  ⟨λ ⟨m, hm, h⟩ => ⟨⟨m, h⟩, λ ⟨_, hm', h'⟩ => hm (h'.unique h ▸ hm')⟩,
    λ ⟨⟨m, h⟩, hn⟩ => ⟨m, λ hm => hn ⟨m, hm, h⟩, h⟩⟩

/-- The low scope of an interval degree quantifier is `Q` of the entities measuring into the
interval, `Comparison.over` at that interval. -/
theorem lowScope_maxIn : lowScope (maxIn U) Q μ ↔ Q λ x => μ x ∈ U := by
  simp only [lowScope, maxIn_Iic]

/-- The high scope at an upper set entails the low one over a monotone quantifier, since if the
shortest girl is taller than `t` every girl is. -/
theorem lowScope_of_highScope (hQ : Monotone Q) (hU : IsUpperSet U)
    (h : highScope (maxIn U) Q μ) : lowScope (maxIn U) Q μ :=
  let ⟨_, hmU, hm⟩ := h; lowScope_maxIn.2 (hQ (λ _ hx => hU hx hmU) hm.1)

/-- The low scope entails the high one under `every` at every interval when the restrictor has
a least-measuring member, since if every girl's height lies in the interval so does the
shortest girl's. -/
theorem highScope_every_of_lowScope {R : α → Prop} (hR : ∃ x, R x ∧ ∀ y, R y → μ x ≤ μ y)
    (h : lowScope (maxIn U) (every_sem R) μ) : highScope (maxIn U) (every_sem R) μ := by
  rw [lowScope_maxIn] at h
  obtain ⟨x₀, hx₀, hmin⟩ := hR
  exact ⟨μ x₀, h x₀ hx₀, hmin, λ _ hd => hd x₀ hx₀⟩

/-- The exact degree quantifier over `every R`: the greatest degree every `R`-witness reaches is
the infimum of their measures. -/
theorem highScope_maxIn_singleton_every {R : α → Prop} {m : D} :
    highScope (maxIn {m}) (every_sem R) μ ↔ IsGLB (μ '' {x | R x}) m := by
  rw [highScope, maxIn_singleton, scopeDegrees_every]; rfl

/-- The exact degree quantifier over `some R`: the greatest degree some `R`-witness reaches is
the greatest of their measures. -/
theorem highScope_maxIn_singleton_some {R : α → Prop} {m : D} :
    highScope (maxIn {m}) (some_sem R) μ ↔ IsGreatest (μ '' {x | R x}) m := by
  rw [highScope, maxIn_singleton]
  constructor
  · rintro ⟨⟨x, hx, hmx⟩, hub⟩
    exact ⟨⟨x, hx, (hub ⟨x, hx, le_rfl⟩).antisymm hmx⟩,
      λ _ ⟨y, hy, hdy⟩ => hdy ▸ hub ⟨y, hy, le_rfl⟩⟩
  · rintro ⟨⟨x, hx, rfl⟩, hub⟩
    exact ⟨⟨x, hx, le_rfl⟩, λ _ ⟨y, hy, hdy⟩ => hdy.trans (hub ⟨y, hy, rfl⟩)⟩

/-- The high scope entails the low one under `some` at every interval, the tallest witness being
a witness. -/
theorem lowScope_some_of_highScope {R : α → Prop} (h : highScope (maxIn U) (some_sem R) μ) :
    lowScope (maxIn U) (some_sem R) μ := by
  obtain ⟨m, hmU, ⟨x, hx, hmx⟩, hub⟩ := h
  exact lowScope_maxIn.2 ⟨x, hx, show μ x ∈ U from hmx.antisymm (hub ⟨x, hx, le_rfl⟩) ▸ hmU⟩

end PartialOrder

section LinearOrder
variable [LinearOrder D] {U : Set D} {Q Q' : Quantifier α} {μ : α → D}

/-- On a finite domain the degree set of a monotone quantifier that fails on the empty
predicate has a maximum as soon as it is nonempty, attained by an entity, the shortest girl
under *every girl* and the tallest under *some girl*. -/
theorem exists_isGreatest_scopeDegrees [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (h : (scopeDegrees Q μ).Nonempty) : ∃ x, IsGreatest (scopeDegrees Q μ) (μ x) := by
  -- every degree of the set lies below a measured degree of the set
  have step : ∀ d ∈ scopeDegrees Q μ, ∃ x, d ≤ μ x ∧ μ x ∈ scopeDegrees Q μ := by
    intro d hd
    have : Nonempty {x // d ≤ μ x} :=
      not_isEmpty_iff.1 λ h => hQ₀ (hQ (λ x hx => h.false ⟨x, hx⟩) hd)
    obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min λ x : {x // d ≤ μ x} => μ x.1
    exact ⟨x₀, hx₀, hQ (λ x hx => hmin ⟨x, hx⟩) hd⟩
  obtain ⟨d, hd⟩ := h
  obtain ⟨x₀, -, hx₀⟩ := step d hd
  have : Nonempty {x // μ x ∈ scopeDegrees Q μ} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨⟨m, hm⟩, hmax⟩ := Finite.exists_max λ x : {x // μ x ∈ scopeDegrees Q μ} => μ x.1
  refine ⟨m, hm, λ d hd => ?_⟩
  obtain ⟨y, hdy, hy⟩ := step d hd
  exact hdy.trans (hmax ⟨y, hy⟩)

/-- The low scope at an upper set entails the high one over a monotone quantifier on a finite
domain, since if every girl is taller than `t` so is the shortest. -/
theorem highScope_of_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥) (hU : IsUpperSet U)
    (h : lowScope (maxIn U) Q μ) : highScope (maxIn U) Q μ := by
  rw [lowScope_maxIn] at h
  have : Nonempty {x // μ x ∈ U} :=
    not_isEmpty_iff.1 λ h' => hQ₀ (hQ (λ x hx => h'.false ⟨x, hx⟩) h)
  obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min λ x : {x // μ x ∈ U} => μ x.1
  have hd₀ : μ x₀ ∈ scopeDegrees Q μ := hQ (λ x hx => hmin ⟨x, hx⟩) h
  obtain ⟨m, hm⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ ⟨_, hd₀⟩
  exact ⟨μ m, hU (hm.2 hd₀) hx₀, hm⟩

/-- Over a monotone quantifier on a finite domain, a degree quantifier at an upper set,
comparative or equative, takes scope without truth-conditional effect. -/
theorem highScope_maxIn_iff_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hU : IsUpperSet U) : highScope (maxIn U) Q μ ↔ lowScope (maxIn U) Q μ :=
  ⟨lowScope_of_highScope hQ hU, highScope_of_lowScope hQ hQ₀ hU⟩

/-- *Less than `t`* over a monotone quantifier, high, is *not as … as `t`*, low, the
scope-splitting reading `NEG + as … as`. -/
theorem highScope_maxIn_Iio_iff [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hne : (scopeDegrees Q μ).Nonempty) {t : D} :
    highScope (maxIn (Iio t)) Q μ ↔ ¬ Q λ x => t ≤ μ x := by
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
  ⟨h.1.1, λ _ hd => le_of_not_gt λ hmd =>
    (h.2 ⟨hd, hQ' (λ _ hx => hmd.le.trans hx) h.1.2⟩).not_gt hmd⟩

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
  ⟨λ hg => hg.unique (isGLB_compl_scopeDegrees hQ hm') ▸ hm', isGLB_compl_scopeDegrees hQ⟩

end LinearOrder

/-! ### The max-quantified comparative

The clausal comparative of [von-stechow-1984] and [rullmann-1995]: some matrix witness measures
strictly above the maximum of the than-clause degree set. Matrix and than-clause restrictions
are independent predicates over a witness sort, so heterogeneous comparatives are the general
case. -/

section MaxQuantified
variable [Preorder D] {Pmatrix Pthan : α → Prop} {μ : α → D}

/-- The max-quantified comparative holds when the `Pthan` degree set has a greatest element `δ`
and some `Pmatrix`-witness measures strictly above `δ`. -/
def maxComparative (Pmatrix Pthan : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (thanDegrees Pthan μ) δ ∧ ∃ x, Pmatrix x ∧ δ < μ x

/-- The max-quantified equative, `maxComparative` with the weak threshold. -/
def maxEquative (Pmatrix Pthan : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (thanDegrees Pthan μ) δ ∧ ∃ x, Pmatrix x ∧ δ ≤ μ x

/-- The strict comparative entails the equative. -/
theorem maxComparative_entails_maxEquative (Pmatrix Pthan : α → Prop) (μ : α → D) :
    maxComparative Pmatrix Pthan μ → maxEquative Pmatrix Pthan μ :=
  λ ⟨δ, hδ, x, hx, hlt⟩ => ⟨δ, hδ, x, hx, hlt.le⟩

/-- A unique `Pthan`-witness makes its measure the greatest than-clause degree. -/
theorem isGreatest_thanDegrees_of_unique {xb : α} (hb : Pthan xb)
    (hb_unique : ∀ x, Pthan x → x = xb) : IsGreatest (thanDegrees Pthan μ) (μ xb) :=
  ⟨⟨xb, hb, le_rfl⟩, λ _ ⟨x, hx, hle⟩ => hb_unique x hx ▸ hle⟩

/-- Under unique matrix and than-clause witnesses, the max-quantified comparative is direct
measure comparison. -/
theorem maxComparative_unique {xa xb : α} (ha : Pmatrix xa) (ha_unique : ∀ x, Pmatrix x → x = xa)
    (hb : Pthan xb) (hb_unique : ∀ x, Pthan x → x = xb) :
    maxComparative Pmatrix Pthan μ ↔ μ xb < μ xa :=
  ⟨λ ⟨_, hδ, x, hx, hlt⟩ => (hδ.2 ⟨xb, hb, le_rfl⟩).trans_lt (ha_unique x hx ▸ hlt),
    λ hlt => ⟨_, isGreatest_thanDegrees_of_unique hb hb_unique, xa, ha, hlt⟩⟩

/-- Comparing unique individuals is direct measure comparison. -/
theorem maxComparative_eq_iff (μ : α → D) (xa xb : α) :
    maxComparative (· = xa) (· = xb) μ ↔ μ xb < μ xa :=
  maxComparative_unique rfl (λ _ h => h) rfl (λ _ h => h)

/-- A greatest than-clause witness under a measure monotone on the witnesses makes its measure
the greatest than-clause degree. -/
theorem isGreatest_thanDegrees_of_isGreatest [Preorder α] {xb : α}
    (hb : IsGreatest {x | Pthan x} xb) (hμ : MonotoneOn μ {x | Pthan x}) :
    IsGreatest (thanDegrees Pthan μ) (μ xb) :=
  ⟨⟨xb, hb.1, le_rfl⟩, λ _ ⟨_, hx, hle⟩ => hle.trans (hμ hx hb.1 (hb.2 hx))⟩

/-- With greatest witnesses on both sides and measures monotone on each side, the
max-quantified comparative compares the greatest witnesses' measures. -/
theorem maxComparative_of_isGreatest [Preorder α] {xa xb : α}
    (ha : IsGreatest {x | Pmatrix x} xa) (hμa : MonotoneOn μ {x | Pmatrix x})
    (hb : IsGreatest {x | Pthan x} xb) (hμb : MonotoneOn μ {x | Pthan x}) :
    maxComparative Pmatrix Pthan μ ↔ μ xb < μ xa :=
  ⟨λ ⟨_, hδ, _, hx, hlt⟩ =>
      (hδ.2 ⟨xb, hb.1, le_rfl⟩).trans_lt (hlt.trans_le (hμa hx ha.1 (ha.2 hx))),
    λ hlt => ⟨_, isGreatest_thanDegrees_of_isGreatest hb hμb, xa, ha.1, hlt⟩⟩

end MaxQuantified

/-! ### Set-of-degrees comparative

The S-comparative of [hoeksema-1983] generalizes `comparativeSem` from a single standard to a
degree-set standard. It is `Comparison.gt.overSet μ`, the strict set-standard predication of
`Degree.Comparison`, and the binary comparator is its singleton case
(`Comparison.overSet_singleton`). -/

section SetOfDegrees
variable [Preorder D] (μ : α → D) {Δ : Set D}

/-- The set-of-degrees comparative as a strict-interval inclusion, the strict mirror of
`mem_upperBounds_iff_subset_Iic`. An entity `y` clears the than-clause iff every standard
degree lies strictly below `μ y`. -/
theorem mem_gtOverSet_iff_subset_Iio (y : α) : y ∈ Comparison.gt.overSet μ Δ ↔ Δ ⊆ Iio (μ y) :=
  Iff.rfl

/-- The S-comparative is anti-additive in its degree-set argument ([hoeksema-1983]), the
algebraic source of NPI licensing in clausal than-comparatives. -/
theorem gtOverSet_isAntiAdditive : IsAntiAdditive (Comparison.gt.overSet μ) :=
  isAntiAdditive_forall_mem λ d y => d < μ y

/-- The S-comparative is determined by the greatest element of its degree-set argument
([bhatt-pancheva-2004]). -/
theorem gtOverSet_eq_singleton_of_isGreatest {m : D} (hm : IsGreatest Δ m) :
    Comparison.gt.overSet μ Δ = Comparison.gt.overSet μ {m} := by
  ext y
  simp only [mem_gtOverSet_iff_subset_Iio, singleton_subset_iff, mem_Iio]
  exact ⟨(· hm.1), λ h _ hd => (hm.2 hd).trans_lt h⟩

/-- When the than-clause degree set has a maximum, a matrix witness clears it iff it clears the
whole set. -/
theorem maxComparative_iff_gtOverSet (Pmatrix Pthan : α → Prop) :
    maxComparative Pmatrix Pthan μ ↔
      (∃ δ, IsGreatest (thanDegrees Pthan μ) δ) ∧
        ∃ x, Pmatrix x ∧ x ∈ Comparison.gt.overSet μ (thanDegrees Pthan μ) :=
  ⟨λ ⟨δ, hδ, x, hx, hlt⟩ => ⟨⟨δ, hδ⟩, x, hx, λ _ hd => (hδ.2 hd).trans_lt hlt⟩,
    λ ⟨⟨δ, hδ⟩, x, hx, hclear⟩ => ⟨δ, hδ, x, hx, hclear hδ.1⟩⟩

end SetOfDegrees

/-! ### Superlatives

*-est* universally quantifies the comparative over a comparison class ([heim-1999]), the
semantic reflex of [bobaljik-2012]'s containment `[[[ADJ] CMPR] SPRL]`. -/

section Superlative
variable [LinearOrder D] {μ : α → D} {C : Set α} {x y : α}

/-- The absolute superlative holds of `x` when `x` is in the comparison class `C` and beats every
other member on the comparative. -/
def absoluteSuperlative (μ : α → D) (C : Set α) (x : α) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → comparativeSem μ x y .positive

/-- At most one entity satisfies the absolute superlative. -/
theorem absoluteSuperlative_unique (hx : absoluteSuperlative μ C x)
    (hy : absoluteSuperlative μ C y) : x = y :=
  by_contra λ hne => lt_asymm (hx.2 y hy.1 (Ne.symm hne)) (hy.2 x hx.1 hne)

/-- The absolute superlative makes `μ x` the greatest element of the degree image `μ '' C`; the
converse fails under ties. -/
theorem absoluteSuperlative_isGreatest (h : absoluteSuperlative μ C x) :
    IsGreatest (μ '' C) (μ x) :=
  ⟨mem_image_of_mem μ h.1, forall_mem_image.2 λ y hy =>
    (eq_or_ne y x).elim (λ e => e ▸ le_rfl) λ hne => (h.2 y hy hne).le⟩

end Superlative

end Degree
