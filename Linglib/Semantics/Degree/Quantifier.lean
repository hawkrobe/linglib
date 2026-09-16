import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.UpperLower.Basic
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Quantification.Basic
import Linglib.Logic.Natural.Additivity

/-!
# Degree quantifiers

A DegP denotes a quantifier over degrees. This file collects the degree quantifiers of the
clausal comparative and their scope: the set-of-degrees comparative `Comparison.gt.overSet μ`
([hoeksema-1983]), the max-quantified comparative over the than-clause degree set `thanDegrees`
([von-stechow-1984], [rullmann-1995]), the scope of a DegP relative to a quantifier over
entities or worlds ([heim-2001]), and the superlative ([heim-1999]).

## Main declarations

* `thanDegrees`, `maxComparative`, `maxEquative`: the than-clause degree set and the
  max-quantified comparative and equative over it; `maxComparative_unique` is the phrasal
  collapse to direct measure comparison.
* `maxIn U P`: the maximum of `P` lies in `U`, the DegP denotations of [heim-2001]: *-er than
  t* at `U = Ioi t`, *less than t* at `Iio t`, *exactly δ -er than t* at `{t + δ}`, the
  equative at `Ici t`.
* `scopeDegrees Q μ`: the degrees `d` at which a quantifier `Q` holds of the entities reaching
  `d`; `lowScope`, `highScope`: a DegP scoping under and over `Q`.
* `highScope_maxIn_iff_lowScope`: over a monotone increasing quantifier on a finite domain the
  two scopes coincide at every upper interval; `not_isGreatest_scopeDegrees`: under a monotone
  decreasing one the maximum is undefined; `isGreatest_scopeDegrees_of_inf`: under a meet of
  the two the maximum is the increasing conjunct's.
* `absoluteSuperlative`, `relativeSuperlative`: *-est* over a comparison class and over focus
  alternatives.

## References

* [heim-2001]
* [hoeksema-1983]
* [von-stechow-1984]
* [rullmann-1995]
* [bhatt-pancheva-2004]
* [pasternak-2019]
* [heim-1999]
* [szabolcsi-1986]
* [bobaljik-2012]
-/

namespace Degree

open NaturalLogic Set

/-! ### Set-of-degrees comparative

The S-comparative of [hoeksema-1983] generalizes `comparativeSem` from a single standard to a
degree-set standard. It is `Comparison.gt.overSet μ`, the strict set-standard predication of
`Degree.Comparison`, and the binary comparator is its singleton case
(`Comparison.overSet_singleton`). -/

section SetOfDegrees
variable {Entity D : Type*} [Preorder D]

/-- The set-of-degrees comparative as a strict-interval inclusion: `y` clears the than-clause iff
every standard degree lies strictly below `μ y`, the strict mirror of
`mem_upperBounds_iff_subset_Iic`. -/
theorem mem_gtOverSet_iff_subset_Iio (μ : Entity → D) (Δ : Set D) (y : Entity) :
    y ∈ Comparison.gt.overSet μ Δ ↔ Δ ⊆ Iio (μ y) :=
  Iff.rfl

/-- The S-comparative is anti-additive in its degree-set argument ([hoeksema-1983]), the
algebraic source of NPI licensing in clausal than-comparatives. -/
theorem gtOverSet_isAntiAdditive (μ : Entity → D) :
    IsAntiAdditive (Comparison.gt.overSet μ) :=
  isAntiAdditive_forall_mem (λ d y => d < μ y)

/-- The S-comparative is determined by the greatest element of its degree-set argument
([bhatt-pancheva-2004]). -/
theorem gtOverSet_eq_singleton_of_isGreatest (μ : Entity → D) {Δ : Set D}
    {m : D} (hm : IsGreatest Δ m) :
    Comparison.gt.overSet μ Δ = Comparison.gt.overSet μ ({m} : Set D) := by
  ext y
  refine ⟨λ h d hd => ?_, λ h d hd => ?_⟩
  · rw [mem_singleton_iff] at hd
    exact hd ▸ h hm.1
  · exact lt_of_le_of_lt (hm.2 hd) (h rfl)

end SetOfDegrees

/-! ### Max-quantified comparative

The clausal comparative of [von-stechow-1984] and [rullmann-1995]: some matrix witness measures
strictly above the maximum of the than-clause degree set. Matrix and than-clause restrictions
are independent predicates over a witness sort, so heterogeneous comparatives are the general
case. -/

section MaxQuantified
variable {α D : Type*} [Preorder D]

/-- The than-clause degree set: the degrees reached by some `Pthan`-witness. -/
def thanDegrees (Pthan : α → Prop) (μ : α → D) : Set D :=
  {d | ∃ x, Pthan x ∧ d ≤ μ x}

/-- A unique standard collapses the than-clause degree set to the principal lower set of its
measure, the phrasal standard. -/
theorem thanDegrees_singleton (μ : α → D) (b : α) :
    thanDegrees (· = b) μ = Iic (μ b) := by
  ext d; simp [thanDegrees]

/-- The max-quantified comparative: the `Pthan` degree set has a greatest element `δ`, and some
`Pmatrix`-witness measures strictly above `δ`. -/
def maxComparative (Pmatrix Pthan : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (thanDegrees Pthan μ) δ ∧ ∃ x, Pmatrix x ∧ δ < μ x

/-- A unique `Pthan`-witness makes its measure the greatest than-clause degree. -/
theorem isGreatest_thanDegrees_of_unique {Pthan : α → Prop} {μ : α → D} {xb : α}
    (hb : Pthan xb) (hb_unique : ∀ x, Pthan x → x = xb) :
    IsGreatest (thanDegrees Pthan μ) (μ xb) :=
  ⟨⟨xb, hb, le_refl _⟩, λ _ ⟨x, hx, hle⟩ => hb_unique x hx ▸ hle⟩

/-- Under unique matrix and than-clause witnesses, the max-quantified comparative is direct
measure comparison. -/
theorem maxComparative_unique {Pmatrix Pthan : α → Prop} {μ : α → D} {xa xb : α}
    (ha : Pmatrix xa) (ha_unique : ∀ x, Pmatrix x → x = xa)
    (hb : Pthan xb) (hb_unique : ∀ x, Pthan x → x = xb) :
    maxComparative Pmatrix Pthan μ ↔ μ xb < μ xa := by
  constructor
  · rintro ⟨δ, hδ, x, hx, hlt⟩
    rw [ha_unique x hx] at hlt
    exact lt_of_le_of_lt (hδ.2 ⟨xb, hb, le_refl _⟩) hlt
  · exact λ hlt =>
      ⟨μ xb, isGreatest_thanDegrees_of_unique hb hb_unique, xa, ha, hlt⟩

/-- The max-quantified equative: `maxComparative` with the weak threshold. -/
def maxEquative (Pmatrix Pthan : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (thanDegrees Pthan μ) δ ∧ ∃ x, Pmatrix x ∧ δ ≤ μ x

/-- The strict comparative entails the equative. -/
theorem maxComparative_entails_maxEquative (Pmatrix Pthan : α → Prop) (μ : α → D) :
    maxComparative Pmatrix Pthan μ → maxEquative Pmatrix Pthan μ :=
  λ ⟨δ, hδ, x, hx, hlt⟩ => ⟨δ, hδ, x, hx, hlt.le⟩

/-- Comparing unique individuals is direct measure comparison. -/
theorem maxComparative_eq_iff (μ : α → D) (xa xb : α) :
    maxComparative (· = xa) (· = xb) μ ↔ μ xb < μ xa :=
  maxComparative_unique rfl (λ _ h => h) rfl (λ _ h => h)

/-- A greatest than-clause witness under a measure monotone on the witnesses makes its measure
the greatest than-clause degree. -/
theorem isGreatest_thanDegrees_of_isGreatest [Preorder α] {Pthan : α → Prop} {μ : α → D}
    {xb : α} (hb : IsGreatest {x | Pthan x} xb) (hμ : MonotoneOn μ {x | Pthan x}) :
    IsGreatest (thanDegrees Pthan μ) (μ xb) :=
  ⟨⟨xb, hb.1, le_refl _⟩, λ _ ⟨_, hx, hle⟩ => hle.trans (hμ hx hb.1 (hb.2 hx))⟩

/-- With greatest witnesses on both sides and measures monotone on each side, the
max-quantified comparative compares the greatest witnesses' measures. -/
theorem maxComparative_of_isGreatest [Preorder α] {Pmatrix Pthan : α → Prop} {μ : α → D}
    {xa xb : α} (ha : IsGreatest {x | Pmatrix x} xa) (hμa : MonotoneOn μ {x | Pmatrix x})
    (hb : IsGreatest {x | Pthan x} xb) (hμb : MonotoneOn μ {x | Pthan x}) :
    maxComparative Pmatrix Pthan μ ↔ μ xb < μ xa := by
  constructor
  · rintro ⟨δ, hδ, x, hx, hlt⟩
    exact lt_of_le_of_lt (hδ.2 ⟨xb, hb.1, le_refl _⟩)
      (lt_of_lt_of_le hlt (hμa hx ha.1 (ha.2 hx)))
  · exact λ hlt => ⟨μ xb, isGreatest_thanDegrees_of_isGreatest hb hμb, xa, ha.1, hlt⟩

/-- The than-clause degree set with the scale's zero degree added ([pasternak-2019]): its
maximum exists even without a than-clause witness. -/
def thanDegreesZero [Zero D] (Pthan : α → Prop) (μ : α → D) : Set D :=
  insert 0 (thanDegrees Pthan μ)

/-- The max-quantified comparative over `thanDegreesZero`: the than-clause positive is not
entailed. -/
def maxComparativeZero [Zero D] (Pmatrix Pthan : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (thanDegreesZero Pthan μ) δ ∧ ∃ x, Pmatrix x ∧ δ < μ x

/-- With no than-clause witness measuring above zero, the comparative holds of any matrix
witness measuring above zero: *Dee ran more than Evan did; in fact, Evan didn't run at all*. -/
theorem maxComparativeZero_of_forall_le_zero [Zero D] {Pmatrix Pthan : α → Prop} {μ : α → D}
    {x : α} (hx : Pmatrix x) (hpos : 0 < μ x) (hthan : ∀ y, Pthan y → μ y ≤ 0) :
    maxComparativeZero Pmatrix Pthan μ :=
  ⟨0, ⟨mem_insert _ _, λ _ hd => (mem_insert_iff.1 hd).elim le_of_eq
    λ ⟨y, hy, hle⟩ => hle.trans (hthan y hy)⟩, x, hx, hpos⟩

/-- When the than-clause degree set has a maximum, a matrix witness clears it iff it clears the
whole set, `Comparison.gt.overSet`. -/
theorem maxComparative_iff_gtOverSet (Pmatrix Pthan : α → Prop) (μ : α → D) :
    maxComparative Pmatrix Pthan μ ↔
      (∃ δ, IsGreatest (thanDegrees Pthan μ) δ) ∧
        ∃ x, Pmatrix x ∧ x ∈ Comparison.gt.overSet μ (thanDegrees Pthan μ) := by
  constructor
  · rintro ⟨δ, hδ, x, hx, hlt⟩
    exact ⟨⟨δ, hδ⟩, x, hx, λ d hd => lt_of_le_of_lt (hδ.2 hd) hlt⟩
  · rintro ⟨⟨δ, hδ⟩, x, hx, hclear⟩
    exact ⟨δ, hδ, x, hx, hclear hδ.1⟩

end MaxQuantified

/-! ### Degree quantifier scope

A DegP scopes relative to a quantifier `Q` over entities or worlds ([heim-2001]): low, inside
`Q` and applied to each entity's own degrees `Iic (μ x)`, or high, applied to `scopeDegrees Q μ`,
the degrees `d` at which `Q` holds of the entities reaching `d`. Over a monotone increasing `Q`
on a finite domain the two coincide for every DegP at an upper interval, comparatives and
equatives alike (`highScope_maxIn_iff_lowScope`); under a monotone decreasing `Q` the degree set
is an upper set and the maximum is undefined (`not_isGreatest_scopeDegrees`); the *exactly* and
*less* DegPs, whose intervals are not upper sets, separate the scopes. -/

section Scope
open Quantification
variable {α D : Type*}

section Preorder
variable [Preorder D] {Q : Quantifier α} {μ : α → D} {d : D}

/-- The maximum of `P` lies in `U`: the DegP denotations of [heim-2001], *-er than `t`* at
`U = Ioi t`, *less than `t`* at `Iio t`, *exactly `δ` -er than `t`* at `{t + δ}`, and the
equative at `Ici t`. -/
def maxIn (U P : Set D) : Prop := ∃ m ∈ U, IsGreatest P m

/-- The degrees at which `Q` holds of the entities reaching them, `Q (Comparison.ge.over μ d)`:
the degree predicate abstracted over `Q`'s scope. -/
def scopeDegrees (Q : Quantifier α) (μ : α → D) : Set D := {d | Q λ x => d ≤ μ x}

theorem mem_scopeDegrees : d ∈ scopeDegrees Q μ ↔ Q λ x => d ≤ μ x := Iff.rfl

/-- A DegP `𝒟` scoping under `Q`, applied to each entity's own degrees. -/
def lowScope (𝒟 : Set D → Prop) (Q : Quantifier α) (μ : α → D) : Prop :=
  Q λ x => 𝒟 (Iic (μ x))

/-- A DegP `𝒟` scoping over `Q`. -/
def highScope (𝒟 : Set D → Prop) (Q : Quantifier α) (μ : α → D) : Prop :=
  𝒟 (scopeDegrees Q μ)

/-- `some R` yields the than-clause degree set of `R`. -/
theorem scopeDegrees_some (R : α → Prop) (μ : α → D) :
    scopeDegrees (some_sem R) μ = thanDegrees R μ :=
  rfl

/-- `every R` yields the lower bounds of the measures of `R`. -/
theorem scopeDegrees_every (R : α → Prop) (μ : α → D) :
    scopeDegrees (every_sem R) μ = lowerBounds (μ '' {x | R x}) := by
  ext d
  exact (mem_lowerBounds.trans forall_mem_image).symm

/-- `no R` yields the complement of the than-clause degree set of `R`, the degrees no
`R`-witness reaches. -/
theorem scopeDegrees_no (R : α → Prop) (μ : α → D) :
    scopeDegrees (no_sem R) μ = (scopeDegrees (some_sem R) μ)ᶜ := by
  ext d
  exact (not_exists.trans (forall_congr' λ _ => not_and)).symm

theorem isLowerSet_scopeDegrees (hQ : Monotone Q) (μ : α → D) : IsLowerSet (scopeDegrees Q μ) :=
  λ _ _ h hd => hQ (λ _ hx => h.trans hx) hd

theorem isUpperSet_scopeDegrees (hQ : Antitone Q) (μ : α → D) : IsUpperSet (scopeDegrees Q μ) :=
  λ _ _ h hd => hQ (λ _ hx => h.trans hx) hd

/-- Under a monotone decreasing quantifier, negation, *at most n*, *refuse*, the degree set has
no maximum on a scale without a top: the high-scope reading is a presupposition failure. -/
theorem not_isGreatest_scopeDegrees [NoMaxOrder D] (hQ : Antitone Q) (μ : α → D) :
    ¬ ∃ m, IsGreatest (scopeDegrees Q μ) m :=
  λ ⟨_, hm⟩ => (isUpperSet_scopeDegrees hQ μ).not_bddAbove ⟨_, hm.1⟩ hm.bddAbove

/-- The degree set of a monotone increasing quantifier with a maximum is the maximum's principal
lower set: the degrees to which the shortest girl is tall. -/
theorem scopeDegrees_eq_Iic (hQ : Monotone Q) {m : D} (hm : IsGreatest (scopeDegrees Q μ) m) :
    scopeDegrees Q μ = Iic m :=
  (mem_upperBounds_iff_subset_Iic.1 hm.2).antisymm
    ((isLowerSet_scopeDegrees hQ μ).Iic_subset hm.1)

end Preorder

section PartialOrder
variable [PartialOrder D] {U P : Set D} {Q : Quantifier α} {μ : α → D}

theorem maxIn_Iic {a : D} : maxIn U (Iic a) ↔ a ∈ U :=
  ⟨λ ⟨_, hm, h⟩ => h.unique isGreatest_Iic ▸ hm, λ h => ⟨a, h, isGreatest_Iic⟩⟩

/-- Scope splitting: the DegP at the complementary interval is the negated DegP under the
presupposition that the maximum exists, *less than t* as *not as … as t*. -/
theorem maxIn_compl : maxIn Uᶜ P ↔ (∃ m, IsGreatest P m) ∧ ¬ maxIn U P :=
  ⟨λ ⟨m, hm, h⟩ => ⟨⟨m, h⟩, λ ⟨_, hm', h'⟩ => hm (h'.unique h ▸ hm')⟩,
    λ ⟨⟨m, h⟩, hn⟩ => ⟨m, λ hm => hn ⟨m, hm, h⟩, h⟩⟩

/-- The low scope of an interval DegP is `Q` of the entities measuring into the interval,
`Comparison.over` at that interval. -/
theorem lowScope_maxIn : lowScope (maxIn U) Q μ ↔ Q λ x => μ x ∈ U := by
  simp only [lowScope, maxIn_Iic]

/-- The high scope of an upper-interval DegP entails the low one over a monotone increasing
quantifier: if the shortest girl is taller than `t`, every girl is. -/
theorem lowScope_of_highScope (hQ : Monotone Q) (hU : IsUpperSet U)
    (h : highScope (maxIn U) Q μ) : lowScope (maxIn U) Q μ :=
  let ⟨_, hmU, hm⟩ := h; lowScope_maxIn.2 (hQ (λ _ hx => hU hx hmU) hm.1)

/-- The low scope entails the high one under `every` at every interval when the restrictor has a
least-measuring member: if every girl's height lies in the interval, so does the shortest
girl's. -/
theorem highScope_every_of_lowScope {R : α → Prop} (hR : ∃ x, R x ∧ ∀ y, R y → μ x ≤ μ y)
    (h : lowScope (maxIn U) (every_sem R) μ) : highScope (maxIn U) (every_sem R) μ := by
  rw [lowScope_maxIn] at h
  obtain ⟨x₀, hx₀, hmin⟩ := hR
  exact ⟨μ x₀, h x₀ hx₀, hmin, λ _ hd => hd x₀ hx₀⟩

/-- The high scope entails the low one under `some` at every interval: the tallest witness is a
witness. -/
theorem lowScope_some_of_highScope {R : α → Prop} (h : highScope (maxIn U) (some_sem R) μ) :
    lowScope (maxIn U) (some_sem R) μ := by
  obtain ⟨m, hmU, ⟨x, hx, hmx⟩, hub⟩ := h
  exact lowScope_maxIn.2 ⟨x, hx, show μ x ∈ U from hmx.antisymm (hub ⟨x, hx, le_rfl⟩) ▸ hmU⟩

end PartialOrder

section LinearOrder
variable [LinearOrder D] {U : Set D} {Q Q' : Quantifier α} {μ : α → D}

/-- On a finite domain the degree set of a monotone increasing quantifier that fails on the empty
predicate has a maximum as soon as it is nonempty, attained by an entity: the shortest girl
under *every girl*, the tallest under *some girl*. -/
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

/-- The low scope of an upper-interval DegP entails the high one over a monotone increasing
quantifier on a finite domain: if every girl is taller than `t`, so is the shortest. -/
theorem highScope_of_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥) (hU : IsUpperSet U)
    (h : lowScope (maxIn U) Q μ) : highScope (maxIn U) Q μ := by
  rw [lowScope_maxIn] at h
  have : Nonempty {x // μ x ∈ U} :=
    not_isEmpty_iff.1 λ h' => hQ₀ (hQ (λ x hx => h'.false ⟨x, hx⟩) h)
  obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min λ x : {x // μ x ∈ U} => μ x.1
  have hd₀ : μ x₀ ∈ scopeDegrees Q μ := hQ (λ x hx => hmin ⟨x, hx⟩) h
  obtain ⟨m, hm⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ ⟨_, hd₀⟩
  exact ⟨μ m, hU (hm.2 hd₀) hx₀, hm⟩

/-- Over a monotone increasing quantifier on a finite domain, a DegP at an upper interval,
comparative or equative, takes scope without truth-conditional effect. -/
theorem highScope_maxIn_iff_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hU : IsUpperSet U) : highScope (maxIn U) Q μ ↔ lowScope (maxIn U) Q μ :=
  ⟨lowScope_of_highScope hQ hU, highScope_of_lowScope hQ hQ₀ hU⟩

/-- *Less than `t`* over a monotone increasing quantifier, high, is *not as … as `t`*, low: the
scope-splitting reading, `NEG + as … as`. -/
theorem highScope_maxIn_Iio_iff [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hne : (scopeDegrees Q μ).Nonempty) {t : D} :
    highScope (maxIn (Iio t)) Q μ ↔ ¬ Q λ x => t ≤ μ x := by
  have h := highScope_maxIn_iff_lowScope (μ := μ) hQ hQ₀ (isUpperSet_Ici t)
  simp only [lowScope_maxIn, mem_Ici] at h
  rw [← compl_Ici, ← h]
  obtain ⟨x, hx⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ hne
  exact maxIn_compl.trans (and_iff_right ⟨_, hx⟩)

/-- Under the meet of a quantifier with a monotone decreasing one, *exactly n* as *at least n*
and *at most n*, the maximum of the degree set, when defined, is that of the other conjunct:
high-scope *exactly two girls are taller than t* means *at least two*. -/
theorem isGreatest_scopeDegrees_of_inf (hQ' : Antitone Q') {m : D}
    (h : IsGreatest (scopeDegrees (Q ⊓ Q') μ) m) : IsGreatest (scopeDegrees Q μ) m :=
  ⟨h.1.1, λ _ hd => le_of_not_gt λ hmd =>
    (h.2 ⟨hd, hQ' (λ _ hx => hmd.le.trans hx) h.1.2⟩).not_gt hmd⟩

/-- On a dense scale the maximum of a degree set with a maximum is the greatest lower bound of
its complement: the maximum of [heim-2001]'s trivalent entry agrees with the bivalent one. -/
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

end Scope

/-! ### Downward-entailingness of than-clauses -/

/-- Universal quantification over a domain is antitone in the domain, the generic monotonicity
fact behind than-clauses being downward-entailing; [hoeksema-1983]'s anti-additivity result is
in `Studies/Hoeksema1983.lean`. -/
theorem comparative_than_DE {α : Type*} (R : α → α → Prop) (μ_a : α)
    (D₁ D₂ : Set α) (h_sub : D₁ ⊆ D₂) (h : ∀ d ∈ D₂, R μ_a d) :
    ∀ d ∈ D₁, R μ_a d :=
  λ d hd => h d (h_sub hd)

/-! ### Superlatives

*-est* universally quantifies the comparative over a comparison class ([heim-1999]; the semantic
reflex of [bobaljik-2012]'s containment `[[[ADJ] CMPR] SPRL]`): absolute readings fix the class
extensionally, relative readings via focus alternatives ([szabolcsi-1986]). -/

section Superlative
variable {Entity D : Type*} [LinearOrder D]

/-- Absolute superlative: `x` is the G-est entity in comparison class `C`, beating every other
member on the comparative. -/
def absoluteSuperlative (μ : Entity → D) (C : Set Entity) (x : Entity) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → comparativeSem μ x y .positive

/-- Relative superlative ([heim-1999]): the focused alternative's entity outranks every other
alternative's under `f`. -/
def relativeSuperlative {Alt : Type*} (μ : Entity → D) (f : Alt → Entity)
    (focusedAlt : Alt) (alternatives : Set Alt) : Prop :=
  ∀ a ∈ alternatives, a ≠ focusedAlt →
    comparativeSem μ (f focusedAlt) (f a) .positive

/-- At most one entity satisfies the absolute superlative. -/
theorem absolute_unique (μ : Entity → D) (C : Set Entity) (x y : Entity)
    (hx : absoluteSuperlative μ C x) (hy : absoluteSuperlative μ C y) :
    x = y := by
  by_contra hne
  exact absurd (hx.2 y hy.1 (Ne.symm hne))
    (not_lt.mpr (le_of_lt (hy.2 x hx.1 hne)))

/-- The absolute superlative makes `μ x` the greatest element of the degree image `μ '' C`; the
converse fails under ties. -/
theorem absoluteSuperlative_isGreatest (μ : Entity → D) (C : Set Entity)
    (x : Entity) (h : absoluteSuperlative μ C x) :
    IsGreatest (μ '' C) (μ x) := by
  refine ⟨mem_image_of_mem μ h.1, λ d hd => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hd
  rcases eq_or_ne y x with rfl | hne
  · exact le_refl _
  · exact le_of_lt (h.2 y hy hne)

end Superlative

end Degree
