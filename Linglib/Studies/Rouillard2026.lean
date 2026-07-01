import Mathlib.Data.NNRat.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Linglib.Core.Order.Boundedness
import Linglib.Core.Order.IntervalContent
import Linglib.Semantics.Degree.Predicate
import Linglib.Core.Order.Interval
import Linglib.Semantics.Entailment.Extremum
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Aspect.SubintervalProperty
import Linglib.Features.Aktionsart
import Linglib.Semantics.Aspect.Boundedness
import Linglib.Fragments.English.TemporalExpressions

/-!
# Rouillard 2026: Temporal *in*-Adverbials and the Maximal Informativity Principle
[rouillard-2026] [fox-hackl-2006] [fox-2007]
[beck-rullmann-1999] [krifka-1989] [krifka-1998]
[vendler-1957] [ladusaw-1979] [iatridou-zeijlstra-2021]
[hoeksema-2006] [gajewski-2011] [von-fintel-iatridou-2019]

[rouillard-2026] "Maximal informativity accounts for the distribution
of temporal *in*-adverbials" (*Linguistics and Philosophy* 49:1–56).

## Core contribution

Temporal *in*-adverbials (TIAs) lead a double life:

- **E-TIAs** ("wrote a paper *in three days*") measure event durations.
  Acceptable only with telic VPs.
- **G-TIAs** ("hasn't been sick *in three days*") measure gap durations.
  NPI behavior: acceptable only in negative perfects.

Both distributional restrictions follow from a single principle: the
**Maximal Informativity Principle (MIP)**. For some constituent γ
containing the TIA, the numeral must be capable of being the maximally
informative value of γ's derived property. Where no maximally informative
numeral exists ("information collapse"), the TIA is blocked.

## Main declarations

- `eTIA_atelic_not_licensed`: atelic E-TIAs fail MIP licensing — the
  subinterval property makes the derived property constant (information
  collapse).
- `eTIA_telic_upwardMonotone` / `upwardMonotone_hasIsLeast_of_witness`:
  telic E-TIAs are upward monotone, with a least-true numeral at the
  event duration.
- `no_smallest_open_PTS_geometric`: density witness — no smallest open
  PTS contains a given closed runtime.
- `gTIAOpen_not_MIP_licensed`: positive G-TIAs over dense time are not
  MIP-licensed (the end-to-end information-collapse discharge), with the
  `ratLength` model over `ℚ` witnessing satisfiability.
- `downwardMonotone_hasIsGreatest_of_bound` / `gTIANeg_hasIsGreatest`:
  negated G-TIAs have a greatest true numeral — the gap length.
- `eTIA_all_predicted` / `gTIA_all_predicted` / `surviving_is_neg_gtia_pfv`:
  the empirical predictions (the paper's Table 1).
-/

namespace NonemptyInterval

/-- Interval boundary type maps to scale boundedness: closed runtimes
    correspond to closed scales (licensed), open PTSs to open scales
    (blocked/information collapse). [rouillard-2026]'s interval
    generalization, consumed by the MIP licensing pipeline below. -/
def BoundaryType.toBoundedness : BoundaryType → Core.Order.Boundedness
  | .closed => .closed
  | .open_ => .open_

theorem closedBoundary_licensed :
    (BoundaryType.toBoundedness .closed).IsLicensed := trivial

theorem openBoundary_blocked :
    ¬ (BoundaryType.toBoundedness .open_).IsLicensed := id

instance : Core.Order.LicensingPipeline BoundaryType where
  toBoundedness := BoundaryType.toBoundedness

end NonemptyInterval

namespace Rouillard2026

open NonemptyInterval
open Semantics.Aspect
open Semantics.Aspect.SubintervalProperty
open Features
open Core.Order
open Degree
open Entailment
open English.TemporalExpressions

variable {W Time : Type*} [LinearOrder Time]
variable {α : Type*} [AddCommMonoid α] [LinearOrder α]

/-! ### Time measure -/

/-- A temporal measure: an `IsIntervalContent` (additivity, [rouillard-2026]
    eq. 6; positivity, eq. 7) together with two saturation axioms — richness
    of `Time` lets any interval be trimmed or right-anchored-extended to any
    target measure (PTSs are anchored at speech time). Instantiate `α := ℕ`
    for the discrete integer-numeral reading or `α := ℚ≥0` over dense time
    for the reading that drives the G-TIA collapse (`ratLength` below). -/
class TimeMeasure (Time : Type*) [LinearOrder Time] {α : Type*}
    [AddCommMonoid α] [LinearOrder α]
    (μ : NonemptyInterval Time → α) : Prop extends IsIntervalContent μ where
  /-- Any interval can be subdivided to a subinterval with a given smaller
      measure. -/
  subdivisible : ∀ (i : NonemptyInterval Time) (m : α), m ≤ μ i →
    ∃ j : NonemptyInterval Time, j ≤ i ∧ μ j = m
  /-- Right-anchored left-extension: any interval can be extended to a
      given larger measure keeping its right endpoint fixed. -/
  extensibleLeft : ∀ (i : NonemptyInterval Time) (m : α), μ i ≤ m →
    ∃ j : NonemptyInterval Time, i ≤ j ∧ j.snd = i.snd ∧ μ j = m

namespace TimeMeasure

/-- Any interval can be extended to a superinterval with a given larger
    measure: weakening of `extensibleLeft` (forget the right anchor). -/
theorem extensible {μ : NonemptyInterval Time → α} [TimeMeasure Time μ]
    (i : NonemptyInterval Time) (m : α) (h : μ i ≤ m) :
    ∃ j : NonemptyInterval Time, i ≤ j ∧ μ j = m :=
  let ⟨j, hij, _, hjμ⟩ := TimeMeasure.extensibleLeft i m h
  ⟨j, hij, hjμ⟩

end TimeMeasure

/-! ### Generalized intervals with open/closed boundaries -/

/-- A generalized interval with specified boundary types.
    Extends the basic `NonemptyInterval` with open/closed annotations on each end.
    [rouillard-2026] eq. (14a–b), (99a–b). -/
structure GInterval (Time : Type*) [LinearOrder Time] where
  /-- Left endpoint -/
  left : Time
  /-- Right endpoint -/
  right : Time
  /-- Left boundary type: closed [m or open]m -/
  leftType : BoundaryType
  /-- Right boundary type: closed m] or open m[ -/
  rightType : BoundaryType
  /-- The endpoints are ordered -/
  valid : left ≤ right

namespace GInterval

/-- A closed interval [m₁, m₂]: both endpoints included.
    [rouillard-2026] eq. (14a): C := {t | min(t) ⊑ᵢ t ∧ max(t) ⊑ᵢ t}. -/
def closed (i : NonemptyInterval Time) : GInterval Time where
  left := i.fst
  right := i.snd
  leftType := .closed
  rightType := .closed
  valid := i.fst_le_snd

/-- An open interval]m₁, m₂[: both endpoints excluded.
    [rouillard-2026] eq. (14b): O := {t | min(t) ⊄ᵢ t ∨ max(t) ⊄ᵢ t}. -/
def open_ (i : NonemptyInterval Time) : GInterval Time where
  left := i.fst
  right := i.snd
  leftType := .open_
  rightType := .open_
  valid := i.fst_le_snd

/-- The o(t) operation: open counterpart of a time.
    [rouillard-2026] eq. (99a): if t is open, o(t) = t; if t is closed,
    o(t) is the open interval with the same endpoints. -/
def toOpen (gi : GInterval Time) : GInterval Time :=
  { gi with leftType := .open_, rightType := .open_ }

/-- The c(t) operation: closed counterpart of a time.
    [rouillard-2026] eq. (99b): if t is closed, c(t) = t; if t is open,
    c(t) adds the endpoints. -/
def toClosed (gi : GInterval Time) : GInterval Time :=
  { gi with leftType := .closed, rightType := .closed }

/-- Is this interval closed (both boundaries included)? -/
def isClosed (gi : GInterval Time) : Prop :=
  gi.leftType = .closed ∧ gi.rightType = .closed

/-- Is this interval open (both boundaries excluded)? -/
def isOpen (gi : GInterval Time) : Prop :=
  gi.leftType = .open_ ∧ gi.rightType = .open_

/-- Containment for generalized intervals: m is in gi.
    For closed endpoints, ≤ is used; for open endpoints, <. -/
def gcontains (gi : GInterval Time) (m : Time) : Prop :=
  (match gi.leftType with
   | .closed => gi.left ≤ m
   | .open_ => gi.left < m) ∧
  (match gi.rightType with
   | .closed => m ≤ gi.right
   | .open_ => m < gi.right)

/-- Generalized subinterval: gi₁ ⊆ gi₂ (every moment in gi₁ is in gi₂). -/
def gsubinterval (gi₁ gi₂ : GInterval Time) : Prop :=
  ∀ m : Time, gi₁.gcontains m → gi₂.gcontains m

/-- Convert a closed GInterval back to the basic NonemptyInterval type. -/
def toInterval (gi : GInterval Time) : NonemptyInterval Time :=
  ⟨⟨gi.left, gi.right⟩, gi.valid⟩

/-- The closed counterpart of an open interval is always closed. -/
@[simp] theorem toClosed_isClosed (gi : GInterval Time) : gi.toClosed.isClosed :=
  ⟨rfl, rfl⟩

/-- The open counterpart is always open. -/
@[simp] theorem toOpen_isOpen (gi : GInterval Time) : gi.toOpen.isOpen :=
  ⟨rfl, rfl⟩

/-- toClosed is idempotent. -/
@[simp] theorem toClosed_idempotent (gi : GInterval Time) :
    gi.toClosed.toClosed = gi.toClosed := rfl

/-- toOpen is idempotent. -/
@[simp] theorem toOpen_idempotent (gi : GInterval Time) :
    gi.toOpen.toOpen = gi.toOpen := rfl

/-- The closed counterpart of an interval contains its endpoints (definitional). -/
@[simp] theorem closed_gcontains_start (i : NonemptyInterval Time) :
    (closed i).gcontains i.fst := ⟨le_refl _, i.fst_le_snd⟩

@[simp] theorem closed_gcontains_finish (i : NonemptyInterval Time) :
    (closed i).gcontains i.snd := ⟨i.fst_le_snd, le_refl _⟩

/-- A closed interval contained in an open generalized interval forces strict
    inequalities at both endpoints: instantiate `gsubinterval` at the closed
    endpoints and unfold `gcontains`. -/
theorem gsubinterval_closed_open_strict
    (rt : NonemptyInterval Time) (gi : GInterval Time)
    (h_open : gi.isOpen) (h_sub : (closed rt).gsubinterval gi) :
    gi.left < rt.fst ∧ rt.snd < gi.right := by
  have h_start := h_sub rt.fst (closed_gcontains_start rt)
  have h_finish := h_sub rt.snd (closed_gcontains_finish rt)
  obtain ⟨hL, hR⟩ := h_open
  refine ⟨?_, ?_⟩
  · -- gi.left < rt.fst: from h_start.1 with leftType = .open_
    have := h_start.1
    rw [hL] at this
    exact this
  · -- rt.snd < gi.right: from h_finish.2 with rightType = .open_
    have := h_finish.2
    rw [hR] at this
    exact this

end GInterval

/-! ### Prior time spans -/

/-- Prior time span: the maximal interval right-bounded by `s` with
    measure `n`, over `GInterval` so open-vs-closed boundary tags are
    carried structurally. [rouillard-2026] eq. (50). -/
def pts (n : α) (μ : NonemptyInterval Time → α) [TimeMeasure Time μ] (s : Time)
    (gi : GInterval Time) : Prop :=
  gi.right = s ∧ μ gi.toInterval = n

/-! ### E-TIA semantics -/

/-- The preposition *in* as an event-level adverbial (E-TIA reading).
    The event's runtime is included in the measure-phrase's bound.
    [rouillard-2026] eq. (62) instantiated at M = τ. -/
def inETIA (e : Event Time) (bound : NonemptyInterval Time) : Prop :=
  e.τ ≤ bound

/-- E-TIA derived property: at world `w`, value `n` is true iff there is
    a P-event whose runtime is included in some `n`-unit time, and that
    `n`-unit time falls within `g1`. [rouillard-2026] eq. (77). -/
def eTIAProperty (P : W → Event Time → Prop) (μ : NonemptyInterval Time → α)
    [TimeMeasure Time μ] (g1 : NonemptyInterval Time) : α → W → Prop :=
  fun n w => ∃ t : NonemptyInterval Time, μ t = n ∧
    ∃ e : Event Time, P w e ∧ e.τ ≤ g1 ∧ e.τ ≤ t

/-! ### G-TIA semantics over open generalized intervals -/

/-- G-TIA derived property: at world `w`, value `n` is true iff there is
    an OPEN PTS of measure `n` ending at `s` containing the closed runtime
    of a P-event. The openness of the PTS is carried structurally by
    `GInterval`. [rouillard-2026] eq. (94) revised with eq. (101). -/
def gTIAPropertyOpen (P : W → Event Time → Prop) (μ : NonemptyInterval Time → α)
    [TimeMeasure Time μ] (s : Time) : α → W → Prop :=
  fun n w => ∃ ptsGI : GInterval Time,
    ptsGI.isOpen ∧
    ptsGI.right = s ∧
    μ ptsGI.toInterval = n ∧
    ∃ e : Event Time, P w e ∧ (GInterval.closed e.τ).gsubinterval ptsGI

/-- The negation of `gTIAPropertyOpen`, used for G-TIAs in negative
    contexts (where the property "no event in the n-unit open PTS" holds
    iff `gTIAPropertyOpen` is false). -/
def gTIAPropertyOpenNeg (P : W → Event Time → Prop) (μ : NonemptyInterval Time → α)
    [TimeMeasure Time μ] (s : Time) : α → W → Prop :=
  fun n w => ¬ gTIAPropertyOpen P μ s n w

/-- The positive G-TIA property is upward monotone: a wider gap window with
    the same right anchor still contains the event runtime, via
    `TimeMeasure.extensibleLeft`. -/
theorem gTIAPropertyOpen_upwardMonotone {μ : NonemptyInterval Time → α}
    [TimeMeasure Time μ] (P : W → Event Time → Prop) (s : Time) :
    IsUpwardMonotone (gTIAPropertyOpen P μ s) := by
  rintro n m hnm w ⟨ptsGI, hOpen, hRight, hμ, e, hP, hSub⟩
  obtain ⟨j, hij, hjsnd, hjμ⟩ :=
    TimeMeasure.extensibleLeft ptsGI.toInterval m (hμ ▸ hnm)
  obtain ⟨hL, hR⟩ := GInterval.gsubinterval_closed_open_strict e.τ ptsGI hOpen hSub
  refine ⟨⟨j.fst, j.snd, .open_, .open_, j.fst_le_snd⟩, ⟨rfl, rfl⟩, ?_, hjμ, e, hP, ?_⟩
  · show j.snd = s
    rw [hjsnd]; exact hRight
  · intro p hp
    have hp1 : e.τ.fst ≤ p := hp.1
    have hp2 : p ≤ e.τ.snd := hp.2
    refine ⟨?_, ?_⟩
    · show j.fst < p
      exact lt_of_le_of_lt hij.1 (lt_of_lt_of_le hL hp1)
    · show p < j.snd
      rw [hjsnd]
      exact lt_of_le_of_lt hp2 hR

/-- The negated G-TIA property is downward monotone: if no event sits in
    the `n`-unit gap window, none sits in any narrower one. Discharges the
    monotonicity that `gTIANeg_hasIsGreatest` needs. -/
theorem gTIAPropertyOpenNeg_downwardMonotone {μ : NonemptyInterval Time → α}
    [TimeMeasure Time μ] (P : W → Event Time → Prop) (s : Time) :
    IsDownwardMonotone (gTIAPropertyOpenNeg P μ s) :=
  fun x y hxy w hy hx =>
    hy (gTIAPropertyOpen_upwardMonotone P s x y hxy w hx)

/-! ### The MIP licensing predicate

`MIP_Licensed` and `MIP_LicensedDown` are defined in
    `Semantics/Entailment/Extremum.lean` and reused here. They
    combine `Degree.AdmitsOptimum P` (non-constancy: the *atelic*
    failure mode) with the per-world existence of a `Set.IsLeast` /
    `Set.IsGreatest` (mathlib): a most-informative numeral exists at some
    world. The two conjuncts capture two separate failure modes:
    information collapse (E-TIA atelic; fails `AdmitsOptimum`) and
    no-extremum (positive G-TIA; fails per-world `IsLeast`). -/

/-! ### E-TIA atelic case: subinterval property → information collapse -/

/-- **E-TIA information collapse for atelic VPs**. When a VP has the
    subinterval property, the E-TIA derived property is constant: every
    numeral yields a true proposition at any world where any does, so no
    numeral is more informative than another. [rouillard-2026] §4.1.1. -/
theorem eTIA_atelic_collapse {μ : NonemptyInterval Time → α} [TimeMeasure Time μ]
    (P : W → Event Time → Prop) (g1 : NonemptyInterval Time)
    (hSub : HasSubintervalProp P) :
    IsConstant (α := α) (eTIAProperty P μ g1) := by
  suffices h : ∀ n m w, eTIAProperty P μ g1 n w → eTIAProperty P μ g1 m w from
    fun n m w => ⟨h n m w, h m n w⟩
  intro n m w ⟨_, _, e, hP, hg1, _⟩
  rcases le_total m (μ e.τ) with hle | hge
  · obtain ⟨j, hj_sub, hj_μ⟩ := TimeMeasure.subdivisible e.τ m hle
    refine ⟨j, hj_μ, ⟨j, .dynamic⟩, hSub e w hP j hj_sub ⟨j, .dynamic⟩ rfl,
      ⟨?_, ?_⟩, ⟨le_refl _, le_refl _⟩⟩
    · exact le_trans hg1.1 hj_sub.1
    · exact le_trans hj_sub.2 hg1.2
  · obtain ⟨j, hj_sup, hj_μ⟩ := TimeMeasure.extensible e.τ m hge
    exact ⟨j, hj_μ, e, hP, hg1, hj_sup⟩

/-- Atelic E-TIA fails the `AdmitsOptimum` half of MIP licensing. -/
theorem eTIA_atelic_no_optimum {μ : NonemptyInterval Time → α} [TimeMeasure Time μ]
    (P : W → Event Time → Prop) (g1 : NonemptyInterval Time)
    (hSub : HasSubintervalProp P) :
    ¬ AdmitsOptimum (eTIAProperty P μ g1) :=
  fun h => h (eTIA_atelic_collapse P g1 hSub)

/-- Atelic E-TIA is not MIP-licensed. -/
theorem eTIA_atelic_not_licensed {μ : NonemptyInterval Time → α} [TimeMeasure Time μ]
    (P : W → Event Time → Prop) (g1 : NonemptyInterval Time)
    (hSub : HasSubintervalProp P) :
    ¬ MIP_Licensed (eTIAProperty P μ g1) :=
  fun ⟨hAdm, _⟩ => eTIA_atelic_no_optimum P g1 hSub hAdm

/-! ### E-TIA telic case: upward monotone, smallest-true at event duration -/

/-- **Quantized predicates yield upward-monotone E-TIA properties**.
    [rouillard-2026] §4.1.1: when P is telic, the derived E-TIA
    property is upward monotone — the same event witnesses larger
    measures via `TimeMeasure.extensible`. -/
theorem eTIA_telic_upwardMonotone {μ : NonemptyInterval Time → α} [TimeMeasure Time μ]
    (P : W → Event Time → Prop) (g1 : NonemptyInterval Time) :
    IsUpwardMonotone (eTIAProperty P μ g1) := by
  intro n m hnm w ⟨t, hμ, e, hP, hg1, hsub⟩
  have h_le : μ t ≤ m := by rw [hμ]; exact hnm
  obtain ⟨j, hj_sup, hj_μ⟩ := TimeMeasure.extensible (μ := μ) t m h_le
  exact ⟨j, hj_μ, e, hP, hg1,
    ⟨le_trans hj_sup.1 hsub.1, le_trans hsub.2 hj_sup.2⟩⟩

/-- For an upward-monotone family with a witness at some world, the
    per-world set `{y | P y w}` has a least element via `Nat.find`. The
    statement is in mathlib idiom (`IsLeast`); the cross-world `IsMaxInf`
    bridge is in `Extremum.lean` (`isMaxInf_of_isLeast_upward`). Pinned to
    `ℕ`: extremum existence needs a well-founded codomain, which dense `α`
    deliberately lacks (that failure IS the G-TIA collapse below). -/
theorem upwardMonotone_hasIsLeast_of_witness {W : Type*}
    {P : ℕ → W → Prop} (_hUp : IsUpwardMonotone P) (w : W)
    [DecidablePred (fun n => P n w)]
    (h_witness : ∃ n, P n w) :
    ∃ x, IsLeast {y | P y w} x := by
  classical
  refine ⟨Nat.find h_witness, Nat.find_spec h_witness, fun y hy => ?_⟩
  exact Nat.find_le hy

/-! ### G-TIA geometric density: no smallest open PTS -/

/-- **No smallest open PTS includes a closed runtime** (geometric witness).
    [rouillard-2026] §4.2.2: under density on `Time`, an open PTS containing
    a closed runtime always has a strictly smaller open PTS still containing
    it — pick a moment between the open boundary and the closed start.

    `gTIAOpen_no_isLeast` below turns this into measure-level collapse via
    additivity and positivity; `gTIAOpen_not_MIP_licensed` is the end-to-end
    blocking result. (For `α := ℕ` over dense time the `TimeMeasure` axioms
    are unsatisfiable — positivity forces an infinite descending ℕ-chain —
    so the discrete reading lives on discrete `Time` only, where E-TIA
    results apply but the density argument does not.) -/
theorem no_smallest_open_PTS_geometric [DenselyOrdered Time]
    (rt : NonemptyInterval Time) (ptsGI : GInterval Time)
    (h_open : ptsGI.isOpen)
    (h_sub : (GInterval.closed rt).gsubinterval ptsGI) :
    ∃ ptsGI' : GInterval Time,
      ptsGI'.isOpen ∧
      (GInterval.closed rt).gsubinterval ptsGI' ∧
      ptsGI'.right = ptsGI.right ∧
      ptsGI.left < ptsGI'.left := by
  obtain ⟨h_strict_left, h_strict_right⟩ :=
    GInterval.gsubinterval_closed_open_strict rt ptsGI h_open h_sub
  obtain ⟨m, hm_left, hm_right⟩ := DenselyOrdered.dense _ _ h_strict_left
  -- m sits strictly between ptsGI.left and rt.fst.
  have hm_valid : m ≤ ptsGI.right :=
    le_of_lt (lt_of_lt_of_le hm_right (le_trans rt.fst_le_snd (le_of_lt h_strict_right)))
  let ptsGI' : GInterval Time :=
    { left := m, right := ptsGI.right
    , leftType := .open_, rightType := .open_
    , valid := hm_valid }
  refine ⟨ptsGI', ⟨rfl, rfl⟩, ?_, rfl, hm_left⟩
  intro p hp
  -- hp : (closed rt).gcontains p, definitionally rt.fst ≤ p ∧ p ≤ rt.snd.
  have hp1 : rt.fst ≤ p := hp.1
  have hp2 : p ≤ rt.snd := hp.2
  refine ⟨?_, ?_⟩
  · -- ptsGI'.gcontains p (left side, open): m < p
    show m < p
    exact lt_of_lt_of_le hm_right hp1
  · -- ptsGI'.gcontains p (right side, open): p < ptsGI.right
    show p < ptsGI.right
    exact lt_of_le_of_lt hp2 h_strict_right

/-- **Positive G-TIA: no least true value**. Under dense `Time`, additivity
    and positivity let every witnessing open PTS shrink to a strictly
    smaller-measure open PTS still containing the runtime, so the per-world
    true set has no least element. [rouillard-2026] §4.2.2. -/
theorem gTIAOpen_no_isLeast [DenselyOrdered Time] [AddRightStrictMono α]
    {μ : NonemptyInterval Time → α} [TimeMeasure Time μ]
    (P : W → Event Time → Prop) (s : Time) (w : W) (x : α) :
    ¬ IsLeast {y | gTIAPropertyOpen P μ s y w} x := by
  rintro ⟨⟨ptsGI, hOpen, hRight, hμ, e, hP, hSub⟩, hLB⟩
  obtain ⟨ptsGI', hOpen', hSub', hRight', hLeft'⟩ :=
    no_smallest_open_PTS_geometric e.τ ptsGI hOpen hSub
  -- the shrunken open PTS witnesses a strictly smaller true value
  have hmem : gTIAPropertyOpen P μ s (μ ptsGI'.toInterval) w :=
    ⟨ptsGI', hOpen', hRight'.trans hRight, rfl, e, hP, hSub'⟩
  have he : ptsGI'.toInterval = ⟨⟨ptsGI'.left, ptsGI.right⟩, hRight' ▸ ptsGI'.valid⟩ :=
    NonemptyInterval.ext (Prod.ext rfl hRight')
  have hlt : μ ptsGI'.toInterval < x := by
    rw [← hμ, he]
    exact IsIntervalContent.measure_lt_of_left_lt μ hLeft' (hRight' ▸ ptsGI'.valid)
  exact absurd (hLB hmem) (not_le.mpr hlt)

/-- **Positive G-TIAs are not MIP-licensed** over dense time: the
    least-true-numeral leg of `MIP_Licensed` fails at every world. The
    end-to-end discharge of the information-collapse argument
    ([rouillard-2026] §4.2.2) that the ℕ-valued measure could not provide. -/
theorem gTIAOpen_not_MIP_licensed [DenselyOrdered Time] [AddRightStrictMono α]
    {μ : NonemptyInterval Time → α} [TimeMeasure Time μ]
    (P : W → Event Time → Prop) (s : Time) :
    ¬ MIP_Licensed (gTIAPropertyOpen P μ s) :=
  fun ⟨_, w, x, hLeast⟩ => gTIAOpen_no_isLeast P s w x hLeast

/-! ### The rational length model

Non-vacuity witness: over `Time := ℚ`, interval length valued in `ℚ≥0` is
a `TimeMeasure`, so the hypotheses of `gTIAOpen_not_MIP_licensed` are
jointly satisfiable at a concrete dense model. -/

/-- Interval length over rational time, as a nonnegative rational. -/
def ratLength (i : NonemptyInterval ℚ) : ℚ≥0 :=
  ⟨i.snd - i.fst, sub_nonneg.mpr i.fst_le_snd⟩

instance : IsIntervalContent ratLength where
  additive a b c hab hbc := by
    apply NNRat.ext
    show c - a = (b - a) + (c - b)
    ring
  positive a b h := by
    rw [← NNRat.coe_pos]
    show (0 : ℚ) < b - a
    linarith

instance : TimeMeasure ℚ ratLength where
  subdivisible i m h := by
    have hm : (m : ℚ) ≤ i.snd - i.fst := NNRat.coe_le_coe.mpr h
    refine ⟨⟨⟨i.fst, i.fst + (m : ℚ)⟩, by linarith [m.coe_nonneg]⟩,
      ⟨le_refl _, ?_⟩, ?_⟩
    · show i.fst + (m : ℚ) ≤ i.snd
      linarith
    · apply NNRat.ext
      show i.fst + (m : ℚ) - i.fst = (m : ℚ)
      ring
  extensibleLeft i m h := by
    have hm : i.snd - i.fst ≤ (m : ℚ) := NNRat.coe_le_coe.mpr h
    refine ⟨⟨⟨i.snd - (m : ℚ), i.snd⟩, by linarith [m.coe_nonneg]⟩,
      ⟨?_, le_refl _⟩, rfl, ?_⟩
    · show i.snd - (m : ℚ) ≤ i.fst
      linarith
    · apply NNRat.ext
      show i.snd - (i.snd - (m : ℚ)) = (m : ℚ)
      ring

/-- The blocking theorem's hypotheses discharge at the rational length
    model: positive G-TIAs over `ℚ`-time are not MIP-licensed. -/
example {W : Type*} (P : W → Event ℚ → Prop) (s : ℚ) :
    ¬ MIP_Licensed (gTIAPropertyOpen P ratLength s) :=
  gTIAOpen_not_MIP_licensed P s

/-! ### Negated G-TIA: greatest true numeral at the gap length -/

/-- For a downward-monotone family over ℕ with a true witness and a failing
    bound at world `w`, the per-world set `{y | P y w}` has a greatest
    element. Dual of `upwardMonotone_hasIsLeast_of_witness`; the cross-world
    bridge is `Extremum.isMaxInf_of_isGreatest_downward`. Pinned to `ℕ` for
    the same well-foundedness reason as its dual. -/
theorem downwardMonotone_hasIsGreatest_of_bound {W : Type*}
    {P : ℕ → W → Prop} (hDown : IsDownwardMonotone P) (w : W)
    [DecidablePred (fun n => P n w)]
    (h_witness : ∃ n, P n w) (h_bound : ∃ n, ¬ P n w) :
    ∃ x, IsGreatest {y | P y w} x := by
  classical
  obtain ⟨n₀, hn₀⟩ := h_witness
  have h_pos : 0 < Nat.find h_bound :=
    Nat.pos_of_ne_zero fun h =>
      (h ▸ Nat.find_spec h_bound) (hDown 0 n₀ (Nat.zero_le _) w hn₀)
  refine ⟨Nat.find h_bound - 1,
    not_not.mp (Nat.find_min h_bound (Nat.sub_lt h_pos one_pos)),
    fun y hy => ?_⟩
  have h_lt : y < Nat.find h_bound := by
    by_contra h_ge
    exact Nat.find_spec h_bound (hDown _ y (not_lt.mp h_ge) w hy)
  omega

/-- **Negated G-TIAs satisfy the MIP at the gap length**. With a true
    witness and a failing bound, a greatest true numeral exists —
    [rouillard-2026] eq. (104)/(110): there can be a largest open interval
    *excluding* a closed time, though never a smallest one including it.
    Downward monotonicity is supplied by
    `gTIAPropertyOpenNeg_downwardMonotone` (no longer hypothesis-gated). -/
theorem gTIANeg_hasIsGreatest {μ : NonemptyInterval Time → ℕ} [TimeMeasure Time μ]
    (P : W → Event Time → Prop) (s : Time) (w : W)
    [DecidablePred (fun n => gTIAPropertyOpenNeg P μ s n w)]
    (h_witness : ∃ n, gTIAPropertyOpenNeg P μ s n w)
    (h_bound : ∃ n, ¬ gTIAPropertyOpenNeg P μ s n w) :
    ∃ x, IsGreatest {y | gTIAPropertyOpenNeg P μ s y w} x :=
  downwardMonotone_hasIsGreatest_of_bound
    (gTIAPropertyOpenNeg_downwardMonotone P s) w h_witness h_bound

/-! ### Boundedness pipeline

The Vendler-class boundedness chain
`VendlerClass →.telicity Telicity →.toMereoTag MereoTag →.toBoundedness Boundedness`
consumed by the empirical predictions below. Codebase plumbing
(`Features.Aktionsart`), not a claim from [rouillard-2026]. -/

/-- Telic VPs route through `LicensingPipeline` to the licensed (closed)
    boundedness tag. -/
theorem telic_predicts_licensing (c : VendlerClass) (h : c.telicity = .telic) :
    (LicensingPipeline.toBoundedness c).IsLicensed := by
  show (c.telicity.toMereoTag.toBoundedness).IsLicensed
  rw [h]; trivial

/-- Atelic VPs route through `LicensingPipeline` to the unlicensed (open)
    boundedness tag. -/
theorem atelic_predicts_blocking (c : VendlerClass) (h : c.telicity = .atelic) :
    ¬ (LicensingPipeline.toBoundedness c).IsLicensed := by
  show ¬ (c.telicity.toMereoTag.toBoundedness).IsLicensed
  rw [h]; exact id

/-! ### Cross-source licensing sentry

Formalizer synthesis, not attributable to [rouillard-2026] — the paper
engages only telicity/Vendler aspect and its own closed/open interval
distinction. These sentries pin the bodies of every registered
`LicensingPipeline` instance in one place, so a silent instance change is
caught here; pairwise agreement between any two sources is
`LicensingPipeline.universal`. -/

/-- Every registered `LicensingPipeline` source maps its "closed" variant to
    licensed. -/
theorem sources_agree_closed :
    LicensingPipeline.IsLicensed Boundedness.closed ∧
    LicensingPipeline.IsLicensed MereoTag.qua ∧
    LicensingPipeline.IsLicensed Telicity.telic ∧
    LicensingPipeline.IsLicensed VendlerClass.accomplishment ∧
    LicensingPipeline.IsLicensed NonemptyInterval.BoundaryType.closed ∧
    LicensingPipeline.IsLicensed SituationBoundedness.bounded ∧
    LicensingPipeline.IsLicensed EpistemicTag.finitelyAdditive :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- Every registered `LicensingPipeline` source maps its "open" variant to
    blocked. -/
theorem sources_agree_open :
    ¬ LicensingPipeline.IsLicensed Boundedness.open_ ∧
    ¬ LicensingPipeline.IsLicensed MereoTag.cum ∧
    ¬ LicensingPipeline.IsLicensed Telicity.atelic ∧
    ¬ LicensingPipeline.IsLicensed VendlerClass.state ∧
    ¬ LicensingPipeline.IsLicensed NonemptyInterval.BoundaryType.open_ ∧
    ¬ LicensingPipeline.IsLicensed SituationBoundedness.unbounded ∧
    ¬ LicensingPipeline.IsLicensed EpistemicTag.qualitative :=
  ⟨id, id, id, id, id, id, id⟩

/-! ### Rouillard's analytical apparatus -/

/-- Rouillard's TIA-type classification. Paper-specific apparatus;
    not on Fragment entries themselves. -/
inductive TIAType where
  | eTIA
  | gTIA
  deriving DecidableEq, Repr

/-- Rouillard's syntactic position for the *in*-adverbial.
    E-TIAs are VP-adjacent (event-level); G-TIAs are AspP-adjacent
    (perfect-level). [rouillard-2026] schemata (57) (§3.2) and (61) (§3.3). -/
inductive AdverbialPosition where
  | eventLevel
  | perfectLevel
  deriving DecidableEq, Repr

/-- Bundle of Rouillard's analytical labels for an *in*-adverbial. -/
structure RouillardClassification where
  tiaType : TIAType
  position : AdverbialPosition
  deriving DecidableEq, Repr

/-- Project a `DurationExprEntry` to Rouillard's analytical labels.
    Returns `none` for entries outside the *in*-adverbial paradigm
    (`forDur`, `ago`). -/
def rouillardClassification? (e : DurationExprEntry) :
    Option RouillardClassification :=
  match e.kind with
  | .telicCompletion => some ⟨.eTIA, .eventLevel⟩
  | .npiGap          => some ⟨.gTIA, .perfectLevel⟩
  | _                => none

/-! ### E-TIA empirical data -/

/-- E-TIA acceptability datum: VP class → acceptable with E-TIA?
    Acceptability is a decidable `Prop` field. -/
structure ETIADatum where
  /-- Description of the VP -/
  vp : String
  /-- Vendler class of the VP -/
  vendlerClass : VendlerClass
  /-- Whether "VP in three days" is acceptable -/
  acceptable : Prop
  [acceptableDecidable : Decidable acceptable]

attribute [instance] ETIADatum.acceptableDecidable

/-- (1a) "Mary wrote up a paper in three days." — accomplishment, ✓ -/
def datum_1a : ETIADatum :=
  { vp := "write up a paper", vendlerClass := .accomplishment, acceptable := True }

/-- (1b) "*Mary was sick in three days." — state, ✗ -/
def datum_1b : ETIADatum :=
  { vp := "be sick", vendlerClass := .state, acceptable := False }

/-- (88) "The climber reached the summit in three days." — achievement, ✓ -/
def datum_88 : ETIADatum :=
  { vp := "reach the summit", vendlerClass := .achievement, acceptable := True }

/-- (84) "*The dancers waltzed in one hour." — activity, ✗ -/
def datum_84 : ETIADatum :=
  { vp := "waltz", vendlerClass := .activity, acceptable := False }

def eTIAData : List ETIADatum :=
  [datum_1a, datum_1b, datum_88, datum_84]

/-- E-TIA acceptability matches the boundedness prediction:
    `LicensingPipeline.toBoundedness d.vendlerClass` is licensed iff
    the datum is acceptable. The pipeline routes through the
    Telicity → MereoTag → Boundedness chain (§ 11). -/
def eTIA_predicted (d : ETIADatum) : Prop :=
  (LicensingPipeline.toBoundedness d.vendlerClass).IsLicensed ↔ d.acceptable

instance (d : ETIADatum) : Decidable (eTIA_predicted d) := by
  unfold eTIA_predicted; infer_instance

theorem eTIA_all_predicted : ∀ d ∈ eTIAData, eTIA_predicted d := by decide

/-! ### G-TIA empirical data -/

/-- G-TIA acceptability datum: polarity × perfect → acceptable. -/
structure GTIADatum where
  /-- Description of the sentence -/
  sentence : String
  /-- Is the sentence negative? -/
  isNegative : Prop
  [isNegativeDecidable : Decidable isNegative]
  /-- Does the sentence contain a perfect? -/
  hasPerfect : Prop
  [hasPerfectDecidable : Decidable hasPerfect]
  /-- Whether the G-TIA is acceptable -/
  acceptable : Prop
  [acceptableDecidable : Decidable acceptable]

attribute [instance] GTIADatum.isNegativeDecidable GTIADatum.hasPerfectDecidable
                      GTIADatum.acceptableDecidable

/-- (2a) "Mary hasn't been sick in three days." — negative perfect, ✓ -/
def datum_2a : GTIADatum :=
  { sentence := "Mary hasn't been sick in three days"
    isNegative := True, hasPerfect := True, acceptable := True }

/-- (2b) "*Mary has been sick in three days." — positive perfect, ✗ -/
def datum_2b : GTIADatum :=
  { sentence := "Mary has been sick in three days"
    isNegative := False, hasPerfect := True, acceptable := False }

/-- (48) "*Mary wasn't sick in three days." — negative, no perfect, ✗ -/
def datum_48 : GTIADatum :=
  { sentence := "Mary wasn't sick in three days"
    isNegative := True, hasPerfect := False, acceptable := False }

def gTIAData : List GTIADatum := [datum_2a, datum_2b, datum_48]

/-- G-TIA acceptability matches the polarity ∧ perfect prediction.
    [rouillard-2026] Table 1: only NEG + PFV with G-TIA reading survives
    MIP filtering. Stated at the surface polarity-and-perfect level; the
    structural halves are `gTIAOpen_not_MIP_licensed` (positive blocked)
    and `gTIANeg_hasIsGreatest` (negative licensed at the gap length). -/
def gTIA_predicted (d : GTIADatum) : Prop :=
  (d.isNegative ∧ d.hasPerfect) ↔ d.acceptable

instance (d : GTIADatum) : Decidable (gTIA_predicted d) := by
  unfold gTIA_predicted; infer_instance

theorem gTIA_all_predicted : ∀ d ∈ gTIAData, gTIA_predicted d := by decide

/-! ### Table 1 (eq. 112): 8 cells with derived blocking -/

/-- [rouillard-2026] Table 1: readings for "*Mary has been sick in
    three days*" and its negation crossed with TIA type and aspect.

    Polarity, TIA type, and aspect are enums (not Bool flags), so the
    table reads structurally rather than as a tuple of opaque booleans. -/
inductive Table1Polarity | positive | negative
  deriving DecidableEq, Repr

inductive Table1Aspect | pfv | impv  -- E-perfect (PFV) vs U-perfect (IMPV)
  deriving DecidableEq, Repr

structure Table1Cell where
  polarity : Table1Polarity
  tiaType : TIAType
  aspect : Table1Aspect
  deriving DecidableEq, Repr

/-- A Table 1 cell survives MIP filtering iff it is the unique
    NEG + G-TIA + PFV configuration. Derived (not stipulated): every
    other cell is blocked by Rouillard's account, by various
    information-collapse mechanisms (positive cells: open-PTS density;
    E-TIA cells under negation: aspect mismatch with perfect; IMPV
    cells: U-perfect quantification mismatch). -/
def table1Survives (c : Table1Cell) : Prop :=
  c.polarity = .negative ∧ c.tiaType = .gTIA ∧ c.aspect = .pfv

instance (c : Table1Cell) : Decidable (table1Survives c) := by
  unfold table1Survives; infer_instance

/-- All 8 Table 1 cells, generated by enumerating the three discriminators. -/
def table1 : List Table1Cell := do
  let pol ← [Table1Polarity.positive, .negative]
  let ty ← [TIAType.eTIA, .gTIA]
  let asp ← [Table1Aspect.pfv, .impv]
  pure ⟨pol, ty, asp⟩

/-- [rouillard-2026] Table 1: exactly one cell survives — NEG + G-TIA + PFV. -/
theorem surviving_is_neg_gtia_pfv :
    table1.filter (fun c => decide (table1Survives c)) =
    [⟨.negative, .gTIA, .pfv⟩] := by decide

/-! ### Stacking constraint

[rouillard-2026] §3.2, ex. (60). When two TIAs stack, the inner
    (VP-adjacent) one must be E-TIA and the outer must be G-TIA. The
    reverse order is ungrammatical. The position constraint follows from
    `AdverbialPosition`: E-TIA = eventLevel (VP-adjacent), G-TIA =
    perfectLevel (AspP-adjacent). -/

/-- TIA stacking datum: inner and outer adverbial classifications. -/
structure StackingDatum where
  sentence : String
  innerType : TIAType
  innerPosition : AdverbialPosition
  outerType : TIAType
  outerPosition : AdverbialPosition
  acceptable : Prop
  [acceptableDecidable : Decidable acceptable]

attribute [instance] StackingDatum.acceptableDecidable

/-- (60a) "Mary hasn't written up a paper in three days in two weeks."
    Inner E-TIA + outer G-TIA: acceptable. -/
def stacking_60a : StackingDatum :=
  { sentence := "Mary hasn't written up a paper in three days in two weeks"
    innerType := .eTIA, innerPosition := .eventLevel
    outerType := .gTIA, outerPosition := .perfectLevel
    acceptable := True }

/-- (60b) "#Mary hasn't written up a paper in two weeks in three days."
    Reversed order: unacceptable. -/
def stacking_60b : StackingDatum :=
  { sentence := "#Mary hasn't written up a paper in two weeks in three days"
    innerType := .gTIA, innerPosition := .perfectLevel
    outerType := .eTIA, outerPosition := .eventLevel
    acceptable := False }

def stackingData : List StackingDatum := [stacking_60a, stacking_60b]

/-- Stacking is acceptable iff inner is event-level and outer is
    perfect-level. [rouillard-2026] schemata (57) (§3.2) and (61) (§3.3). -/
def stacking_predicted (d : StackingDatum) : Prop :=
  (d.innerPosition = .eventLevel ∧ d.outerPosition = .perfectLevel) ↔ d.acceptable

instance (d : StackingDatum) : Decidable (stacking_predicted d) := by
  unfold stacking_predicted; infer_instance

theorem stacking_all_predicted : ∀ d ∈ stackingData, stacking_predicted d := by
  decide

/-! ### Since-when questions

[rouillard-2026] §5.2, ex. (131): "Since when has Mary been sick?" lacks
the E-perfect/U-perfect ambiguity of the corresponding declarative.
Rouillard derives this via the MIP over the Hamblin sets: eq. (135) gives
the U-perfect ANS, while the E-perfect set (reformulated as eq. (137)) has
no maximally informative true answer (open-PTS density). The observation
is originally [von-fintel-iatridou-2019]'s; the density mechanism is
[fox-hackl-2006]'s. The datum below records the observation; the density
mechanism for the blocked E-perfect reading is `gTIAOpen_not_MIP_licensed`
(its Hamblin-set application is not formalized at this substrate level). -/

/-- Since-when question datum: which perfect readings are available?
    Observation-only (no prediction sentry): the Hamblin-set derivation
    is not formalized at this substrate level. -/
structure SinceWhenDatum where
  sentence : String
  uPerfect : Prop
  [uPerfectDecidable : Decidable uPerfect]
  ePerfect : Prop
  [ePerfectDecidable : Decidable ePerfect]

attribute [instance] SinceWhenDatum.uPerfectDecidable SinceWhenDatum.ePerfectDecidable

/-- (131) "Since when has Mary been sick?" — U-perfect only. -/
def sinceWhen_131 : SinceWhenDatum :=
  { sentence := "Since when has Mary been sick?"
    uPerfect := True
    ePerfect := False }

/-! ### Fragment bridges -/

/-- Fragment bridge: *since* is veridical and pins the PTS left
    boundary, matching the since-when question's presupposition. -/
theorem since_fragment_bridge :
    since_conn.complementVeridical = true ∧
    since_conn.order = TemporalOrder.since_ := ⟨rfl, rfl⟩

/-- The Rouillard projection assigns the expected analytical labels:
    E-TIA at event-level for telic-completion *in*; G-TIA at
    perfect-level for the NPI-gap *in*. -/
theorem rouillard_classification :
    rouillardClassification? inTelic = some ⟨.eTIA, .eventLevel⟩ ∧
    rouillardClassification? inGap   = some ⟨.gTIA, .perfectLevel⟩ :=
  ⟨rfl, rfl⟩

/-- Out-of-paradigm entries return `none`: *for* and *ago* are duration
    adverbials but not *in*-adverbials. -/
theorem rouillard_partial :
    rouillardClassification? forDur = none ∧
    rouillardClassification? ago    = none :=
  ⟨rfl, rfl⟩

end Rouillard2026
