import Mathlib.Order.Bounds.Image
import Linglib.Semantics.Degree.Predicate
import Linglib.Semantics.Degree.Defs
import Linglib.Semantics.Degree.DirectedMeasure

/-!
# Cross-world extremum under entailment
[fox-2007] [fox-hackl-2006] [beck-rullmann-1999]
[von-fintel-fox-iatridou-2014] [rouillard-2026]

The cross-world entailment-based "maximally informative" predicate (`IsMaxInf`)
that has no mathlib analogue, plus mathlib bridges for the per-world
specialization, plus the `MIP_Licensed` licensing predicate combining
non-constancy with per-world extremum existence.

## Two formulations

The mathlib-shape per-world reading is just `IsLeast {y | P y w} x`
(or `IsGreatest`) — call mathlib directly. The Fox 2007-style cross-world
reading is unique to formal semantics:

  IsMaxInf P x w := P x w ∧ ∀ y, P y w → ∀ w', P x w' → P y w'

reading: at world w, x is true; and for any other true alternative y at w,
the proposition denoted by x entails the proposition denoted by y across
every world. Equivalently: x denotes the smallest proposition (in subset
order on `Set W`) among true alternatives at w. Bridge to per-world via
mathlib's `MonotoneOn.map_isLeast` family.

Two predicates fail under different conditions, so the MIP licensing
condition is their conjunction:

- `AdmitsOptimum P` (non-constancy in α; the *atelic / homogeneous* failure):
  fails when every alternative denotes the same proposition — no informative
  distinction among alternatives.
- `IsLeast {y | P y w} x` (existence of a smallest-true alternative; the
  *no-extremum* failure under density): fails when the true set is upward-closed
  with no minimum (e.g., `Set.Ioi a` in a dense linear order).

## Naming

The shared mathematical structure — extracting the extremal element of an
indexed family under an evaluation map — also appears outside semantics
(notably as `argmax_u (ln P_L0(s | u))` in RSA-style pragmatics; both pick
the most informative alternative under their respective evaluation map).
The file lives in `Semantics/Entailment/` because the cross-world
quantifier is the entailment relation between propositions.

## Beck-Rullmann attribution

[beck-rullmann-1999] introduce `answer1(w)(Q) = ⋂{p : Q(w)(p) ∧ p(w)}` —
the conjunction of all true Hamblin propositions at `w`. For upward-monotone
scalar predicates this reduces to the smallest-true-degree case captured by
`IsLeast`. For non-scalar predicates (their §4.4) it is the literal
conjunction and not an extremum. So the `IsLeast` per-world reading is
an *ergonomic specialization* of Beck-Rullmann answerhood under monotonicity,
not their primary formulation.
-/

namespace Entailment

open Degree
open Core.Order (Comparison)
variable {α : Type*} [LinearOrder α]

-- ════════════════════════════════════════════════════
-- § 1. Cross-world entailment-based maximal informativity
-- ════════════════════════════════════════════════════

/-- A scale value `x` is **maximally informative** in a degree property `P`
    at world `w` iff `P x w` is true and `P x` entails `P y` (across every
    world) for every other true `P y w`.

    The unified exhaustivity condition underlying *only*-implicatures, degree
    questions, and definite descriptions in the [fox-2007] /
    [von-fintel-fox-iatridou-2014] tradition. [rouillard-2026]
    specializes this to numerals in temporal *in*-adverbials. -/
def IsMaxInf {W : Type*} (P : α → W → Prop) (x : α) (w : W) : Prop :=
  P x w ∧ ∀ y, P y w → (∀ w', P x w' → P y w')

/-- A degree property has a maximally informative element at world `w`. -/
def HasMaxInf {W : Type*} (P : α → W → Prop) (w : W) : Prop :=
  ∃ x, IsMaxInf P x w

/-- Information collapse: no element is maximally informative at any world.
    [fox-hackl-2006]: this is why degree questions fail over dense
    complements, why *only* + "more than n" is contradictory, and why
    definite descriptions over dense open sets lack a presupposition-satisfying
    referent. -/
def InformationCollapse {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ w, ¬ HasMaxInf P w

-- ════════════════════════════════════════════════════
-- § 2. Bridges from mathlib per-world IsLeast/IsGreatest
-- ════════════════════════════════════════════════════

/-- For an upward-monotone family, a per-world smallest-true value is
    cross-world maximally informative. The converse requires
    threshold-witness assumptions on the world space (one direction only). -/
theorem isMaxInf_of_isLeast_upward {W : Type*}
    {P : α → W → Prop} (hUp : IsUpwardMonotone P) (w : W) (x : α)
    (h : IsLeast {y | P y w} x) : IsMaxInf P x w := by
  refine ⟨h.1, fun y hy w' hx_w' => ?_⟩
  exact hUp x y (h.2 hy) w' hx_w'

/-- Dually for downward-monotone families: the per-world largest-true value
    is cross-world maximally informative. -/
theorem isMaxInf_of_isGreatest_downward {W : Type*}
    {P : α → W → Prop} (hDown : IsDownwardMonotone P) (w : W) (x : α)
    (h : IsGreatest {y | P y w} x) : IsMaxInf P x w := by
  refine ⟨h.1, fun y hy w' hx_w' => ?_⟩
  exact hDown y x (h.2 hy) w' hx_w'

-- ════════════════════════════════════════════════════
-- § 3. MIP licensing
-- ════════════════════════════════════════════════════

/-- **Maximal Informativity Principle licensing** for upward-monotone
    derived properties (e.g., E-TIA telic in [rouillard-2026]). The
    conjunction captures both failure modes:
    - `AdmitsOptimum P` (non-constancy): the family distinguishes alternatives
      at all (failure mode for atelic / homogeneous predicates).
    - `IsLeast {y | P y w} x` at some `w`: a smallest true value exists
      (failure mode under density without minimum). -/
def MIP_Licensed {W : Type*} (P : α → W → Prop) : Prop :=
  AdmitsOptimum P ∧ ∃ w x, IsLeast {y | P y w} x

/-- Dual MIP licensing for downward-monotone derived properties (e.g., G-TIA
    in negative perfects). -/
def MIP_LicensedDown {W : Type*} (P : α → W → Prop) : Prop :=
  AdmitsOptimum P ∧ ∃ w x, IsGreatest {y | P y w} x

-- ════════════════════════════════════════════════════
-- § 4. Degree-predicate IsMaxInf characterizations
-- ════════════════════════════════════════════════════

/-! Applications of `IsMaxInf` to the canonical degree predicates
    `Comparison.{ge,gt,le}.over` (defined in `Core/Order/Comparison.lean`,
    monotonicity in `Semantics/Degree/Predicate.lean`). The IsMaxInf-flavored
    consequences live here as a downstream entailment-theoretic application. -/

/-- "At least d" always has a maximally informative element: d₀ = μ(w).

    This holds on ANY scale — dense or discrete — because the actual
    value μ(w) is always in the domain and "at least μ(w)" entails
    "at least d" for all d ≤ μ(w) by transitivity.

    This is why bare numerals generate scalar implicatures regardless
    of scale density: the `≥` relation creates a closed set with a
    natural maximum at the true value. -/
theorem atLeast_hasMaxInf {W : Type*} (μ : W → α) (w : W) :
    HasMaxInf (Comparison.ge.over μ) w :=
  ⟨μ w, le_refl _, fun _ hd _ hw' => le_trans hd hw'⟩

/-- **Implicature asymmetry** ([fox-2007], [fox-hackl-2006]):
    on a dense scale, "more than n" has NO maximally informative element.

    For any candidate d₀ < μ(w), density gives d' ∈ (d₀, μ(w)).
    A witness world w₁ with μ(w₁) ∈ (d₀, d') has "more than d₀"
    true but "more than d'" false — so d₀ does not entail d'.

    The `hSurj` hypothesis says every degree value is realized by some
    possible world. -/
theorem moreThan_noMaxInf {W : Type*} [DenselyOrdered α] (μ : W → α)
    (hSurj : Function.Surjective μ) (w : W) :
    ¬ HasMaxInf (Comparison.gt.over μ) w := by
  intro ⟨d₀, hd₀, hent⟩
  obtain ⟨d', hd₀d', hd'w⟩ := DenselyOrdered.dense d₀ (μ w) hd₀
  obtain ⟨m, hd₀m, hmd'⟩ := DenselyOrdered.dense d₀ d' hd₀d'
  obtain ⟨w₁, rfl⟩ := hSurj m
  exact absurd (hent d' hd'w w₁ hd₀m) (not_lt.mpr (le_of_lt hmd'))

/-- **Kennedy / [fox-hackl-2006] bridge (point-realization form)**:
    `IsMaxInf` of the "at least" degree property at value m and world w holds
    iff `μ w = m`, given only that `m` itself is in the image of `μ`. This is
    strictly weaker than full `Function.Surjective μ` and is the hypothesis
    actually used in the proof. -/
theorem isMaxInf_atLeast_of_hit {W : Type*} (μ : W → α) (m : α) (w : W)
    (hHit : ∃ w', μ w' = m) :
    IsMaxInf (Comparison.ge.over μ) m w ↔ μ w = m := by
  constructor
  · intro ⟨hge, hent⟩
    obtain ⟨w_m, hw_m⟩ := hHit
    have h : μ w_m ≥ μ w := hent (μ w) (le_refl _) w_m (le_of_eq hw_m.symm)
    have : μ w ≤ m := by rw [← hw_m]; exact h
    exact (le_antisymm hge this).symm
  · rintro rfl
    exact ⟨le_refl _, fun _ hd _ hn' => le_trans hd hn'⟩

/-- **Kennedy / [fox-hackl-2006] bridge**: `IsMaxInf` of the "at least"
    degree property at value m and world w holds iff the measure at w
    equals m, under full surjectivity. Corollary of `isMaxInf_atLeast_of_hit`. -/
theorem isMaxInf_atLeast_iff_eq {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (Comparison.ge.over μ) m w ↔ μ w = m :=
  isMaxInf_atLeast_of_hit μ m w (hSurj m)

/-- On ℕ, "more than m" has `HasMaxInf`: the discrete collapse rescues maximality.
    Contrast with `moreThan_noMaxInf`: on dense scales, `HasMaxInf` fails. -/
theorem moreThan_nat_hasMaxInf {W : Type*} (μ : W → ℕ) (w : W)
    (hw : w ∈ Comparison.gt.over μ 0) : HasMaxInf (Comparison.gt.over μ) w := by
  refine ⟨μ w - 1, ?_, fun d hd w' hw' => ?_⟩
  · have : μ w > 0 := hw; show μ w > μ w - 1; omega
  · have : μ w' > μ w - 1 := hw'; have : μ w > d := hd; show μ w' > d; omega

/-- "At most d" always has a maximally informative element: d₀ = μ(w).
    Symmetric to `atLeast_hasMaxInf`. -/
theorem atMost_hasMaxInf {W : Type*} (μ : W → α) (w : W) :
    HasMaxInf (Comparison.le.over μ) w :=
  ⟨μ w, le_refl _, fun _ hd _ hw' => le_trans hw' hd⟩

/-- **Kennedy / [rouillard-2026] bridge**: `IsMaxInf` of "at most d" at
    value m and world w holds iff the measure at w equals m. Symmetric to
    `isMaxInf_atLeast_iff_eq`: the MIP derives exact meaning from "at most"
    just as it does from "at least". -/
theorem isMaxInf_atMost_iff_eq {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (Comparison.le.over μ) m w ↔ μ w = m := by
  constructor
  · intro ⟨hle, hent⟩
    obtain ⟨w_m, hw_m⟩ := hSurj m
    have h : μ w_m ≤ μ w := hent (μ w) (le_refl _) w_m (le_of_eq hw_m)
    have : m ≤ μ w := hw_m ▸ h
    exact le_antisymm hle this
  · rintro rfl
    exact ⟨le_refl _, fun _ hd _ hw' => le_trans hw' hd⟩

-- ════════════════════════════════════════════════════
-- § 5. MIP = Kennedy's Type-Shift
-- ════════════════════════════════════════════════════

/-! Kennedy's de-Fregean type-shift is the MIP applied to a monotone degree
    property: for both "at least" (Kennedy direction) and "at most"
    ([rouillard-2026] direction), max⊨ at world w = μ(w), the true
    value. So the MIP universally derives exact meaning from monotone
    degree properties, regardless of monotonicity direction. -/

/-- MIP derives exact meaning from "at least" (Kennedy's direction). -/
theorem mip_atLeast_is_exact {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (Comparison.ge.over μ) m w ↔ w ∈ Comparison.eq.over μ m := by
  rw [isMaxInf_atLeast_iff_eq μ m w hSurj, Comparison.mem_over, Comparison.rel]

/-- MIP derives exact meaning from "at most" (Rouillard's direction). -/
theorem mip_atMost_is_exact {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (Comparison.le.over μ) m w ↔ w ∈ Comparison.eq.over μ m := by
  rw [isMaxInf_atMost_iff_eq μ m w hSurj, Comparison.mem_over, Comparison.rel]

/-- The MIP is direction-invariant: "at least" and "at most" yield the
    same exact meaning under maximal informativity. Kennedy's type-shift
    and Rouillard's MIP are literally the same operation. -/
theorem mip_direction_invariant {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (Comparison.ge.over μ) m w ↔ IsMaxInf (Comparison.le.over μ) m w := by
  rw [mip_atLeast_is_exact μ m w hSurj, mip_atMost_is_exact μ m w hSurj]

/-! ### The bundled form: `DirectedMeasure.degreeProperty`

`DirectedMeasure.degreeProperty` derives "at least" or "at most" from the
stored `direction`; under maximal informativity either direction yields
exact meaning at the true measure value. This ties the algebraic
constructor layer (`numeral`, `adjective`, epistemic thresholds) to the
entailment-theoretic MIP layer. -/

/-- The maximally informative degree of a directed measure's derived
    property is the true measure value, whichever the direction. -/
theorem _root_.Degree.DirectedMeasure.isMaxInf_degreeProperty_iff
    {W : Type*} (dm : DirectedMeasure α W) (m : α) (w : W)
    (hSurj : Function.Surjective dm.μ) :
    IsMaxInf dm.degreeProperty m w ↔ dm.μ w = m := by
  cases h : dm.direction with
  | positive =>
      simp only [DirectedMeasure.degreeProperty, h]
      exact isMaxInf_atLeast_iff_eq dm.μ m w hSurj
  | negative =>
      simp only [DirectedMeasure.degreeProperty, h]
      exact isMaxInf_atMost_iff_eq dm.μ m w hSurj

/-- Direction-invariance, bundled: two directed measures sharing a measure
    function agree on maximal informativity regardless of direction or
    boundedness — the constructor-level form of `mip_direction_invariant`. -/
theorem _root_.Degree.DirectedMeasure.isMaxInf_degreeProperty_congr
    {W : Type*} (dm₁ dm₂ : DirectedMeasure α W) (hμ : dm₁.μ = dm₂.μ)
    (m : α) (w : W) (hSurj : Function.Surjective dm₁.μ) :
    IsMaxInf dm₁.degreeProperty m w ↔ IsMaxInf dm₂.degreeProperty m w := by
  rw [dm₁.isMaxInf_degreeProperty_iff m w hSurj,
      dm₂.isMaxInf_degreeProperty_iff m w (hμ ▸ hSurj), hμ]

end Entailment
