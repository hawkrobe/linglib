import Linglib.Core.Order.Boundedness
import Linglib.Core.Order.Comparison
import Linglib.Core.Order.ComparativeScale

/-!
# States-Based Gradable Adjective Semantics

[cariani-santorio-wellwood-2024] [wellwood-2015] [kennedy-2007]

An alternative to Kennedy-style degree semantics (`Theory.lean`). Gradable
adjectives denote properties of states (type `⟨v,t⟩`), not measure functions.
The positive form works via a **background ordering** on states and a
**contrast point** that carves out the positive region — no covert `pos`
morpheme is needed.

## Key Idea

Each gradable predicate sits on an ordered domain of states (the background
ordering). The predicate's **contrast point** divides the ordering into a
positive region (states at or above the contrast point) and the rest.
Different predicates on the same ordering have different contrast points:
`warm` and `hot` share a temperature ordering but `hot` has a higher
contrast point.

Comparative morphology (`more`) introduces a measure function on states,
accessing the background ordering but discarding the contrast point. This
explains why "A is more confident that p than that q" has the same truth
conditions whether we use `confident` or `certain` — both share the
confidence ordering (CSW observation (72)).

## Architecture

`StatesBasedEntry` extends `ComparativeScale` (from `Degree`) with a
contrast point. The background ordering is the ambient `[Preorder S]`.
This is a competing theory to the standard threshold model in `Theory.lean`; the
bridge theorem `statesBased_iff_kennedy` shows when they agree.

-/

namespace Degree

open Core.Order (ComparativeScale Boundedness)
/-! ### States-Based Entry -/

/-- A states-based gradable predicate entry.

    Each entry names a positive region on a background ordering of states.
    The `contrastPoint` determines the lower bound of the positive region:
    a state `s` is in the positive region iff `contrastPoint ≤ s`.

    The background ordering comes from the ambient `[Preorder S]`.
    `scale` provides the boundedness classification (open, closed, etc.).

    Example: `tall` and `short` share a `ComparativeScale HeightState` but
    have different contrast points. `confident` and `certain` share a
    confidence ordering but `certain` has a higher contrast point. -/
structure StatesBasedEntry (S : Type*) [Preorder S] where
  /-- Boundedness classification of the background ordering -/
  scale : ComparativeScale S
  /-- The threshold state delimiting the positive region -/
  contrastPoint : S

variable {S : Type*} [Preorder S]

/-- A state is in the positive region iff it is at least as high as the
    contrast point in the background ordering (CSW eq. 28b).

    This is the states-based counterpart to Kennedy's `positiveMeaning`:
    instead of `d > θ` (degree exceeds threshold), we have `c ≤ s`
    (state is at or above the contrast point in the preorder). -/
def StatesBasedEntry.inPositiveRegion (entry : StatesBasedEntry S) (s : S) : Prop :=
  s ∈ Core.Order.Comparison.ge.over id entry.contrastPoint

/-- A state is in the *lower* region iff it is at or below the contrast
    point. The dual of `inPositiveRegion`, used for negative-polarity
    adjectives like `short`, `cool`, `doubts` (CSW §5.2 (63c)).

    The same `StatesBasedEntry` shape hosts either region; whether a
    lexical entry is positive- or negative-polarity is determined by
    which membership predicate consumers invoke. Mathlib analogue:
    `Mathlib.Order.UpperLower` provides `UpperSet` and `LowerSet` as
    separate types over the same preorder. -/
def StatesBasedEntry.inLowerRegion (entry : StatesBasedEntry S) (s : S) : Prop :=
  s ∈ Core.Order.Comparison.le.over id entry.contrastPoint

/-- Two entries with strictly-ordered contrast points carve out
    disjoint upper/lower regions. If `e_pos.contrastPoint > e_low.contrastPoint`
    (encoded as `¬ e_pos.contrastPoint ≤ e_low.contrastPoint`), no state
    is simultaneously above `e_pos`'s point and below `e_low`'s.

    This is the substrate witness for negative-polarity-vs-positive-
    polarity exclusion (e.g., CSW (63a)/(63c): no holder simultaneously
    `confident(p)` and `doubts(p)`). -/
theorem disjoint_regions {S : Type*} [Preorder S]
    (e_pos e_low : StatesBasedEntry S)
    (h_strict : ¬ e_pos.contrastPoint ≤ e_low.contrastPoint)
    (s : S) :
    ¬ (e_pos.inPositiveRegion s ∧ e_low.inLowerRegion s) := by
  intro ⟨h_pos, h_low⟩
  exact h_strict (le_trans h_pos h_low)

/-! ### Scale-Mate Relationship -/

/-- Two entries are scale-mates iff they share a background ordering
    (same `scale`) but differ in their contrast points. Scale-mates
    form clusters like `warm/hot`, `confident/certain`, `cool/cold`.
    (CSW §3.3: different cut-off points for different adjectives.) -/
def areScaleMates (e₁ e₂ : StatesBasedEntry S) : Prop :=
  e₁.scale = e₂.scale ∧ e₁.contrastPoint ≠ e₂.contrastPoint

/-- `e₁` asymmetrically entails `e₂` when `e₁`'s contrast point is at
    least as high as `e₂`'s. Every state in `e₁`'s positive region is
    also in `e₂`'s, but not vice versa.

    Example: `certain` asymmetrically entails `confident` because
    certainty requires a higher level of confidence (CSW §5.2). -/
def asymEntails (e₁ e₂ : StatesBasedEntry S) : Prop :=
  e₂.contrastPoint ≤ e₁.contrastPoint

/-- Asymmetric entailment implies positive-region inclusion: if
    `e₁` asymmetrically entails `e₂`, then every state in `e₁`'s
    positive region is also in `e₂`'s positive region.

    CSW (65): "Ann is certain that p" entails "Ann is confident that p". -/
theorem asymEntails_positive_region (e₁ e₂ : StatesBasedEntry S)
    (h : asymEntails e₁ e₂) (s : S) :
    e₁.inPositiveRegion s → e₂.inPositiveRegion s := by
  intro h_pos
  exact le_trans h h_pos

-- Comparative morphology on states is shared substrate: measure
-- admissibility (CSW (21)/(31)) is `Degree.admissibleMeasure`
-- (`Measure.lean`); the direct comparative (CSW (32)) is
-- `Degree.comparativeSem μ · · .positive`; the faithful max-quantified
-- comparative (CSW (46)/(47)) is `Degree.maxComparative`, with CSW fn
-- 25's unique-state collapse at `Degree.maxComparative_eq_iff`.
-- Confidence reports instantiate these in `Semantics/Attitudes/Confidence.lean`.

/-! ### Morphisms

The transport out of the states-based representation:
`statesBased_iff_kennedy` (CSW ↔ Kennedy threshold, along a `StrictMono`
degree assignment). Cross-framework maps between measurement, threshold
degrees, and delineation live in `Degree/Hom.lean`. -/

/-- When a monotone measure maps the contrast point to a Kennedy threshold,
    the states-based positive form agrees with degree-based comparison.

    CSW's framework and Kennedy's are equivalent over linearly ordered
    scales with measure functions: `contrastPoint ≤ s ↔ θ ≤ μ(s)`.

    Note: CSW use weak inequality `≿` for the positive form. The existing
    `positiveMeaning` in `Theory.lean` uses strict `<`. This theorem uses
    weak `≤` on both sides, matching CSW. -/
theorem statesBased_iff_kennedy
    {S : Type*} [LinearOrder S] {D : Type*} [LinearOrder D]
    (μ : S → D) (hMono : StrictMono μ) (contrastPt : S) (θ : D)
    (hBridge : μ contrastPt = θ) (s : S) :
    contrastPt ≤ s ↔ θ ≤ μ s := by
  constructor
  · intro h
    rw [← hBridge]
    exact hMono.monotone h
  · intro h
    by_contra h_not
    have h_lt : s < contrastPt := lt_of_not_ge h_not
    have := hMono h_lt
    rw [hBridge] at this
    exact absurd h (not_le.mpr this)

end Degree
