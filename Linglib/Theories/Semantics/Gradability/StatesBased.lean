import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Gradability.Theory

/-!
# States-Based Gradable Adjective Semantics

@cite{cariani-santorio-wellwood-2024} @cite{wellwood-2015} @cite{kennedy-2007}

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

`StatesBasedEntry` extends `ComparativeScale` (from `Core.Scale`) with a
contrast point. The background ordering is the ambient `[Preorder S]`.
This is a competing theory to the standard threshold model in `Theory.lean`; the
bridge theorem `statesBased_iff_kennedy` shows when they agree.

-/

namespace Semantics.Gradability.StatesBased

open Core.Scale (ComparativeScale Boundedness)

-- ════════════════════════════════════════════════════
-- § 1. States-Based Entry
-- ════════════════════════════════════════════════════

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
  entry.contrastPoint ≤ s

-- ════════════════════════════════════════════════════
-- § 2. Scale-Mate Relationship
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 3. Comparative Morphology on States
-- ════════════════════════════════════════════════════

/-- CSW's monotonicity constraint (eq. 21): a measure function `μ` is
    admissible for a background ordering iff it preserves strict order.

    If `s₁ ≺ s₂` in the background ordering, then `μ(s₁) < μ(s₂)`.
    This is Mathlib's `StrictMono`. -/
abbrev admissibleMeasure {D : Type*} [Preorder D] (μ : S → D) : Prop :=
  StrictMono μ

/-- Comparative semantics on states (CSW (32)): "A is more G than B"
    iff the measure of A's state exceeds the measure of B's state.

    The key CSW insight (§3.4): the comparative uses only the background
    ordering (via an admissible measure), not the contrast point. This is
    captured architecturally by the type signature — `statesComparativeSem`
    takes no `StatesBasedEntry` parameter, so the contrast point that
    distinguishes scale-mates (`confident`/`certain`, `warm`/`hot`) is
    invisible to the comparative. Scale-mate comparative equivalence
    (CSW (72)) holds by construction. -/
def statesComparativeSem {D : Type*} [Preorder D]
    (μ : S → D) (s_a s_b : S) : Prop :=
  μ s_b < μ s_a

-- ════════════════════════════════════════════════════
-- § 4. Bridge: States-Based ↔ Kennedy
-- ════════════════════════════════════════════════════

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

end Semantics.Gradability.StatesBased
