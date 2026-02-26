import Linglib.Theories.Semantics.Events.Basic
import Linglib.Core.Temporal.Time

/-!
# Spatiotemporal Distance @cite{koev-2017}

Koev (2017, *Journal of Semantics* 34(1):1–38) argues that the Bulgarian
evidential introduces a **learning event** — the event through which the
speaker acquired the reported information — that must be **spatiotemporally
distant** (△) from the described event. The key predicate (Definition 24):

  △(e, e') iff τ(e) ∩ τ(e') = ∅ ∨ loc(e) ≠ loc(e')

Two events satisfy △ when either their temporal traces don't overlap
(standard indirect evidence: the speaker learned about the event after
it happened) or they occur at different locations (the smoke-from-chimney
scenario: the speaker perceives the event's effects from a distance,
at the same time but a different place).

## Architectural Note

Events (`Ev Time`) currently lack a location field. Rather than extending
the core event type (which would affect ~20 files), this module defines △
parameterized over an external location function `loc : Ev Time → L`.
The temporal component (`temporallyDisjoint`) is self-contained and
connects to Cumming's (2026) downstream evidence constraint (T ≤ A)
via `disjoint_earlier_implies_isBefore`.

## References

- Koev, T. (2017). Evidentiality, learning events, and spatiotemporal
  distance. *Journal of Semantics* 34(1):1–38.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
-/

namespace Semantics.Events.SpatiotemporalDistance

open Core.Time
open Semantics.Events

-- ════════════════════════════════════════════════════
-- § 1. Temporal Disjointness
-- ════════════════════════════════════════════════════

/-- Two events are temporally disjoint when their temporal traces do not
    overlap (Koev 2017, first disjunct of Definition 24). This rules out
    direct perception: if the speaker was present for the event, the
    evidential is infelicitous. -/
def temporallyDisjoint {Time : Type*} [LinearOrder Time]
    (e₁ e₂ : Ev Time) : Prop :=
  ¬ (e₁.τ.overlaps e₂.τ)

-- ════════════════════════════════════════════════════
-- § 2. Spatiotemporal Distance △
-- ════════════════════════════════════════════════════

/-- Spatiotemporal distance △ (Koev 2017, Definition 24).
    Two events are spatiotemporally distant if either their temporal traces
    don't overlap or they occur at different locations. Parameterized over
    a location function `loc : Ev Time → L` since `Ev` lacks a built-in
    location field. -/
def spatiotemporallyDistant {Time : Type*} [LinearOrder Time]
    {L : Type*} [DecidableEq L]
    (loc : Ev Time → L) (e₁ e₂ : Ev Time) : Prop :=
  temporallyDisjoint e₁ e₂ ∨ loc e₁ ≠ loc e₂

-- ════════════════════════════════════════════════════
-- § 3. Connection Theorems
-- ════════════════════════════════════════════════════

/-- If e₁ temporally precedes e₂ (no overlap, e₁ strictly before e₂),
    then they are temporally disjoint. This is the standard indirect
    evidence case: the described event finished before the learning event
    started. -/
theorem temporallyDisjoint_of_precedes {Time : Type*} [LinearOrder Time]
    (e₁ e₂ : Ev Time)
    (h : e₁.τ.precedes e₂.τ) : temporallyDisjoint e₁ e₂ := by
  unfold temporallyDisjoint Interval.overlaps Interval.precedes at *
  simp only [Ev.τ] at *
  exact fun ⟨_, h2⟩ => absurd h2 (not_le.mpr h)

/-- If two events are temporally disjoint and the first starts no later
    than the second, then the first is temporally before the second:
    e₁.τ.finish ≤ e₂.τ.start. This bridges Koev's event-based △ to
    Cumming's point-based T ≤ A constraint. -/
theorem disjoint_earlier_implies_isBefore {Time : Type*} [LinearOrder Time]
    (e₁ e₂ : Ev Time)
    (hd : temporallyDisjoint e₁ e₂)
    (hearlier : e₁.τ.start ≤ e₂.τ.start) : e₁.τ.isBefore e₂.τ := by
  unfold temporallyDisjoint Interval.overlaps at hd
  unfold Interval.isBefore
  simp only [Ev.τ] at *
  by_contra h
  push_neg at h
  exact hd ⟨le_trans hearlier e₂.runtime.valid, le_of_lt h⟩

/-- If two events' temporal traces overlap, they are not temporally
    disjoint. Direct perception (overlapping runtimes) is incompatible
    with temporal distance. -/
theorem overlapping_not_disjoint {Time : Type*} [LinearOrder Time]
    (e₁ e₂ : Ev Time)
    (h : e₁.τ.overlaps e₂.τ) : ¬ temporallyDisjoint e₁ e₂ :=
  fun hd => hd h

/-- Spatial distance alone suffices for △, regardless of temporal
    overlap (Koev 2017, ex. 25b: smoke from chimney). -/
theorem spatiotemporallyDistant_of_different_location
    {Time : Type*} [LinearOrder Time] {L : Type*} [DecidableEq L]
    (loc : Ev Time → L) (e₁ e₂ : Ev Time)
    (h : loc e₁ ≠ loc e₂) : spatiotemporallyDistant loc e₁ e₂ :=
  Or.inr h

/-- Temporal disjointness alone suffices for △. -/
theorem spatiotemporallyDistant_of_temporallyDisjoint
    {Time : Type*} [LinearOrder Time] {L : Type*} [DecidableEq L]
    (loc : Ev Time → L) (e₁ e₂ : Ev Time)
    (h : temporallyDisjoint e₁ e₂) : spatiotemporallyDistant loc e₁ e₂ :=
  Or.inl h

end Semantics.Events.SpatiotemporalDistance
