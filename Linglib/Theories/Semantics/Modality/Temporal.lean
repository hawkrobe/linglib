import Linglib.Theories.Semantics.Modality.Kratzer.Operators

/-!
# Temporal Modal Evaluation
@cite{abusch-1997} @cite{condoravdi-2002} @cite{kratzer-2012} @cite{werner-2006}

Modal bases and ordering sources are functions of both world and time
(@cite{kratzer-2012} Ch. 4, @cite{condoravdi-2002}). This module extends `Kratzer.lean`
with time-indexed conversational backgrounds and derives the static
(time-independent) versions as a special case.

## Core Extension

Kratzer.lean defines `ConvBackground W := W → List (W → Bool)`.
@cite{kratzer-2012} Ch. 4 argues that this should be `W → Time → List (W → Bool)`:
the modal base and ordering source can vary with the temporal perspective.

This distinction matters for:
- **Temporal orientation**: whether "must p" is about the past, present, or
  future depends on when the modal base is evaluated.
- **Historical accessibility**: worlds that share history up to time t may
  diverge afterward ("branching futures").
- **Epistemic change**: the speaker's evidence base changes over time;
  "at t, it was necessary that p" ≠ "at t', it is necessary that p".

## Key Result

`temporal_eq_static`: temporal modal evaluation reduces to standard Kratzer
evaluation when the conversational backgrounds are time-independent.

-/

namespace Semantics.Modality.Temporal

open Semantics.Modality.Kratzer

variable {W : Type*} [DecidableEq W] [Fintype W]

/-! ## Time-indexed conversational backgrounds -/

/-- A time-indexed conversational background maps (world, time) pairs to
    sets of propositions. This is the book's core extension: f(w,t) and g(w,t).

    At different times, the same world may yield different sets of relevant
    facts (modal base) or normative standards (ordering source). -/
abbrev TemporalConvBackground (W : Type*) (Time : Type*) := W → Time → List (W → Bool)

/-- Time-indexed modal base: what facts are relevant at (w, t). -/
abbrev TemporalModalBase (W : Type*) (Time : Type*) := TemporalConvBackground W Time

/-- Time-indexed ordering source: what standards apply at (w, t). -/
abbrev TemporalOrderingSource (W : Type*) (Time : Type*) := TemporalConvBackground W Time

/-- Fix a time t to obtain a standard (time-independent) conversational
    background. This is the "temporal perspective" operation: evaluating
    the modal at a specific time. -/
def TemporalConvBackground.atTime {Time : Type*}
    (f : TemporalConvBackground W Time) (t : Time) : ConvBackground W :=
  λ w => f w t

/-- Lift a time-independent background to a trivially temporal one
    (constant across time). -/
def ConvBackground.liftTemporal {Time : Type*}
    (f : ConvBackground W) : TemporalConvBackground W Time :=
  λ w _ => f w

omit [DecidableEq W] [Fintype W] in
/-- Lifting then fixing at any time recovers the original background. -/
theorem lift_atTime_id {Time : Type*} (f : ConvBackground W) (t : Time) :
    (ConvBackground.liftTemporal f).atTime t = f := rfl

/-! ## Temporal modal evaluation -/

/-- Modal necessity evaluated at a world-time pair.

    ⟦must p⟧(w, t) = ∀w' ∈ Best(f(w,t), g(w,t), w). p(w') -/
def temporalNecessity {Time : Type*}
    (f : TemporalModalBase W Time) (g : TemporalOrderingSource W Time)
    (t : Time) (p : W → Bool) (w : W) : Prop :=
  necessity (f.atTime t) (g.atTime t) p w

/-- Modal possibility evaluated at a world-time pair.

    ⟦might p⟧(w, t) = ∃w' ∈ Best(f(w,t), g(w,t), w). p(w') -/
def temporalPossibility {Time : Type*}
    (f : TemporalModalBase W Time) (g : TemporalOrderingSource W Time)
    (t : Time) (p : W → Bool) (w : W) : Prop :=
  possibility (f.atTime t) (g.atTime t) p w

/-- **Temporal ↔ Static bridge**: temporal modal evaluation reduces to
    standard Kratzer when the backgrounds are time-independent. -/
theorem temporal_eq_static {Time : Type*}
    (f : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) (t : Time) :
    temporalNecessity (ConvBackground.liftTemporal f)
      (ConvBackground.liftTemporal g) t p w ↔
    necessity f g p w :=
  Iff.rfl

/-- Temporal duality: □ₜp ↔ ¬◇ₜ¬p. -/
theorem temporal_duality {Time : Type*}
    (f : TemporalModalBase W Time) (g : TemporalOrderingSource W Time)
    (t : Time) (p : W → Bool) (w : W) :
    temporalNecessity f g t p w ↔
    ¬ temporalPossibility f g t (λ w' => !p w') w :=
  duality (f.atTime t) (g.atTime t) p w

/-! ## Historical accessibility

Worlds share history up to time t: they agree on all facts prior to t.
This gives the "branching futures" model: the past is settled, the future
is open. -/

/-- Historical necessity: p holds at all worlds sharing w's history up to t.

    The history function (a `TemporalConvBackground`) serves as the modal base;
    the ordering source is empty (pure accessibility, no ranking). -/
def historicalNecessity {Time : Type*}
    (history : TemporalConvBackground W Time)
    (t : Time) (p : W → Bool) (w : W) : Prop :=
  temporalNecessity history
    (λ _ _ => ([] : List (W → Bool))) t p w

/-- With empty history (no shared past), all worlds are accessible:
    historical necessity collapses to necessity over `Finset.univ`. -/
theorem empty_history_universal {Time : Type*}
    (t : Time) (p : W → Bool) (w : W) :
    historicalNecessity (λ (_ : W) (_ : Time) => ([] : List (W → Bool)))
      t p w ↔ ∀ w' : W, p w' = true := by
  show necessity emptyBackground emptyBackground p w ↔ _
  rw [necessity_iff_all, empty_ordering_emptyBackground, empty_base_universal_access]
  simp [Finset.mem_univ]

/-! ## Epistemic change over time -/

/-- Evidence monotonicity: if the evidence at t₁ is a subset of the
    evidence at t₂ (more evidence was gathered), then what was necessary
    at t₁ (less evidence) is still necessary at t₂ (more evidence).

    More evidence → fewer accessible worlds → at least as many necessities. -/
theorem evidence_monotone {Time : Type*}
    (f : TemporalModalBase W Time) (t₁ t₂ : Time)
    (p : W → Bool) (w : W)
    (hSub : ∀ q, q ∈ f w t₁ → q ∈ f w t₂)
    (hNec : temporalNecessity f (λ _ _ => ([] : List (W → Bool))) t₁ p w) :
    temporalNecessity f (λ _ _ => ([] : List (W → Bool))) t₂ p w := by
  change necessity (f.atTime t₂) emptyBackground p w
  change necessity (f.atTime t₁) emptyBackground p w at hNec
  intro w' hBest₂
  apply hNec w'
  -- More propositions in the modal base → stronger filtering → subset of accessible worlds
  rw [kratzerBestR_empty] at hBest₂ ⊢
  rw [kratzerR_iff_accessible] at hBest₂ ⊢
  simp only [accessibleWorlds, propIntersection, TemporalConvBackground.atTime,
    Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true] at hBest₂ ⊢
  intro q hq
  exact hBest₂ q (hSub q hq)

/-! ## Future-as-modal (Ch 4 bridge) -/

/-- "Will" as a circumstantial modal with empty ordering source.
    The future marker contributes modal force (necessity over a circumstantial
    base) without adding normative/stereotypical ranking.

    This captures the unitary modal analysis: "will" does not decompose
    cleanly into force × flavor. -/
def futureAsModal (circumstantial : ModalBase W) (p : W → Bool) (w : W) : Prop :=
  necessity circumstantial emptyBackground p w

/-- Future-as-modal with empty ordering = simple necessity over the
    circumstantial base. -/
theorem future_eq_simple_necessity
    (circumstantial : ModalBase W) (p : W → Bool) (w : W) :
    futureAsModal circumstantial p w ↔
    simpleNecessity circumstantial p w := by
  exact necessity_empty_eq_simple circumstantial p w

end Semantics.Modality.Temporal
