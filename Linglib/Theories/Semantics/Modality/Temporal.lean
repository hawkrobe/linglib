import Linglib.Theories.Semantics.Modality.Kratzer

/-!
# Temporal Modal Evaluation
@cite{abusch-1997} @cite{condoravdi-2002} @cite{kratzer-2012} @cite{werner-2006}

Modal bases and ordering sources are functions of both world and time
(Kratzer 2012 Ch. 4, Condoravdi 2002). This module extends `Kratzer.lean`
with time-indexed conversational backgrounds and derives the static
(time-independent) versions as a special case.

## Core Extension

Kratzer.lean defines `ConvBackground := World → List (BProp World)`.
@cite{kratzer-2012} Ch. 4 argues that this should be `World → Time → List (BProp World)`:
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
open Semantics.Attitudes.Intensional
open Core.Proposition

/-! ## Time-indexed conversational backgrounds -/

/-- A time-indexed conversational background maps (world, time) pairs to
    sets of propositions. This is the book's core extension: f(w,t) and g(w,t).

    At different times, the same world may yield different sets of relevant
    facts (modal base) or normative standards (ordering source). -/
abbrev TemporalConvBackground (Time : Type*) := World → Time → List (BProp World)

/-- Time-indexed modal base: what facts are relevant at (w, t). -/
abbrev TemporalModalBase (Time : Type*) := TemporalConvBackground Time

/-- Time-indexed ordering source: what standards apply at (w, t). -/
abbrev TemporalOrderingSource (Time : Type*) := TemporalConvBackground Time

/-- Fix a time t to obtain a standard (time-independent) conversational
    background. This is the "temporal perspective" operation: evaluating
    the modal at a specific time. -/
def TemporalConvBackground.atTime {Time : Type*}
    (f : TemporalConvBackground Time) (t : Time) : ConvBackground :=
  λ w => f w t

/-- Lift a time-independent background to a trivially temporal one
    (constant across time). -/
def ConvBackground.liftTemporal {Time : Type*}
    (f : ConvBackground) : TemporalConvBackground Time :=
  λ w _ => f w

/-- Lifting then fixing at any time recovers the original background. -/
theorem lift_atTime_id {Time : Type*} (f : ConvBackground) (t : Time) :
    (ConvBackground.liftTemporal f).atTime t = f := rfl

/-! ## Temporal modal evaluation -/

/-- Modal necessity evaluated at a world-time pair.

    ⟦must p⟧(w, t) = ∀w' ∈ Best(f(w,t), g(w,t), w). p(w') -/
def temporalNecessity {Time : Type*}
    (f : TemporalModalBase Time) (g : TemporalOrderingSource Time)
    (t : Time) (p : BProp World) (w : World) : Bool :=
  necessity (f.atTime t) (g.atTime t) p w

/-- Modal possibility evaluated at a world-time pair.

    ⟦might p⟧(w, t) = ∃w' ∈ Best(f(w,t), g(w,t), w). p(w') -/
def temporalPossibility {Time : Type*}
    (f : TemporalModalBase Time) (g : TemporalOrderingSource Time)
    (t : Time) (p : BProp World) (w : World) : Bool :=
  possibility (f.atTime t) (g.atTime t) p w

/-- **Temporal ↔ Static bridge**: temporal modal evaluation reduces to
    standard Kratzer when the backgrounds are time-independent. -/
theorem temporal_eq_static {Time : Type*}
    (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) (t : Time) :
    temporalNecessity (ConvBackground.liftTemporal f)
      (ConvBackground.liftTemporal g) t p w =
    necessity f g p w := rfl

/-- Temporal duality: □ₜp ↔ ¬◇ₜ¬p. -/
theorem temporal_duality {Time : Type*}
    (f : TemporalModalBase Time) (g : TemporalOrderingSource Time)
    (t : Time) (p : BProp World) (w : World) :
    (temporalNecessity f g t p w ==
     !temporalPossibility f g t (λ w' => !p w') w) = true :=
  duality (f.atTime t) (g.atTime t) p w

/-! ## Historical accessibility

Worlds share history up to time t: they agree on all facts prior to t.
This gives the "branching futures" model: the past is settled, the future
is open. -/

/-- Historical necessity: p holds at all worlds sharing w's history up to t.

    The history function (a `TemporalConvBackground`) serves as the modal base;
    the ordering source is empty (pure accessibility, no ranking). -/
def historicalNecessity {Time : Type*}
    (history : TemporalConvBackground Time)
    (t : Time) (p : BProp World) (w : World) : Bool :=
  temporalNecessity history
    (λ _ _ => ([] : List (BProp World))) t p w

/-- With empty history (no shared past), all worlds are accessible:
    historical necessity collapses to universal quantification. -/
theorem empty_history_universal {Time : Type*}
    (t : Time) (p : BProp World) (w : World) :
    historicalNecessity (λ (_ : World) (_ : Time) => ([] : List (BProp World)))
      t p w = (allWorlds.all p) := by
  -- Reduces to necessity emptyBackground emptyBackground p w
  change necessity emptyBackground emptyBackground p w = allWorlds.all p
  unfold necessity
  congr 1

/-! ## Epistemic change over time -/

/-- Evidence monotonicity: if the evidence at t₁ is a subset of the
    evidence at t₂ (more evidence was gathered), then what was necessary
    at t₁ (less evidence) is still necessary at t₂ (more evidence).

    More evidence → fewer accessible worlds → at least as many necessities. -/
theorem evidence_monotone {Time : Type*}
    (f : TemporalModalBase Time) (t₁ t₂ : Time)
    (p : BProp World) (w : World)
    (hSub : ∀ q, q ∈ f w t₁ → q ∈ f w t₂)
    (hNec : temporalNecessity f (λ _ _ => ([] : List (BProp World))) t₁ p w = true) :
    temporalNecessity f (λ _ _ => ([] : List (BProp World))) t₂ p w = true := by
  unfold temporalNecessity TemporalConvBackground.atTime at hNec ⊢
  change necessity (λ w => f w t₁) emptyBackground p w = true at hNec
  change necessity (λ w => f w t₂) emptyBackground p w = true
  unfold necessity at hNec ⊢
  rw [empty_ordering_emptyBackground] at hNec ⊢
  unfold accessibleWorlds propIntersection at hNec ⊢
  simp only [List.all_eq_true, List.mem_filter] at hNec ⊢
  intro w' ⟨hw'_mem, hw'_all⟩
  exact hNec w' ⟨hw'_mem, λ q hq => hw'_all q (hSub q hq)⟩

/-! ## Future-as-modal (Ch 4 bridge) -/

/-- "Will" as a circumstantial modal with empty ordering source.
    The future marker contributes modal force (necessity over a circumstantial
    base) without adding normative/stereotypical ranking.

    This captures the unitary modal analysis: "will" does not decompose
    cleanly into force × flavor. -/
def futureAsModal (circumstantial : ModalBase) (p : BProp World) (w : World) : Bool :=
  necessity circumstantial emptyBackground p w

/-- Future-as-modal with empty ordering = simple necessity over the
    circumstantial base. -/
theorem future_eq_simple_necessity
    (circumstantial : ModalBase) (p : BProp World) (w : World) :
    futureAsModal circumstantial p w =
    simpleNecessity circumstantial p w := by
  unfold futureAsModal simpleNecessity necessity
  rw [empty_ordering_emptyBackground]

end Semantics.Modality.Temporal
