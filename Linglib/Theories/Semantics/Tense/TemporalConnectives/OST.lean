import Linglib.Theories.Semantics.Tense.TemporalConnectives.EventBridge
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Anscombe

/-!
# Ogihara & Steinert-Threlkeld (2024): Event-Level Temporal Connectives
@cite{ogihara-steinert-threlkeld-2024}

An interval-based semantics for *before* and *after* that operates at
**Level 3** (event predicates), replacing point-level (Anscombe) and
interval-set-level (Rett) approaches with direct quantification over events
and their runtime intervals.

## Core Insight: Quantificational Asymmetry

*before* and *after* differ in quantificational force over the complement:

- **after(P, Q)** = ∃e₁∃e₂[P(e₁) ∧ Q(e₂) ∧ τ(e₂) ≺ τ(e₁)]
  Double-existential: both events must exist.

- **before(P, Q)** = ∃e₁[P(e₁) ∧ ∀e₂[Q(e₂) → τ(e₁) ≺ τ(e₂)]]
  Existential over P, **universal** over Q.

This asymmetry derives the **veridicality contrast**: *after* entails its
complement (∃e₂ asserts Q happened); *before* doesn't (∀e₂ is vacuously
true when no Q-event exists).

## Level

**Level 3 (event predicates)**: operates on `EvPred Time`. Projects to
Level 2 via `eventDenotation` (EventBridge.lean).

## Cross-Level Comparison

`OST.after P Q → Anscombe.after (eventDenotation P) (eventDenotation Q)`
but the converse fails: Anscombe allows partial overlap of runtimes,
while O&ST requires entire-runtime precedence (τ-precedence).

## References

- Ogihara, T. & Steinert-Threlkeld, S. (2024). An interval-based
  semantics for *before* and *after*.
-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval
open Semantics.Events

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: O&ST's Truth Conditions
-- ============================================================================

/-- O&ST's *after*: ∃e₁∃e₂[P(e₁) ∧ Q(e₂) ∧ τ(e₂) ≺ τ(e₁)].

    Double-existential: both the main-clause event and the subordinate-clause
    event must exist, and the subordinate event's runtime entirely precedes
    the main event's runtime. -/
def OST.after (P Q : EvPred Time) : Prop :=
  ∃ e₁ e₂ : Ev Time, P e₁ ∧ Q e₂ ∧ e₂.τ.precedes e₁.τ

/-- O&ST's *before*: ∃e₁[P(e₁) ∧ ∀e₂[Q(e₂) → τ(e₁) ≺ τ(e₂)]].

    Existential over the main clause, universal over the subordinate:
    the main event's runtime precedes that of EVERY potential subordinate event.
    When no Q-events exist, the universal is vacuously true — making *before*
    non-veridical. -/
def OST.before (P Q : EvPred Time) : Prop :=
  ∃ e₁ : Ev Time, P e₁ ∧ ∀ e₂ : Ev Time, Q e₂ → e₁.τ.precedes e₂.τ

-- ============================================================================
-- § 2: Veridicality
-- ============================================================================

/-- *After* is veridical: `after(P, Q)` entails the complement Q.

    This follows directly from the double-existential structure: the
    definition asserts ∃e₂, Q(e₂), which witnesses the complement. -/
theorem OST.after_veridical (P Q : EvPred Time) :
    OST.after P Q → ∃ e : Ev Time, Q e := by
  rintro ⟨_, e₂, _, hq, _⟩
  exact ⟨e₂, hq⟩

/-- *After* is veridical w.r.t. the main clause too: both events must exist. -/
theorem OST.after_veridical_main (P Q : EvPred Time) :
    OST.after P Q → ∃ e : Ev Time, P e := by
  rintro ⟨e₁, _, hp, _, _⟩
  exact ⟨e₁, hp⟩

/-- *Before* is non-veridical: there exist P, Q such that `before(P, Q)` holds
    but Q has no witnesses.

    Concretely: if P has a witness and Q is empty, then ∀e₂, Q(e₂) → ... is
    vacuously true. -/
theorem OST.before_nonveridical :
    ∃ (P Q : EvPred ℤ), OST.before P Q ∧ ¬∃ e : Ev ℤ, Q e := by
  refine ⟨fun e => e = ⟨⟨0, 1, by omega⟩, .action⟩, fun _ => False, ?_, ?_⟩
  · exact ⟨⟨⟨0, 1, by omega⟩, .action⟩, rfl, fun _ h => h.elim⟩
  · rintro ⟨_, h⟩; exact h

/-- *Before* is still veridical w.r.t. its main clause: the P-event must exist. -/
theorem OST.before_veridical_main (P Q : EvPred Time) :
    OST.before P Q → ∃ e : Ev Time, P e := by
  rintro ⟨e₁, hp, _⟩
  exact ⟨e₁, hp⟩

-- ============================================================================
-- § 3: Cross-Level Comparison — O&ST (Level 3) vs Anscombe (Level 1)
-- ============================================================================

/-- O&ST's *after* implies Anscombe's *after* when projected through `eventDenotation`.

    Proof: from `e₂.τ.precedes e₁.τ` (i.e., `e₂.τ.finish < e₁.τ.start`),
    take `t = e₁.τ.start` and `t' = e₂.τ.finish`. -/
theorem OST.after_implies_anscombe (P Q : EvPred Time) :
    OST.after P Q → Anscombe.after (eventDenotation P) (eventDenotation Q) := by
  rintro ⟨e₁, e₂, hp, hq, hprec⟩
  refine ⟨e₁.τ.start, ?_, e₂.τ.finish, ?_, hprec⟩
  · rw [timeTrace_eventDenotation]
    exact ⟨e₁, hp, le_refl _, e₁.τ.valid⟩
  · rw [timeTrace_eventDenotation]
    exact ⟨e₂, hq, e₂.τ.valid, le_refl _⟩

/-- O&ST's *before* implies Anscombe's *before* when projected.

    Proof: from `∀e₂, Q(e₂) → e₁.τ.finish < e₂.τ.start`, take
    `t = e₁.τ.finish`. For any `t' ∈ timeTrace(eventDenotation Q)`,
    some `e₂` has `Q(e₂)` and `e₂.τ.start ≤ t'`, so
    `t = e₁.τ.finish < e₂.τ.start ≤ t'`. -/
theorem OST.before_implies_anscombe (P Q : EvPred Time) :
    OST.before P Q → Anscombe.before (eventDenotation P) (eventDenotation Q) := by
  rintro ⟨e₁, hp, hall⟩
  refine ⟨e₁.τ.finish, ?_, ?_⟩
  · rw [timeTrace_eventDenotation]
    exact ⟨e₁, hp, e₁.τ.valid, le_refl _⟩
  · intro t' ht'
    rw [timeTrace_eventDenotation] at ht'
    obtain ⟨e₂, hq, ht'_lo, _⟩ := ht'
    exact lt_of_lt_of_le (hall e₂ hq) ht'_lo

-- ============================================================================
-- § 4: Divergence — Anscombe Does NOT Imply O&ST
-- ============================================================================

/-- Anscombe's *before* does NOT imply O&ST's *before*: the converse of
    `before_implies_anscombe` fails.

    Counterexample: P-event at [1,5], Q-event at [3,8].
    - Anscombe: t=1 ∈ timeTrace P, and 1 < all t' ∈ [3,8]. ✓
    - O&ST: τ(e₁).finish = 5, τ(e₂).start = 3, and 5 < 3 is false. ✗

    The point-level theory sees a point in A before all of B; the event-level
    theory requires the entire A-runtime to precede the entire B-runtime. -/
theorem anscombe_before_not_implies_ost :
    ¬∀ (P Q : EvPred ℤ),
      Anscombe.before (eventDenotation P) (eventDenotation Q) → OST.before P Q := by
  intro h
  -- Define overlapping events: P at [1,5], Q at [3,8]
  let eP : Ev ℤ := ⟨⟨1, 5, by omega⟩, .action⟩
  let eQ : Ev ℤ := ⟨⟨3, 8, by omega⟩, .action⟩
  let P : EvPred ℤ := fun e => e = eP
  let Q : EvPred ℤ := fun e => e = eQ
  -- Anscombe holds: witness t = 1
  have hansc : Anscombe.before (eventDenotation P) (eventDenotation Q) := by
    refine ⟨1, ?_, ?_⟩
    · rw [timeTrace_eventDenotation]
      exact ⟨eP, rfl, by simp [Ev.τ, eP], by simp [Ev.τ, eP]⟩
    · intro t' ht'
      rw [timeTrace_eventDenotation] at ht'
      obtain ⟨e, rfl, hlo, _⟩ := ht'
      simp only [Ev.τ, eQ] at hlo; omega
  -- O&ST would require eP.τ.finish < eQ.τ.start, i.e. 5 < 3
  have host := h P Q hansc
  obtain ⟨e₁, rfl, hall⟩ := host
  have := hall eQ rfl
  simp [precedes, Ev.τ, eP, eQ] at this

/-- Anscombe's *after* does NOT imply O&ST's *after*: Anscombe allows the
    A-point to be inside B's runtime, while O&ST requires B's runtime to
    entirely precede A's.

    Counterexample: P-event at [5,5], Q-event at [1,8].
    - Anscombe: t=5, t'=1, 1 < 5. ✓
    - O&ST: τ(eQ).finish = 8 > 5 = τ(eP).start, so ¬precedes. ✗ -/
theorem anscombe_after_not_implies_ost :
    ¬∀ (P Q : EvPred ℤ),
      Anscombe.after (eventDenotation P) (eventDenotation Q) → OST.after P Q := by
  intro h
  let eP : Ev ℤ := ⟨⟨5, 5, by omega⟩, .action⟩
  let eQ : Ev ℤ := ⟨⟨1, 8, by omega⟩, .action⟩
  let P : EvPred ℤ := fun e => e = eP
  let Q : EvPred ℤ := fun e => e = eQ
  have hansc : Anscombe.after (eventDenotation P) (eventDenotation Q) := by
    refine ⟨5, ?_, 1, ?_, by omega⟩
    · rw [timeTrace_eventDenotation]
      exact ⟨eP, rfl, by simp [Ev.τ, eP], by simp [Ev.τ, eP]⟩
    · rw [timeTrace_eventDenotation]
      exact ⟨eQ, rfl, by simp [Ev.τ, eQ], by simp [Ev.τ, eQ]⟩
  have host := h P Q hansc
  obtain ⟨e₁, e₂, rfl, rfl, hprec⟩ := host
  simp [precedes, Ev.τ, eP, eQ] at hprec

end Semantics.Tense.TemporalConnectives
