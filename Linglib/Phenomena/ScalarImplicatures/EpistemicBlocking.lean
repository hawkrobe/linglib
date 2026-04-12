import Linglib.Core.Semantics.Proposition

/-!
# Sauerland-RSA Correspondence
@cite{sauerland-2004}

Formalizes the connection between @cite{sauerland-2004}'s epistemic implicature
framework and RSA's probabilistic reasoning.

## Sauerland's Framework

Sauerland distinguishes:
- **Primary implicatures**: ¬Kψ ("speaker doesn't know ψ")
- **Secondary implicatures**: K¬ψ ("speaker knows ¬ψ")

Secondary implicatures are derived from primary ones via an additional
"competence" assumption: the speaker either knows ψ or knows ¬ψ.

Key insight: Secondary K¬ψ is blocked if it contradicts the assertion
or the primary implicatures.

## Main Results

1. **Epistemic duality** (`duality`): ¬K¬φ ↔ Pφ — the standard equivalence
   between not-knowing-not and considering-possible.

2. **Primary-possibility correspondence** (`primary_possibility_correspondence`):
   ¬Kψ → P¬ψ — if the speaker doesn't know ψ, she considers ¬ψ possible.

3. **Blocking** (`blocking_correspondence`): Pψ → ¬K¬ψ — possibility
   blocks secondary implicatures.

## Status

RSA L1 computation and graded exclusivity theorems (showing Sauerland's
categorical framework as the α → ∞ limit of RSA) need reimplementation
with the current `RSAConfig` framework. The general RSA→IBR limit is
proved in `IBR/RSABridge.lean` (`rsa_speaker_to_ibr`).
-/

namespace Phenomena.ScalarImplicatures.EpistemicBlocking

open Core.Proposition

/-- An epistemic state represents what the speaker knows.
We model this as a set of worlds the speaker considers possible. -/
structure EpistemicState (W : Type*) where
  /-- Worlds compatible with speaker's knowledge -/
  possible : List W
  /-- Non-empty (speaker knows something is true) -/
  nonempty : possible ≠ []

/-- K operator: speaker knows φ iff φ is true in all epistemically
possible worlds. -/
def knows {W : Type*} (e : EpistemicState W) (φ : BProp W) : Bool :=
  e.possible.all φ

/-- P operator: speaker considers φ possible. -/
def possible {W : Type*} (e : EpistemicState W) (φ : BProp W) : Bool :=
  e.possible.any φ

private theorem not_not_eq_true (b : Bool) : ((!b) ≠ true) ↔ (b = true) := by
  cases b <;> decide

private theorem not_eq_true_iff (b : Bool) : ((!b) = true) ↔ (b = false) := by
  cases b <;> decide

/-- Standard epistemic duality: ¬K¬φ ↔ Pφ. -/
theorem duality {W : Type*} (e : EpistemicState W) (φ : BProp W) :
    (knows e (λ w => !φ w) = false) ↔ (possible e φ = true) := by
  simp only [knows, possible, Bool.eq_false_iff, ne_eq, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h
    push_neg at h
    obtain ⟨w, hw, hneg⟩ := h
    use w, hw
    exact (not_not_eq_true (φ w)).mp hneg
  · intro ⟨w, hw, hφ⟩ h
    have hneg := h w hw
    rw [not_eq_true_iff] at hneg
    rw [hφ] at hneg
    contradiction

/-- Secondary implicature: speaker knows the alternative is false. -/
def hasSecondaryImplicature {W : Type*} (e : EpistemicState W) (ψ : BProp W) : Prop :=
  knows e (λ w => !ψ w) = true

/-- Key insight: if ψ is possible, then K¬ψ is blocked. -/
theorem secondary_blocked_if_possible {W : Type*} (e : EpistemicState W) (ψ : BProp W) :
    possible e ψ = true → knows e (λ w => !ψ w) = false := by
  intro hpos
  simp only [possible, List.any_eq_true] at hpos
  simp only [knows, Bool.eq_false_iff, ne_eq, List.all_eq_true]
  obtain ⟨w, hw, hψ⟩ := hpos
  intro h
  have hneg := h w hw
  rw [not_eq_true_iff] at hneg
  rw [hψ] at hneg
  contradiction

/-- **Primary-Possibility Correspondence**:
¬Kψ (speaker doesn't know ψ) → P¬ψ (speaker considers ¬ψ possible).

These are equivalent when the epistemic state corresponds to the support
of the probability distribution. -/
theorem primary_possibility_correspondence {W : Type*}
    (e : EpistemicState W) (ψ : BProp W) :
    (knows e ψ = false) → (possible e (λ w => !ψ w) = true) := by
  intro h
  simp only [knows, Bool.eq_false_iff, ne_eq, List.all_eq_true] at h
  simp only [possible, List.any_eq_true]
  push_neg at h
  obtain ⟨w, hw, hψ⟩ := h
  use w, hw
  rw [not_eq_true_iff]
  cases hψw : ψ w
  · rfl
  · exact absurd hψw hψ

/-- **Blocking Correspondence**:
Secondary K¬ψ is blocked when Pψ holds. -/
theorem blocking_correspondence {W : Type*}
    (e : EpistemicState W) (ψ : BProp W) :
    possible e ψ = true → ¬hasSecondaryImplicature e ψ := by
  intro hpos hsec
  simp only [hasSecondaryImplicature] at hsec
  have := secondary_blocked_if_possible e ψ hpos
  rw [hsec] at this
  contradiction

end Phenomena.ScalarImplicatures.EpistemicBlocking
