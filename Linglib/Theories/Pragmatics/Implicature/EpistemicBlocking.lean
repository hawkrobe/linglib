import Mathlib.Data.Finset.Basic
import Linglib.Theories.Semantics.Entailment.AsymStronger

/-!
# Sauerland's Epistemic Implicature Framework
@cite{sauerland-2004}

Categorical primitives for the primary/secondary implicature distinction
of @cite{sauerland-2004}. Pure pragmatic theory — no RSA, no specific
empirical paper. Consumed by `Phenomena/.../Studies/` files (e.g.,
`Numerals/Studies/Kennedy2015.lean`) that need a categorical implicature
operator alongside or instead of an RSA derivation.

## Sauerland's Framework

Sauerland distinguishes:
- **Primary implicatures**: ¬Kψ ("speaker doesn't know ψ")
- **Secondary implicatures**: K¬ψ ("speaker knows ¬ψ")

Secondary implicatures are derived from primary ones via an additional
"competence" assumption: the speaker either knows ψ or knows ¬ψ.

Key insight: Secondary K¬ψ is blocked if it contradicts the assertion
or the primary implicatures.

## Main Results

1. **Epistemic duality** (`duality`): ¬K¬φ ↔ Pφ.
2. **Primary-possibility correspondence**: ¬Kψ → P¬ψ.
3. **Blocking**: Pψ → ¬K¬ψ — possibility blocks secondary implicatures.

The asymmetric-entailment primitive used to characterize Sauerland's
primary-implicature alternatives lives in
`Theories/Semantics/Entailment/AsymStronger.lean` as `asymStrongerOn`.
A consumer wanting "the alternatives that trigger primary implicatures"
writes `alts.filter (asymStrongerOn e.possible · φ)` directly — no
wrapper needed.

The categorical-vs-graded relationship between Sauerland and RSA (RSA as
the α → ∞ limit of Sauerland exclusion) is the subject of
`IBR/RSABridge.lean` (`rsa_speaker_to_ibr`); this file provides only the
categorical side.
-/

namespace Implicature.EpistemicBlocking

/-- An epistemic state represents what the speaker knows.
We model this as a finite set of worlds the speaker considers possible. -/
structure EpistemicState (W : Type*) where
  /-- Worlds compatible with speaker's knowledge -/
  possible : Finset W
  /-- Non-empty (speaker knows something is true) -/
  nonempty : possible.Nonempty

/-- K operator: speaker knows φ iff φ is true in all epistemically
possible worlds. -/
def knows {W : Type*} (e : EpistemicState W) (φ : W → Prop) : Prop :=
  ∀ w ∈ e.possible, φ w

instance {W : Type*} (e : EpistemicState W) (φ : W → Prop) [DecidablePred φ] :
    Decidable (knows e φ) :=
  inferInstanceAs (Decidable (∀ w ∈ e.possible, φ w))

/-- P operator: speaker considers φ possible. -/
def possible {W : Type*} (e : EpistemicState W) (φ : W → Prop) : Prop :=
  ∃ w ∈ e.possible, φ w

instance {W : Type*} (e : EpistemicState W) (φ : W → Prop) [DecidablePred φ] :
    Decidable (possible e φ) :=
  inferInstanceAs (Decidable (∃ w ∈ e.possible, φ w))

/-- Standard epistemic duality: ¬K¬φ ↔ Pφ. One of five sibling `theorem duality`s
    (see `Theories/Semantics/Modality/Kratzer/Operators.lean::duality` for the
    unification opportunity via `Core.Logic.Opposition.Square.fromBox`). -/
theorem duality {W : Type*} (e : EpistemicState W) (φ : W → Prop) :
    ¬ knows e (fun w => ¬ φ w) ↔ possible e φ := by
  simp only [knows, possible, not_forall, not_not, exists_prop]

/-- Secondary implicature: speaker knows the alternative is false. -/
def hasSecondaryImplicature {W : Type*} (e : EpistemicState W) (ψ : W → Prop) : Prop :=
  knows e (fun w => ¬ ψ w)

/-- Key insight: if ψ is possible, then K¬ψ is blocked. -/
theorem secondary_blocked_if_possible {W : Type*}
    (e : EpistemicState W) (ψ : W → Prop) :
    possible e ψ → ¬ knows e (fun w => ¬ ψ w) := by
  rintro ⟨w, hw, hψ⟩ hknow
  exact hknow w hw hψ

/-- **Primary-Possibility Correspondence**:
¬Kψ (speaker doesn't know ψ) → P¬ψ (speaker considers ¬ψ possible). -/
theorem primary_possibility_correspondence {W : Type*}
    (e : EpistemicState W) (ψ : W → Prop) :
    ¬ knows e ψ → possible e (fun w => ¬ ψ w) := by
  intro h
  simp only [knows, not_forall] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨w, hw.1, hw.2⟩

/-- **Blocking Correspondence**:
Secondary K¬ψ is blocked when Pψ holds. -/
theorem blocking_correspondence {W : Type*}
    (e : EpistemicState W) (ψ : W → Prop) :
    possible e ψ → ¬ hasSecondaryImplicature e ψ :=
  secondary_blocked_if_possible e ψ

end Implicature.EpistemicBlocking
