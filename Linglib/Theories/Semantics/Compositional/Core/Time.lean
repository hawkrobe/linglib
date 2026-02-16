import Linglib.Core.Time

/-!
# Branching Time and Temporal Propositions

Theory-specific temporal infrastructure that commits to truth-conditional
evaluation at situation indices.

The framework-agnostic layer (intervals, situations, temporal relations,
Reichenbach frames) lives in `Core.Time` and `Core.Reichenbach`.

## Key Concepts

1. **Historical modal base** (Thomason 1984) for future branching
2. **Temporal propositions** evaluated at situations

## References

- Thomason, R. (1984). Combinations of tense and modality.
- Condoravdi, M. (2002). Temporal interpretation of modals.
-/

namespace Semantics.Compositional.Core.Time

open _root_.Core.Time

/--
World history function: given a world and time, returns worlds that
agree with that world up to that time.

This is the basis for the "historical" or "open future" modal base
used in future-oriented modality.

Intuition: At time t in world w, multiple futures are possible.
The historical alternatives are all worlds that share the same
past with w up to t.
-/
def WorldHistory (W Time : Type*) := W → Time → Set W

/--
Historical modal base: situations whose worlds agree with s up to τ(s),
and whose times are at or after τ(s).

Following Thomason (1984) and Condoravdi (2002):
- Past is fixed (determined)
- Future branches (open)

hist(s) = {s' : w_{s'} ∈ H(wₛ, τ(s)) ∧ τ(s') ≥ τ(s)}
-/
def historicalBase {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (s : Situation W Time) : Set (Situation W Time) :=
  { s' | s'.world ∈ history s.world s.time ∧ s'.time ≥ s.time }

/--
A world history is reflexive if every world agrees with itself.
-/
def WorldHistory.reflexive {W Time : Type*} (h : WorldHistory W Time) : Prop :=
  ∀ w t, w ∈ h w t

/--
A world history is backwards-closed: if w' agrees with w up to t,
and t' ≤ t, then w' agrees with w up to t'.

"If two worlds agree up to time t, they also agree up to any earlier time."
-/
def WorldHistory.backwardsClosed {W Time : Type*} [LE Time]
    (h : WorldHistory W Time) : Prop :=
  ∀ w w' t t', t' ≤ t → w' ∈ h w t → w' ∈ h w t'

/--
Standard historical modal base properties.
-/
structure HistoricalProperties {W Time : Type*} [LE Time]
    (h : WorldHistory W Time) : Prop where
  /-- Every world agrees with itself -/
  refl : h.reflexive
  /-- Agreement is preserved for earlier times -/
  backwards : h.backwardsClosed


/--
A temporal proposition: true or false at each situation.

This is the situation-semantic analog of Prop' W.
-/
abbrev TProp (W Time : Type*) := Situation W Time → Prop

/--
Decidable temporal proposition (for computation).
-/
abbrev TBProp (W Time : Type*) := Situation W Time → Bool

/--
Lift a world proposition to a temporal proposition.

The lifted proposition is true at situation s iff the original
proposition is true at s.world.
-/
def liftProp {W Time : Type*} (p : W → Prop) : TProp W Time :=
  λ s => p s.world

/--
A proposition holds at time t in world w.
-/
def holdsAt {W Time : Type*} (p : TProp W Time) (w : W) (t : Time) : Prop :=
  p ⟨w, t⟩

end Semantics.Compositional.Core.Time
