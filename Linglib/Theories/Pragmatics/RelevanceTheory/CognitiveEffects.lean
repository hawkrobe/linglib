import Mathlib.Data.Rat.Defs

/-!
# Cognitive Effects — Sperber & Wilson (1986/95)

Cognitive effects are changes in an individual's beliefs from processing an
input in a context. Three types:

1. **Strengthening**: Existing assumption gains evidential support
2. **Contradiction**: Existing assumption contradicted and eliminated
3. **Contextual implication**: New conclusion from input + context jointly

An input with no cognitive effects is irrelevant. More effects = more
relevant (other things being equal).

The 2nd edition (Postface, p. 265) renames "contextual effects" to
"cognitive effects" to emphasize these are changes in the individual's
cognitive state.

## References

Sperber, D. & Wilson, D. (1986/95). Relevance. Ch. 3 §1-3; Postface.
-/

set_option autoImplicit false

namespace Theories.Pragmatics.RelevanceTheory

/-- The three types of cognitive effect (S&W, Ch. 3).
    These exhaust the ways new information can be relevant in a context.
    An input producing none of these is irrelevant. -/
inductive EffectType where
  /-- Existing assumption strengthened by new evidence -/
  | strengthening
  /-- Existing assumption contradicted and eliminated -/
  | contradiction
  /-- New conclusion derived from input + context jointly -/
  | contextualImplication
  deriving DecidableEq, BEq, Repr

/-- All three types are positive cognitive effects. Contradiction is
    positive because eliminating a false assumption improves the
    individual's representation of the world. -/
def EffectType.isPositive : EffectType → Bool
  | .strengthening => true
  | .contradiction => true
  | .contextualImplication => true

/-- Every effect type is positive. -/
theorem EffectType.all_positive (e : EffectType) : e.isPositive = true := by
  cases e <;> rfl

/-- An effect profile: the cognitive effects of processing an input in
    context, with an overall magnitude assessment.

    The practitioner classifies the effects and estimates their magnitude;
    the comprehension procedure uses the magnitude for relevance
    assessment. -/
structure EffectProfile where
  /-- Which types of effects are produced -/
  effects : List EffectType
  /-- Overall magnitude (higher = more relevant, all else equal) -/
  magnitude : ℕ
  deriving Repr

/-- Does the profile contain any positive effects? -/
def EffectProfile.hasPositiveEffects (p : EffectProfile) : Bool :=
  !p.effects.isEmpty

/-- An input with no effects is irrelevant (S&W, Ch. 3). -/
def EffectProfile.irrelevant (p : EffectProfile) : Prop :=
  p.effects = [] ∧ p.magnitude = 0

end Theories.Pragmatics.RelevanceTheory
