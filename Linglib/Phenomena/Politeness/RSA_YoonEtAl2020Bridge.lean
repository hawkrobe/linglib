import Linglib.Phenomena.Politeness.Studies.YoonEtAl2020
import Linglib.Core.Scale
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Proposition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Bridge: RSA Politeness Model → Phenomena Data

Connects the RSA politeness model for Yoon et al. (2020) to empirical data
in `Phenomena.Politeness.Studies.YoonEtAl2020`.

The entire RSA model for this paper consumes Phenomena types (HeartState,
Utterance, SoftProp, etc.), so all model code lives here rather than in
`Theories/Pragmatics/RSA/Implementations/YoonEtAl2020.lean`.

## Status

RSA evaluation infrastructure (normalize, getScore, basicL1, combined,
combined3, powRat) has been removed. Compositional semantics theorems
(softNot properties, negation compositionality, Montague connections)
are preserved. RSA model stubs remain with `sorry` for future
reimplementation.
-/


namespace RSA.Implementations.YoonEtAl2020

open Phenomena.Politeness.Studies.YoonEtAl2020


-- Compositional Negation Properties

/-- softNot is involutive (double negation cancels).

This is the soft analog of `pnot (pnot p) = p` in Boolean logic. -/
theorem softNot_involutive : ∀ p : SoftProp, softNot (softNot p) = p := by
  intro p
  funext s
  simp only [softNot]
  ring

/-- softNot is antitone (downward entailing).

If `p s ≤ q s` for all states, then `softNot q s ≤ softNot p s`.
This is the soft analog of `pnot_isDownwardEntailing` from Semantics.Montague. -/
theorem softNot_antitone : ∀ p q : SoftProp,
    (∀ s, p s ≤ q s) → (∀ s, softNot q s ≤ softNot p s) := by
  intro p q hpq s
  simp only [softNot]
  -- 1 - q s ≤ 1 - p s  ↔  p s ≤ q s
  linarith [hpq s]

/-- Negated utterances are compositionally derived.

`utteranceSemantics .notX = softNot (utteranceSemantics .X)`. -/
theorem negation_is_compositional :
    (utteranceSemantics .notTerrible = softNot (utteranceSemantics .terrible)) ∧
    (utteranceSemantics .notBad = softNot (utteranceSemantics .bad)) ∧
    (utteranceSemantics .notGood = softNot (utteranceSemantics .good)) ∧
    (utteranceSemantics .notAmazing = softNot (utteranceSemantics .amazing)) := by
  simp only [utteranceSemantics, adjMeaning, and_self]

-- Connection to Montague's pnot

open Semantics.Entailment.Polarity in
/-- softNot mirrors pnot structure.

Both negation operators share the same algebraic structure:
1. Involution: `not(not(x)) = x`
2. Antitone: reverses ordering (DE property)

`pnot_isDownwardEntailing` proves the Boolean case; `softNot_antitone` proves the soft case. -/
theorem softNot_mirrors_pnot_structure :
    -- Both are involutions
    (∀ p : SoftProp, softNot (softNot p) = p) ∧
    -- softNot is antitone (like pnot)
    (∀ p q : SoftProp, (∀ s, p s ≤ q s) → (∀ s, softNot q s ≤ softNot p s)) :=
  ⟨softNot_involutive, softNot_antitone⟩

/-- At Boolean endpoints, softNot = pnot.

When soft semantics take values in {0, 1}, the operations coincide. -/
theorem softNot_matches_boolean :
    softNot (λ _ => 0) = (λ _ => 1) ∧
    softNot (λ _ => 1) = (λ _ => 0) := by
  constructor <;> funext s <;> simp [softNot]

/-- Negation reverses the goodness ordering.

If adjective A is "better" than B (more compatible with high states),
then "not A" is "worse" than "not B" (by `softNot_antitone`). -/
theorem negation_reverses_goodness_order :
    -- "amazing" is better than "good" at h3
    adjMeaning .amazing .h3 > adjMeaning .good .h3 →
    -- So "not amazing" is less good than "not good" at h3
    softNot (adjMeaning .amazing) .h3 < softNot (adjMeaning .good) .h3 := by
  intro _
  native_decide

/-- Applying softNot twice returns the original semantics.
This mirrors `pnot_pnot_isUpwardEntailing` (DE ∘ DE = UE). -/
theorem double_negation_cancels :
    ∀ adj : Adjective, softNot (softNot (adjMeaning adj)) = adjMeaning adj := by
  intro adj
  exact softNot_involutive (adjMeaning adj)

-- Qualitative Predictions from Compositionality

/-- Negation makes bad states more acceptable.

For "terrible": direct form is highly compatible with 0 hearts;
compositional "not terrible" is highly compatible with higher states.
This emerges from the compositional semantics, not stipulated. -/
theorem negation_shifts_compatibility :
    -- "terrible" peaks at h0
    adjMeaning .terrible .h0 > adjMeaning .terrible .h3 →
    -- "not terrible" (compositionally derived) peaks away from h0
    softNot (adjMeaning .terrible) .h0 < softNot (adjMeaning .terrible) .h3 := by
  intro _
  native_decide

/-- Negation is informationally weaker.

"Not terrible" is compatible with multiple states (1, 2, 3 hearts),
while "good" is more specific (peaks at 2-3 hearts).

This weak informativity combined with face-saving is why "both" goal
speakers prefer negation. -/
theorem negation_is_vague :
    -- "not terrible" has high probability for states 1, 2, 3
    softNot (adjMeaning .terrible) .h1 > 90/100 ∧
    softNot (adjMeaning .terrible) .h2 > 90/100 ∧
    softNot (adjMeaning .terrible) .h3 > 90/100 := by
  native_decide

-- Data Verification

/-- All utterances are covered -/
theorem utterances_complete : allUtterances.length = 8 := rfl

/-- All states are covered -/
theorem states_complete : allHeartStates.length = 4 := rfl

/-- Negation costs more than direct speech -/
theorem negation_costlier :
    utteranceCost .notTerrible > utteranceCost .terrible := by native_decide

/-- Soft semantics: "terrible" is highly compatible with 0 hearts -/
theorem terrible_h0_compatible :
    softSemantics .terrible .h0 = 95/100 := rfl

/-- Soft semantics: "amazing" is highly compatible with 3 hearts -/
theorem amazing_h3_compatible :
    softSemantics .amazing .h3 = 90/100 := rfl

end RSA.Implementations.YoonEtAl2020
