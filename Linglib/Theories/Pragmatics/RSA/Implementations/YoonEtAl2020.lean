/-
# Yoon et al. (2020): Polite Speech RSA Model

"Polite Speech Emerges From Competing Social Goals"

## Innovation

This model has two speaker levels with different utility structures:
- **S1**: Balances informational + social utilities (weighted by φ)
- **S2**: Balances informational + social + presentational utilities (ω weights)

The presentational utility captures the speaker's desire to *appear* both
kind and honest, which uniquely drives preference for indirect speech.

## Model Structure

```
L0: Literal listener (soft semantics)
     ↑
S1: First-order speaker (φ-weighted info + social)
     ↑
L1: Pragmatic listener (jointly infers state s and goal φ)
     ↑
S2: Second-order speaker (ω-weighted info + social + presentational)
```

## Reference

Yoon, E. J., Tessler, M. H., Goodman, N. D., & Frank, M. C. (2020).
Polite Speech Emerges From Competing Social Goals.
Open Mind: Discoveries in Cognitive Science, 4, 71-87.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Linglib.Phenomena.Politeness.Studies.YoonEtAl2020
import Linglib.Core.MeasurementScale
import Linglib.Theories.Semantics.Compositional.Core.Polarity
import Linglib.Core.Proposition

namespace RSA.Implementations.YoonEtAl2020

open Phenomena.Politeness.Studies.YoonEtAl2020
open RSA RSA.Eval RSA.CombinedUtility


/-- Expected value under a distribution -/
def expectedValue (dist : List (HeartState × ℚ)) (f : HeartState → ℚ) : ℚ :=
  dist.foldl (λ acc (s, p) => acc + p * f s) 0


/--
L0: Literal listener posterior over states given utterance.

P_L0(s | w) ∝ L(w, s) · P(s)

Uses soft semantics from the norming experiment.
Assumes uniform prior over states.
-/
def L0 (w : Utterance) : List (HeartState × ℚ) :=
  let scores := allHeartStates.map λ s =>
    let sem := utteranceSemantics w s
    let prior := 1  -- Uniform prior
    (s, sem * prior)
  normalize scores

/-- L0 probability of state s given utterance w -/
def L0_prob (w : Utterance) (s : HeartState) : ℚ :=
  getScore (L0 w) s


/--
S1 utility: weighted combination of informational and social utilities.

U_S1(w; s; φ) = φ · ln(P_L0(s|w)) + (1-φ) · E_{P_L0(s|w)}[V(s)] - C(w)

Since we can't compute log exactly, we use P_L0(s|w)^α as a proxy for
exp(α · ln(P_L0(s|w))).

Here we compute the utility components separately.
-/
def S1_informationalUtility (w : Utterance) (s : HeartState) : ℚ :=
  -- Proxy: P_L0(s|w) - higher probability = more informative about s
  L0_prob w s

def S1_socialUtility (w : Utterance) : ℚ :=
  -- E_{P_L0(s|w)}[V(s)] - expected value implied to listener
  expectedValue (L0 w) subjectiveValue

/--
S1: First-order speaker distribution.

P_S1(w | s, φ) ∝ exp[α · U_S1(w; s; φ)]

φ = 1: Pure informational
φ = 0: Pure social
-/
def S1 (cfg : PolitenessConfig) (s : HeartState) (phi : ℚ) : List (Utterance × ℚ) :=
  let scores := allUtterances.map λ w =>
    let infoScore := S1_informationalUtility w s
    let socialScore := S1_socialUtility w / 3  -- Normalize to [0, 1]
    let cost := (utteranceCost w : ℚ) * cfg.costScale / 3  -- Scaled cost
    -- combined φ socialScore infoScore cost = (1-φ)·social + φ·info - cost
    let combinedScore := combined phi socialScore infoScore cost
    -- Softmax: exp(α · U) approximated by score^α for positive scores
    let softmaxScore := if combinedScore > 0 then powRat combinedScore cfg.alpha else 0
    (w, softmaxScore)
  normalize scores

/-- S1 probability of utterance w given state s and goal weight φ -/
def S1_prob (cfg : PolitenessConfig) (s : HeartState) (phi : ℚ) (w : Utterance) : ℚ :=
  getScore (S1 cfg s phi) w


/--
Discretized goal weights φ for L1 to reason over.

φ = 0: Pure social (kind)
φ = 1: Pure informational (honest)
-/
def discretePhis (steps : ℕ) : List ℚ :=
  if steps <= 1 then [1/2]
  else List.range steps |>.map λ i => (i : ℚ) / (steps - 1 : ℚ)

/--
L1: Pragmatic listener jointly infers state and S1's goal weight.

P_L1(s, φ | w) ∝ P_S1(w | s, φ) · P(s) · P(φ)

Assumes uniform priors over states and goal weights.
-/
def L1_joint (cfg : PolitenessConfig) (w : Utterance) : List ((HeartState × ℚ) × ℚ) :=
  let phis := discretePhis cfg.phiSteps
  let pairs := allHeartStates.flatMap λ s =>
    phis.map λ phi => (s, phi)
  let scores := pairs.map λ (s, phi) =>
    let s1Score := S1_prob cfg s phi w
    let statePrior := 1  -- Uniform
    let phiPrior := 1    -- Uniform
    ((s, phi), s1Score * statePrior * phiPrior)
  normalize scores

/-- L1 marginal distribution over states -/
def L1_state (cfg : PolitenessConfig) (w : Utterance) : List (HeartState × ℚ) :=
  let joint := L1_joint cfg w
  allHeartStates.map λ s =>
    let prob := joint.filter (λ ((s', _), _) => s' == s)
      |>.map (·.2) |> sumScores
    (s, prob)

/-- L1 marginal distribution over goal weights φ -/
def L1_phi (cfg : PolitenessConfig) (w : Utterance) : List (ℚ × ℚ) :=
  let joint := L1_joint cfg w
  let phis := discretePhis cfg.phiSteps
  phis.map λ phi =>
    let prob := joint.filter (λ ((_, phi'), _) => phi' == phi)
      |>.map (·.2) |> sumScores
    (phi, prob)

/-- L1 probability of state s given utterance w -/
def L1_state_prob (cfg : PolitenessConfig) (w : Utterance) (s : HeartState) : ℚ :=
  getScore (L1_state cfg w) s

/-- L1 probability of goal weight φ given utterance w -/
def L1_phi_prob (cfg : PolitenessConfig) (w : Utterance) (phi : ℚ) : ℚ :=
  getScore (L1_phi cfg w) phi


/--
S2 informational utility: how much L1 learns about the true state.

U_inf(w; s) = ln(P_L1(s | w))

We use P_L1(s|w) as a proxy (higher = more informative).
-/
def S2_informationalUtility (cfg : PolitenessConfig) (w : Utterance) (s : HeartState) : ℚ :=
  L1_state_prob cfg w s

/--
S2 social utility: expected value implied to pragmatic listener.

U_soc(w) = E_{P_L1(s|w)}[V(s)]
-/
def S2_socialUtility (cfg : PolitenessConfig) (w : Utterance) : ℚ :=
  expectedValue (L1_state cfg w) subjectiveValue

/--
S2 presentational utility: speaker wants to project a particular goal φ.

U_pres(w; φ) = ln(P_L1(φ | w))

When φ ≈ 0.5, speaker wants to appear both kind and honest.
This uniquely drives preference for indirect (negated) utterances.
-/
def S2_presentationalUtility (cfg : PolitenessConfig) (w : Utterance) (projectedPhi : ℚ) : ℚ :=
  -- Find the closest discretized phi
  let phis := discretePhis cfg.phiSteps
  -- Helper: absolute difference for rationals
  let absDiff (a b : ℚ) : ℚ := if a > b then a - b else b - a
  let closestPhi := phis.foldl (λ best phi =>
    if absDiff phi projectedPhi < absDiff best projectedPhi then phi else best) (1/2)
  L1_phi_prob cfg w closestPhi

/--
S2 total utility: weighted combination of three utilities.

U_total(w; s; ω; φ) = ω_inf · U_inf(w; s) + ω_soc · U_soc(w) + ω_pres · U_pres(w; φ) - C(w)
-/
def S2_totalUtility (cfg : PolitenessConfig) (w : Utterance) (s : HeartState)
    (weights : InferredWeights) : ℚ :=
  let infoUtil := S2_informationalUtility cfg w s
  let socialUtil := S2_socialUtility cfg w / 3  -- Normalize
  let presUtil := S2_presentationalUtility cfg w weights.phi
  let cost := (utteranceCost w : ℚ) * cfg.costScale / 3
  combined3 weights.omega_inf weights.omega_soc weights.omega_pres
    infoUtil socialUtil presUtil cost

/--
S2: Second-order polite speaker distribution.

P_S2(w | s, ω) ∝ exp[α · U_total(w; s; ω; φ)]
-/
def S2 (cfg : PolitenessConfig) (s : HeartState) (weights : InferredWeights)
    : List (Utterance × ℚ) :=
  let scores := allUtterances.map λ w =>
    let util := S2_totalUtility cfg w s weights
    -- Softmax approximation
    let softmaxScore := if util > 0 then powRat util cfg.alpha else 1/1000
    (w, softmaxScore)
  normalize scores

/-- S2 probability of utterance w given state s and goal condition -/
def S2_prob (cfg : PolitenessConfig) (s : HeartState) (goal : GoalCondition)
    (w : Utterance) : ℚ :=
  getScore (S2 cfg s (getWeights goal)) w


/--
Prediction: "Both" goal produces more negation for bad states.

When true state is 0 hearts and goal is to be both informative and kind,
the speaker should prefer "It wasn't terrible" over direct alternatives.
-/
def predictNegationForBothGoal (cfg : PolitenessConfig) (s : HeartState) : ℚ :=
  let dist := S2 cfg s weightsBoth
  -- Sum probability of all negated utterances
  dist.foldl (λ acc (w, p) =>
    if w.isNegated then acc + p else acc) 0

/-- Negation probability for informative goal -/
def predictNegationForInfoGoal (cfg : PolitenessConfig) (s : HeartState) : ℚ :=
  let dist := S2 cfg s weightsInformative
  dist.foldl (λ acc (w, p) =>
    if w.isNegated then acc + p else acc) 0

/-- Negation probability for kind goal -/
def predictNegationForKindGoal (cfg : PolitenessConfig) (s : HeartState) : ℚ :=
  let dist := S2 cfg s weightsKind
  dist.foldl (λ acc (w, p) =>
    if w.isNegated then acc + p else acc) 0


/--
L1 computation for the S1 level (for comparison with standard RSA).

Note: This captures S1 only. The full politeness model requires
the custom S2 computation above because of the presentational utility.

Uses RSA.Eval for list-based computations suitable for #eval.
-/
def s1_L1 (cfg : PolitenessConfig) (u : Utterance) : List (HeartState × ℚ) :=
  RSA.Eval.basicL1 allUtterances allHeartStates
    (λ u' s => utteranceSemantics u' s)
    (λ _ => 1)  -- Uniform prior
    cfg.alpha
    (λ w => utteranceCost w)
    u


/-- All utterances are covered -/
theorem utterances_complete : allUtterances.length = 8 := by native_decide

/-- All states are covered -/
theorem states_complete : allHeartStates.length = 4 := by native_decide

/-- Negation costs more than direct speech -/
theorem negation_costlier :
    utteranceCost .notTerrible > utteranceCost .terrible := by native_decide

/-- Soft semantics: "terrible" is highly compatible with 0 hearts -/
theorem terrible_h0_compatible :
    softSemantics .terrible .h0 = 95/100 := rfl

/-- Soft semantics: "amazing" is highly compatible with 3 hearts -/
theorem amazing_h3_compatible :
    softSemantics .amazing .h3 = 90/100 := rfl


/-
## Grounding in Compositional Semantics

The soft semantics used here connect to the gradable adjective framework
in `Montague/Lexicon/Adjectives/`:

1. **Degree semantics**: Each adjective (terrible, bad, good, amazing) corresponds
   to a position on a quality scale with threshold uncertainty.

2. **Negation**: "not terrible" uses sentential negation, which is DE
   (proven in `Montague/Entailment/Polarity.lean`).

3. **Scalar implicature**: "not amazing" implicates "not quite as good as amazing"
   which connects to the scalar reasoning in `NeoGricean/`.

The connection is:
- Adjective meanings: P(state | adjective) ≈ P(degree > θ | observation)
- Negation: P(state | NOT adjective) = 1 - P(state | adjective)

This soft semantics emerges from degree uncertainty + threshold uncertainty.
-/

-- PART 9a: Compositional Negation Properties

/-- softNot is involutive (double negation cancels).

This is the soft analog of `pnot (pnot p) = p` in Boolean logic. -/
theorem softNot_involutive : ∀ p : SoftProp, softNot (softNot p) = p := by
  intro p
  funext s
  simp only [softNot]
  ring

/-- softNot is antitone (downward entailing).

If `p s ≤ q s` for all states, then `softNot q s ≤ softNot p s`.
This is the soft analog of `pnot_isDownwardEntailing` from TruthConditional. -/
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

-- PART 9b: Connection to Montague's pnot

open TruthConditional.Core.Polarity in
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

-- PART 9c: Qualitative Predictions from Compositionality

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

-- ============================================================
-- Bridge Theorems: S1 and S2 use CombinedUtility
-- ============================================================

/-- S1's utility is `combined φ socialScore infoScore cost`:
`(1-φ)·social + φ·info - cost = φ·info + (1-φ)·social - cost`. -/
theorem s1_uses_combined (phi socialScore infoScore cost : ℚ) :
    combined phi socialScore infoScore cost =
    phi * infoScore + (1 - phi) * socialScore - cost := by
  unfold combined; ring

/-- S2's utility is `combined3 ω_inf ω_soc ω_pres U_inf U_soc U_pres cost`. -/
theorem s2_uses_combined3 (wInf wSoc wPres uInf uSoc uPres cost : ℚ) :
    combined3 wInf wSoc wPres uInf uSoc uPres cost =
    wInf * uInf + wSoc * uSoc + wPres * uPres - cost := by
  unfold combined3; ring

end RSA.Implementations.YoonEtAl2020
