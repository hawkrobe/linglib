import Linglib.Core.Empirical
import Linglib.Fragments.English.Determiners
import Linglib.Theories.Semantics.Conditionals.Counterfactual
import Mathlib.Data.Rat.Defs

/-!
# @cite{ramotowska-santorio-2025} - Counterfactuals and Quantificational Force

Ramotowska, S., Marty, P., Romoli, J. & Santorio, P. (2025).
Counterfactuals and quantificational force: Experimental evidence for
selectional semantics. Semantics & Pragmatics 18, Article 6: 1–43.

## Finding

Quantifier STRENGTH determines graded truth-value judgments for
counterfactuals embedded under quantifiers, not polarity or QUD.

This supports the SELECTIONAL theory (Stalnaker + supervaluation) over:
- Homogeneity theory (von Fintel/Križ): predicts QUD × polarity interaction
- Universal theory (Lewis/Kratzer): predicts determinate true/false

## Experimental Paradigm

Two experiments using graded truth-value judgments (0–99 slider from
"completely false" to "completely true"). QUD manipulated between
subjects: E-QuD (existential: "at least one has a chance to win")
vs U-QuD (universal: "all are guaranteed to win").

- **Experiment 1** (n=87 after exclusion): Lottery scenarios where
  "only some of the tickets that have been bought win a prize."
- **Experiment 2** (n=94 after exclusion): Card game with 4 players;
  mixed scenario has 2/4 red cards (win) and 2/4 gray cards (lose).
  Also tested plural definite sentences alongside counterfactuals.

Test sentences (Experiment 2):
- "All/None/Some/Not all of the players would have won if they had
  played and finished this round."

## Key Results

- Strong quantifiers (every, no): mean ratings < 15 (Exp 1), < 4 (Exp 2)
- Weak quantifiers (some, not every): mean ratings > 84 (Exp 1), > 82 (Exp 2)
- STRENGTH: β = −77.09, p < .001 (Exp 1); β = −88.7, p < .001 (Exp 2)
- QUD: not significant for counterfactuals
  (Exp 1: β = −0.09, p = .97; Exp 2: β = −0.6, p = 0.7)
- Plural definites WERE sensitive to QUD (Exp 2: β = −12.6, p = 0.01),
  confirming the QUD manipulation was effective
-/

namespace Phenomena.Conditionals.Studies.RamotowskaEtAl2025

open Phenomena

-- ════════════════════════════════════════════════════════════════
-- Experimental Design
-- ════════════════════════════════════════════════════════════════

/-- The three theories being tested. -/
inductive Theory where
  | universal    -- Lewis/Kratzer: ∀ closest worlds
  | selectional  -- Stalnaker + supervaluation
  | homogeneity  -- Universal + homogeneity presupposition
  deriving Repr, DecidableEq, BEq

/-- Quantifiers tested in the experiment. -/
inductive Quantifier where
  | every      -- Universal affirmative (strong/positive)
  | some       -- Existential (weak/positive)
  | no         -- Universal negative (strong/negative)
  | notEvery   -- Negated universal (weak/negative)
  deriving Repr, DecidableEq, BEq

open Fragments.English.Determiners (Strength)

/-- Map local quantifiers to canonical Strength (B&C Table II). -/
def Quantifier.strength : Quantifier → Strength
  | .every => .strong | .no => .strong
  | .some => .weak   | .notEvery => .weak

/-- Quantifier strength classification, derived from canonical `Strength`. -/
def Quantifier.isStrong (q : Quantifier) : Bool := q.strength == .strong

/-- Quantifier polarity classification. -/
def Quantifier.isPositive : Quantifier → Bool
  | .every => true
  | .some => true
  | .no => false
  | .notEvery => false

/-- QUD type manipulated between subjects. -/
inductive QuDType where
  | existential  -- E-QuD: "at least one has a chance to win"
  | universal    -- U-QuD: "all are guaranteed to win"
  deriving Repr, DecidableEq, BEq

-- ════════════════════════════════════════════════════════════════
-- Theoretical Predictions (Table 3 of the paper)
-- ════════════════════════════════════════════════════════════════

/-- Selectional theory predictions (Table 3): QUD-independent.
    Strong quantifiers → rejected (low ratings),
    weak quantifiers → accepted (high ratings). -/
def selectionalPredictedHigh (q : Quantifier) : Bool := !q.isStrong

/-- Homogeneity theory predictions (Table 3): QUD-dependent.
    Positive quantifiers: high under E-QuD, low under U-QuD.
    Negative quantifiers: low under E-QuD, high under U-QuD.
    The predicted interaction is between QUD and polarity, not strength. -/
def homogeneityPredictedHigh (q : Quantifier) (qud : QuDType) : Bool :=
  match q.isPositive, qud with
  | true,  .existential => true
  | true,  .universal   => false
  | false, .existential => false
  | false, .universal   => true

-- ════════════════════════════════════════════════════════════════
-- Experimental Results
-- ════════════════════════════════════════════════════════════════

/--
Experimental datum: mean slider rating (0–99 scale) for a condition.
0 = "completely false", 99 = "completely true". -/
structure ExperimentalDatum where
  quantifier : Quantifier
  qud : QuDType
  meanRating : ℚ     -- Mean slider value (0–99 scale)
  deriving Repr

/-! ### Experiment 2 Results (card game, n=94)

Experiment 2 (§6) provides per-condition mean slider ratings for
target counterfactual (TC) sentences in the mixed scenario, reported
in §6.7.3 (p. 6:34). These are the verified values. -/

/-- Experiment 2: mean slider ratings for counterfactuals in mixed
    scenarios. Verified from paper §6.7.3 (p. 6:34).

    Strong quantifiers (every/all, none): all means < 4.
    Weak quantifiers (not all, some): all means > 82. -/
def experiment2MixedResults : List ExperimentalDatum :=
  [ -- Strong quantifiers
    { quantifier := .every, qud := .universal,    meanRating := 15/10 }  -- M = 1.5
  , { quantifier := .every, qud := .existential,  meanRating := 12/10 }  -- M = 1.2
  , { quantifier := .no,    qud := .universal,    meanRating := 33/10 }  -- M = 3.3
  , { quantifier := .no,    qud := .existential,  meanRating := 9/10  }  -- M = 0.9
    -- Weak quantifiers
  , { quantifier := .notEvery, qud := .universal,   meanRating := 821/10 } -- M = 82.1
  , { quantifier := .notEvery, qud := .existential, meanRating := 861/10 } -- M = 86.1
  , { quantifier := .some,     qud := .universal,   meanRating := 961/10 } -- M = 96.1
  , { quantifier := .some,     qud := .existential, meanRating := 972/10 } -- M = 97.2
  ]

-- ════════════════════════════════════════════════════════════════
-- Key Empirical Observations
-- ════════════════════════════════════════════════════════════════

/--
**Key empirical observation**: Strength, not polarity or QUD, determines
truth-value judgments for counterfactuals in mixed scenarios.

Strong quantifiers (every, no) have uniformly low mean ratings (< 4/99).
Weak quantifiers (some, not every) have uniformly high ratings (> 82/99).
QUD has no significant effect on counterfactual ratings. -/
def strengthEffect : Bool :=
  let strong := experiment2MixedResults.filter (·.quantifier.isStrong)
  let weak := experiment2MixedResults.filter (!·.quantifier.isStrong)
  -- All strong ratings below midpoint (50), all weak above
  strong.all (·.meanRating < 50) && weak.all (·.meanRating > 50)

#guard strengthEffect

/--
**Strength effect**: all strong quantifier ratings are below 5/99 and
all weak quantifier ratings are above 80/99 in the mixed scenario.

This extreme separation rules out chance variation and confirms that
strength is the dominant factor. -/
theorem strength_effect_verified :
    experiment2MixedResults.all (λ d =>
      if d.quantifier.isStrong then d.meanRating < 5
      else d.meanRating > 80) = true := by native_decide

/--
**QUD has no effect on counterfactuals**: within each quantifier,
E-QuD and U-QuD ratings are close (differ by < 5 points on 0–99 scale).

This is the key prediction of the selectional theory (QUD-independent)
and against the homogeneity theory (which predicts QUD × polarity). -/
def qudNoEffect : Bool :=
  let pairs := [
    (Quantifier.every, QuDType.existential, QuDType.universal),
    (Quantifier.no, QuDType.existential, QuDType.universal),
    (Quantifier.some, QuDType.existential, QuDType.universal),
    (Quantifier.notEvery, QuDType.existential, QuDType.universal)
  ]
  pairs.all λ (q, qud1, qud2) =>
    match experiment2MixedResults.find? (λ d => d.quantifier == q && d.qud == qud1),
          experiment2MixedResults.find? (λ d => d.quantifier == q && d.qud == qud2) with
    | some d1, some d2 =>
      let diff := if d1.meanRating > d2.meanRating
                  then d1.meanRating - d2.meanRating
                  else d2.meanRating - d1.meanRating
      diff < 5  -- Within 5 points on 0–99 scale
    | _, _ => false

#guard qudNoEffect

-- ════════════════════════════════════════════════════════════════
-- Theory Evaluation
-- ════════════════════════════════════════════════════════════════

/--
**Selectional theory succeeds**: predictions match data.

The selectional theory predicts that quantifier strength determines
ratings regardless of QUD. This matches the observed pattern:
strong quantifiers uniformly rejected, weak uniformly accepted,
with no QUD modulation. -/
def selectionalFits : Bool :=
  experiment2MixedResults.all λ d =>
    let predictedHigh := selectionalPredictedHigh d.quantifier
    if predictedHigh then d.meanRating > 50 else d.meanRating < 50

#guard selectionalFits

/--
**Homogeneity theory fails**: predicted QUD × polarity interaction absent.

The homogeneity theory predicts that positive quantifiers (every, some)
should be rated HIGH under E-QuD but LOW under U-QuD, and vice versa
for negative quantifiers. The data shows no such interaction:
- "every" is low under BOTH QUDs (~1.2 and ~1.5)
- "some" is high under BOTH QUDs (~97.2 and ~96.1) -/
def homogeneityFails : Bool :=
  -- Find a case where the homogeneity prediction is wrong
  experiment2MixedResults.any λ d =>
    let predictedHigh := homogeneityPredictedHigh d.quantifier d.qud
    -- Prediction says high but rating is low, or vice versa
    (predictedHigh && d.meanRating < 50) || (!predictedHigh && d.meanRating > 50)

#guard homogeneityFails

/--
The homogeneity theory makes wrong predictions for 4 of 8 conditions.

Under U-QuD, homogeneity predicts:
- every → low (✓ observed: 1.5)
- some → low (✗ observed: 96.1)
- no → high (✗ observed: 3.3)
- not every → high (✓ observed: 82.1)

Under E-QuD, homogeneity predicts:
- every → high (✗ observed: 1.2)
- some → high (✓ observed: 97.2)
- no → low (✓ observed: 0.9)
- not every → low (✗ observed: 86.1) -/
theorem homogeneity_wrong_count :
    (experiment2MixedResults.filter λ d =>
      let predictedHigh := homogeneityPredictedHigh d.quantifier d.qud
      (predictedHigh && d.meanRating < 50) || (!predictedHigh && d.meanRating > 50)
    ).length = 4 := by native_decide

-- ════════════════════════════════════════════════════════════════
-- Statistical Results
-- ════════════════════════════════════════════════════════════════

/-!
### Mixed-Effects Model Results (Table 5 of paper)

Experiment 2 target counterfactual sentences, linear mixed-effects model
with POLARITY, STRENGTH, QUD and interactions as predictors:

| Effect              | β      | p      |
|---------------------|--------|--------|
| INTERCEPT           | 46.1   | < .001 |
| STRENGTH            | −88.7  | < .001 |
| QUD                 | −0.6   | 0.7    |
| POLARITY            | 5.9    | < .001 |
| QUD:POLARITY        | 0.3    | 0.9    |
| STRENGTH:QUD        | 3.9    | 0.2    |
| STRENGTH:POLARITY   | −13.2  | < .001 |
| STR:POL:QUD         | −5.3   | 0.4    |

Key findings:
- **STRENGTH** is the dominant predictor (β = −88.7)
- **QUD** has no significant main effect or interactions
- **POLARITY** has a small effect (β = 5.9): "some" rated slightly
  higher than "not every" within weak quantifiers
- **STRENGTH×POLARITY** interaction (β = −13.2): the polarity effect
  is confined to weak quantifiers
-/

-- ════════════════════════════════════════════════════════════════
-- Grounding: Study Predictions ↔ Formal Selectional Semantics
-- ════════════════════════════════════════════════════════════════

open Semantics.Conditionals.Counterfactual
  (embeddedSelectional noSelectional notEverySelectional QStrength
   all_four_quantifiers_mixed)
open Core.Duality (Truth3)

/-- Bridge: map study quantifiers to formal selectional predictions.
    Each quantifier maps to the corresponding projection operation
    from the theory layer (`Counterfactual.lean`). -/
def Quantifier.selectionalResult (q : Quantifier) (results : List Truth3) : Truth3 :=
  match q with
  | .every    => embeddedSelectional .strong results
  | .some     => embeddedSelectional .weak results
  | .no       => noSelectional results
  | .notEvery => notEverySelectional results

/--
**Grounding theorem**: the study-level prediction (`selectionalPredictedHigh`)
agrees with the formal selectional semantics for any mixed input.

This connects the theory layer's three-valued projection operations to the
study file's simple strength-based classification. The classification is
not stipulated — it is derived from the formal theory by construction. -/
theorem selectional_prediction_grounded (q : Quantifier) (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    (q.selectionalResult (bs.map Truth3.ofBool) == .true) = selectionalPredictedHigh q := by
  obtain ⟨h1, h2, h3, h4⟩ := all_four_quantifiers_mixed bs h_some_true h_some_false
  cases q <;>
    simp only [Quantifier.selectionalResult, selectionalPredictedHigh,
      Quantifier.isStrong, Quantifier.strength, h1, h2, h3, h4] <;>
    decide

-- ════════════════════════════════════════════════════════════════
-- Connections to Other Phenomena
-- ════════════════════════════════════════════════════════════════

/-!
## Related Phenomena

1. **Projection Duality**:
   The strength effect reflects the adjoint duality between universal
   (right adjoint, fragile) and existential (left adjoint, robust)
   operators. See `Counterfactual.lean` for the formalization.

2. **Plural Definites and QUD**:
   Unlike counterfactuals, plural definite sentences ("The players won
   this round") ARE sensitive to QUD manipulation (Exp 2: E-QuD M=42.2
   vs U-QuD M=29.6, β = −12.6, p = 0.01). This confirms the QUD
   manipulation worked and that counterfactuals' insensitivity to QUD
   is a genuine semantic property, not a failure of the manipulation.

3. **Conditional Excluded Middle (CEM)**:
   Stalnaker's semantics validates CEM: (A □→ B) ∨ (A □→ ¬B).
   See `Counterfactual.lean` for the proof.
-/

end Phenomena.Conditionals.Studies.RamotowskaEtAl2025
