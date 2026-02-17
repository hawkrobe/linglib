/-
# Tessler & Goodman (2022)

"Warm (for Winter): Inferring Comparison Classes in Communication"
Unpublished manuscript (extension of Cognition 2019 paper)

This paper extends Lassiter & Goodman (2017) by modeling how listeners infer
not just the threshold θ but also the COMPARISON CLASS c.

## Innovation

Lassiter & Goodman (2017): `P_L1(x, θ | u) ∝ P_S1(u | x, θ) × P(x) × P(θ)`

Tessler & Goodman (2022): `P_L1(x, c | u, k) ∝ P_S1(u | x, c) × P(x | k) × P(c | k)`

Key additions:
- k = KIND (the nominal, e.g., "basketball player")
- c = COMPARISON CLASS (what we compare to: subordinate vs. superordinate)
- P(x | k) = prior on x given kind (basketball players are tall)
- P(c | k) = prior on comparison class (default to subordinate)

## Main Prediction: Polarity × Expectations Interaction

"tall basketball player" → tall for a PERSON (superordinate)
"short basketball player" → short for a BASKETBALL PLAYER (subordinate)

Why? RSA reasoning:
- Basketball players are expected to be tall (high P(x | k) for large x)
- Saying "tall" is UNINFORMATIVE if comparing to basketball players
- So listener infers SUPERORDINATE comparison class (people in general)
- Saying "short" is SURPRISING, so must be informative comparison
- Listener sticks with SUBORDINATE (basketball players)

This asymmetry emerges from pragmatic inference, not stipulation.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.Distribution
import Linglib.Core.MeasurementScale
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype

namespace RSA.TesslerGoodman2022

open RSA.Eval
open Core.Scale (Degree Threshold Degree.ofNat Degree.toNat Threshold.toNat
  deg thr allDegrees allThresholds)

-- Domain: Heights (backed by canonical Degree 10)

/--
Discretized height values (in inches, scaled).
Heights range from "short" (0) to "tall" (10) in discrete steps.
Now backed by the canonical `Degree 10` type with `LinearOrder` and `BoundedOrder`.
-/
abbrev Height := Degree 10

-- Domain: Comparison Classes

/--
Comparison classes for scalar adjectives.

The key distinction in the paper:
- SUBORDINATE: Compare to the kind itself (e.g., basketball players)
- SUPERORDINATE: Compare to the broader category (e.g., people in general)

Example: "tall basketball player"
- Subordinate: tall compared to basketball players
- Superordinate: tall compared to people in general

The paper shows that listeners infer which comparison class is intended.
-/
inductive ComparisonClass where
  | subordinate   -- compare to the specific kind (basketball players)
  | superordinate -- compare to the general category (people)
  deriving Repr, DecidableEq, BEq, Fintype

-- Domain: Kinds (Nominals)

/--
Kinds (nominals) that can be modified by adjectives.

Each kind has:
- An associated HEIGHT DISTRIBUTION (expectations)
- A default comparison class preference

The paper focuses on kinds with ATYPICAL expectations:
- Basketball players: expected to be TALL
- Jockeys: expected to be SHORT

These create asymmetries in comparison class inference.
-/
inductive Kind where
  | person            -- generic person (baseline)
  | basketballPlayer  -- expected to be tall
  | jockey            -- expected to be short
  deriving Repr, DecidableEq, BEq, Fintype

-- Utterances

/-- Utterances about height -/
inductive Utterance where
  | tall    -- "x is tall"
  | short   -- "x is short"
  | silent  -- say nothing (baseline)
  deriving Repr, DecidableEq, BEq, Fintype

-- Priors: P(height | kind)

/--
Height prior for generic people (baseline).
Normal distribution centered at h5.
-/
def personHeightPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 1    -- tails
  | 1 => 2
  | 2 => 5
  | 3 => 10
  | 4 => 15
  | 5 => 20   -- peak (mean)
  | 6 => 15
  | 7 => 10
  | 8 => 5
  | 9 => 2
  | _ => 1    -- tails

/--
Height prior for basketball players.
Shifted RIGHT - basketball players are taller on average.
Peak at h7 instead of h5.
-/
def basketballHeightPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 5
  | 5 => 10
  | 6 => 15
  | 7 => 20   -- peak shifted right
  | 8 => 15
  | 9 => 10
  | _ => 5

/--
Height prior for jockeys.
Shifted LEFT - jockeys are shorter on average.
Peak at h3 instead of h5.
-/
def jockeyHeightPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 5
  | 1 => 10
  | 2 => 15
  | 3 => 20   -- peak shifted left
  | 4 => 15
  | 5 => 10
  | 6 => 5
  | 7 => 2
  | 8 => 1
  | 9 => 0
  | _ => 0

/-- Height prior given kind: P(h | k) -/
def heightPriorGivenKind (k : Kind) : Height → ℚ :=
  match k with
  | .person => personHeightPrior
  | .basketballPlayer => basketballHeightPrior
  | .jockey => jockeyHeightPrior

-- Priors: P(comparison class | kind)

/--
Comparison class prior given kind: P(c | k).

The paper assumes a BASELINE preference for SUBORDINATE comparison class
(compare to the specific kind), with some probability of SUPERORDINATE
(compare to people in general).

For "basketball player":
- Default: compare to basketball players (subordinate)
- Alternative: compare to people (superordinate)
-/
def comparisonClassPrior (k : Kind) : ComparisonClass → ℚ :=
  match k with
  | .person =>
    -- For generic "person", subordinate = superordinate = people
    λ _ => 1  -- uniform
  | .basketballPlayer =>
    -- Slight preference for subordinate (compare to basketball players)
    λ c => match c with
      | .subordinate => 3    -- 60% baseline
      | .superordinate => 2  -- 40%
  | .jockey =>
    -- Slight preference for subordinate (compare to jockeys)
    λ c => match c with
      | .subordinate => 3
      | .superordinate => 2

-- Semantics: Threshold depends on Comparison Class

/--
The EFFECTIVE THRESHOLD for "tall" depends on the comparison class.

- Subordinate (basketball players): threshold is HIGHER
  (need to be tall even for a basketball player)
- Superordinate (people): threshold is at POPULATION MEAN

This is the key semantic insight: the comparison class shifts the threshold.
-/
def tallThreshold (c : ComparisonClass) (k : Kind) : Nat :=
  match c with
  | .superordinate => 5  -- population mean
  | .subordinate =>
    match k with
    | .person => 5           -- subordinate = superordinate for generic
    | .basketballPlayer => 7 -- higher threshold (basketball players are tall)
    | .jockey => 3           -- lower threshold (jockeys are short)

/--
The EFFECTIVE THRESHOLD for "short" depends on the comparison class.
-/
def shortThreshold (c : ComparisonClass) (k : Kind) : Nat :=
  tallThreshold c k  -- symmetric with tall

/--
Meaning of "tall" given comparison class and kind.

⟦tall⟧(c, k)(h) = 1 iff height(h) > threshold(c, k)
-/
def tallMeaning (c : ComparisonClass) (k : Kind) (h : Height) : Bool :=
  h.toNat > tallThreshold c k

/--
Meaning of "short" given comparison class and kind.

⟦short⟧(c, k)(h) = 1 iff height(h) < threshold(c, k)
-/
def shortMeaning (c : ComparisonClass) (k : Kind) (h : Height) : Bool :=
  h.toNat < shortThreshold c k

/--
Full meaning function: utterance × comparison class × kind → height → Bool
-/
def meaning (u : Utterance) (c : ComparisonClass) (k : Kind) (h : Height) : Bool :=
  match u with
  | .tall => tallMeaning c k h
  | .short => shortMeaning c k h
  | .silent => true  -- vacuously true

-- RSA Model with Comparison Class Inference

/--
Joint state space: (Height, ComparisonClass).

L1 reasons jointly over:
- The height of the individual
- The comparison class the speaker intended
-/
abbrev JointState := Height × ComparisonClass

instance : Fintype JointState := inferInstance
instance : DecidableEq JointState := inferInstance
instance : BEq JointState := inferInstance

/-- All heights -/
def allHeights : List Height := allDegrees 10

/--
L0: Literal listener distribution over heights given utterance and comparison class.

P_L0(h | u, c, k) ∝ 1[⟦u⟧(c,k)(h)] × P(h | k)

The literal listener:
1. Filters heights consistent with the utterance meaning
2. Weights by the kind-specific height prior
-/
def L0 (k : Kind) (c : ComparisonClass) (u : Utterance) : List (Height × ℚ) :=
  let scores := allHeights.map λ h =>
    let sem := if meaning u c k h then (1 : ℚ) else 0
    let prior := heightPriorGivenKind k h
    (h, sem * prior)
  RSA.Eval.normalize scores

/--
S1: Pragmatic speaker distribution over utterances.

P_S1(u | h, c, k) ∝ P_L0(h | u, c, k)

The speaker chooses utterances that are informative about the height,
given the comparison class they have in mind.
-/
def S1 (k : Kind) (c : ComparisonClass) (h : Height) : List (Utterance × ℚ) :=
  let utterances : List Utterance := [.tall, .short, .silent]
  let scores := utterances.map λ u =>
    let l0Score := RSA.Eval.getScore (L0 k c u) h
    (u, l0Score)
  RSA.Eval.normalize scores

/--
L1 joint: Pragmatic listener distribution over (height, comparison class).

P_L1(h, c | u, k) ∝ P_S1(u | h, c, k) × P(h | k) × P(c | k)

This is the key equation from the paper. The listener jointly infers:
- The height of the individual
- The comparison class the speaker intended

The comparison class inference is the novel contribution.
-/
def L1_joint (k : Kind) (u : Utterance) : List (JointState × ℚ) :=
  let classes : List ComparisonClass := [.subordinate, .superordinate]
  let pairs := allHeights.flatMap λ h => classes.map λ c => (h, c)
  let scores := pairs.map λ (h, c) =>
    let heightPrior := heightPriorGivenKind k h
    let classPrior := comparisonClassPrior k c
    let s1Score := RSA.Eval.getScore (S1 k c h) u
    ((h, c), heightPrior * classPrior * s1Score)
  RSA.Eval.normalize scores

/--
L1 marginal over heights: P_L1(h | u, k) = Σ_c P_L1(h, c | u, k)
-/
def L1_height (k : Kind) (u : Utterance) : List (Height × ℚ) :=
  let joint := L1_joint k u
  allHeights.map λ h =>
    let hScores := joint.filter (·.1.1 == h) |>.map (·.2)
    (h, RSA.Eval.sumScores hScores)

/--
L1 marginal over comparison classes: P_L1(c | u, k) = Σ_h P_L1(h, c | u, k)
-/
def L1_class (k : Kind) (u : Utterance) : List (ComparisonClass × ℚ) :=
  let joint := L1_joint k u
  let classes : List ComparisonClass := [.subordinate, .superordinate]
  classes.map λ c =>
    let cScores := joint.filter (·.1.2 == c) |>.map (·.2)
    (c, RSA.Eval.sumScores cScores)

-- Compute Distributions

-- L0 distributions
#eval L0 .basketballPlayer .subordinate .tall    -- tall for a basketball player
#eval L0 .basketballPlayer .superordinate .tall  -- tall for a person
#eval L0 .basketballPlayer .subordinate .short   -- short for a basketball player
#eval L0 .basketballPlayer .superordinate .short -- short for a person

-- S1 distributions
#eval S1 .basketballPlayer .subordinate (deg 8)      -- speaker with tall basketball player, comparing to BBall
#eval S1 .basketballPlayer .superordinate (deg 8)    -- speaker with tall basketball player, comparing to people

-- L1 joint distributions (the key model output)
#eval L1_joint .basketballPlayer .tall           -- "tall basketball player"
#eval L1_joint .basketballPlayer .short          -- "short basketball player"

-- L1 marginal over comparison classes (the key prediction)
#eval L1_class .basketballPlayer .tall           -- comparison class inference for "tall"
#eval L1_class .basketballPlayer .short          -- comparison class inference for "short"

-- L1 for jockeys (opposite pattern expected)
#eval L1_class .jockey .tall                     -- "tall jockey"
#eval L1_class .jockey .short                    -- "short jockey"

-- Main Theorems: Polarity × Expectations Interaction

/--
**Main Prediction: "tall basketball player" → superordinate comparison**

When hearing "tall basketball player", listeners infer the speaker
is comparing to PEOPLE IN GENERAL (superordinate), not to basketball players.

Why? Basketball players are expected to be tall. Saying "tall" when comparing
to basketball players is UNINFORMATIVE (most would be tall). To be informative,
the speaker must mean tall for a PERSON - which is noteworthy for a basketball player.

This is the key polarity × expectations interaction.
-/
theorem tall_basketball_prefers_superordinate :
    RSA.Eval.getScore (L1_class .basketballPlayer .tall) .superordinate >
    RSA.Eval.getScore (L1_class .basketballPlayer .tall) .subordinate := by
  native_decide

/--
**Main Prediction: "short basketball player" → subordinate comparison**

When hearing "short basketball player", listeners infer the speaker
is comparing to BASKETBALL PLAYERS (subordinate), not to people in general.

Why? Short is unexpected for basketball players. Saying "short" when comparing
to basketball players is HIGHLY INFORMATIVE (few would qualify). The utterance
is rationalized by the subordinate comparison class.

This is the other half of the polarity × expectations interaction.
-/
theorem short_basketball_prefers_subordinate :
    RSA.Eval.getScore (L1_class .basketballPlayer .short) .subordinate >
    RSA.Eval.getScore (L1_class .basketballPlayer .short) .superordinate := by
  native_decide

/--
**Polarity Reversal Theorem**

For basketball players, "tall" and "short" lead to OPPOSITE comparison
class inferences:
- "tall" → superordinate preferred
- "short" → subordinate preferred

This asymmetry is the paper's main empirical prediction.
-/
theorem basketball_polarity_reversal :
    (RSA.Eval.getScore (L1_class .basketballPlayer .tall) .superordinate >
     RSA.Eval.getScore (L1_class .basketballPlayer .tall) .subordinate) ∧
    (RSA.Eval.getScore (L1_class .basketballPlayer .short) .subordinate >
     RSA.Eval.getScore (L1_class .basketballPlayer .short) .superordinate) := by
  native_decide

-- Jockey Predictions: Opposite Pattern

/--
**Jockey Prediction: "short jockey" → superordinate comparison**

For jockeys (expected to be SHORT), the pattern REVERSES:
- "short jockey" → superordinate (short for a person, unremarkable for jockey)
- "tall jockey" → subordinate (tall for a jockey is noteworthy)

This demonstrates that the effect depends on KIND EXPECTATIONS, not polarity alone.
-/
theorem short_jockey_prefers_superordinate :
    RSA.Eval.getScore (L1_class .jockey .short) .superordinate >
    RSA.Eval.getScore (L1_class .jockey .short) .subordinate := by
  native_decide

/--
**Jockey Prediction: "tall jockey" → subordinate comparison**

"Tall jockey" is noteworthy because jockeys are expected to be short.
The listener infers subordinate comparison class to rationalize this.
-/
theorem tall_jockey_prefers_subordinate :
    RSA.Eval.getScore (L1_class .jockey .tall) .subordinate >
    RSA.Eval.getScore (L1_class .jockey .tall) .superordinate := by
  native_decide

/--
**Jockey Polarity Reversal**

For jockeys, the pattern is REVERSED compared to basketball players:
- "tall jockey" → subordinate (opposite of "tall basketball player")
- "short jockey" → superordinate (opposite of "short basketball player")
-/
theorem jockey_polarity_reversal :
    (RSA.Eval.getScore (L1_class .jockey .tall) .subordinate >
     RSA.Eval.getScore (L1_class .jockey .tall) .superordinate) ∧
    (RSA.Eval.getScore (L1_class .jockey .short) .superordinate >
     RSA.Eval.getScore (L1_class .jockey .short) .subordinate) := by
  native_decide

-- Cross-Kind Comparison: The General Pattern

/--
**General Pattern Theorem**

The comparison class inference follows the pattern:
- EXPECTED adjective → SUPERORDINATE comparison
- UNEXPECTED adjective → SUBORDINATE comparison

Basketball players: tall expected, short unexpected
- "tall basketball player" → superordinate
- "short basketball player" → subordinate

Jockeys: short expected, tall unexpected
- "short jockey" → superordinate
- "tall jockey" → subordinate

This pattern emerges from RSA reasoning about informativity.
-/
theorem expected_leads_to_superordinate :
    -- Expected adjectives lead to superordinate comparison
    (RSA.Eval.getScore (L1_class .basketballPlayer .tall) .superordinate >
     RSA.Eval.getScore (L1_class .basketballPlayer .tall) .subordinate) ∧
    (RSA.Eval.getScore (L1_class .jockey .short) .superordinate >
     RSA.Eval.getScore (L1_class .jockey .short) .subordinate) ∧
    -- Unexpected adjectives lead to subordinate comparison
    (RSA.Eval.getScore (L1_class .basketballPlayer .short) .subordinate >
     RSA.Eval.getScore (L1_class .basketballPlayer .short) .superordinate) ∧
    (RSA.Eval.getScore (L1_class .jockey .tall) .subordinate >
     RSA.Eval.getScore (L1_class .jockey .tall) .superordinate) := by
  native_decide

-- Height Inference: Secondary Predictions

/--
**Height Inference: "tall basketball player" shifts height UP**

Even though we're inferring superordinate comparison, hearing "tall"
still shifts the height inference upward.
-/
theorem tall_basketball_height_shift :
    RSA.Eval.getScore (L1_height .basketballPlayer .tall) (deg 8) >
    RSA.Eval.getScore (L1_height .basketballPlayer .tall) (deg 3) := by
  native_decide

/--
**Height Inference: "short basketball player" shifts height DOWN**

Hearing "short" shifts the height inference downward.
-/
theorem short_basketball_height_shift :
    RSA.Eval.getScore (L1_height .basketballPlayer .short) (deg 3) >
    RSA.Eval.getScore (L1_height .basketballPlayer .short) (deg 8) := by
  native_decide

-- Baseline: Generic "person"

/--
**Baseline: For "person", no comparison class asymmetry**

For generic "person", subordinate and superordinate are identical,
so there should be no strong preference either way.

Note: With uniform prior over comparison classes for person, the
scores should be equal (or close, depending on implementation).
-/
theorem person_no_asymmetry :
    -- For person, tall and short should not strongly prefer either class
    RSA.Eval.getScore (L1_class .person .tall) .subordinate =
    RSA.Eval.getScore (L1_class .person .tall) .superordinate := by
  native_decide

-- Why This Works: Informativity Analysis

/-!
## Why the Polarity × Expectations Interaction Works

### The Informativity Argument

For "tall basketball player" with SUBORDINATE comparison (to basketball players):

1. **Threshold is HIGH** (θ = 7 for basketball players)
2. **Most basketball players are already tall** (peak at h7)
3. **"Tall" is TRUE for most basketball players** (heights > 7 are fewer)
4. **So "tall" is UNINFORMATIVE** - doesn't narrow down which player

For "tall basketball player" with SUPERORDINATE comparison (to people):

1. **Threshold is LOWER** (θ = 5 for people)
2. **Most basketball players exceed this** (they're tall for people)
3. **"Tall" is INFORMATIVE** - tells us this is a tall individual
4. **Speaker prefers this** → Listener infers superordinate

### The Opposite for "Short"

For "short basketball player" with SUBORDINATE comparison:

1. **Threshold is HIGH** (θ = 7)
2. **"Short" means height < 7** (many basketball players qualify!)
3. **But the RARE ones are very short** (< 7 is noteworthy)
4. **"Short" is HIGHLY INFORMATIVE** about the individual

For "short basketball player" with SUPERORDINATE comparison:

1. **Threshold is LOWER** (θ = 5)
2. **"Short" means height < 5** (almost no basketball players!)
3. **This is TRIVIALLY FALSE** for most basketball players
4. **Speaker wouldn't use this** → Listener infers subordinate
-/

-- Informativity Verification

/--
**Informativity: "tall" more informative with superordinate comparison**

S1 probability of "tall" is higher when comparing to people (superordinate)
than when comparing to basketball players (subordinate), for a typical
basketball player height (h7).

This is because with subordinate comparison, h7 is NOT tall (threshold is 7),
but with superordinate comparison, h7 IS tall (threshold is 5).
-/
theorem tall_more_informative_superordinate :
    RSA.Eval.getScore (S1 .basketballPlayer .superordinate (deg 7)) .tall >
    RSA.Eval.getScore (S1 .basketballPlayer .subordinate (deg 7)) .tall := by
  native_decide

/--
**Informativity: "short" more informative with subordinate comparison**

For a below-average basketball player (h5), "short" is MORE informative
with subordinate comparison (comparing to basketball players).

With subordinate: h5 < 7, so "short" applies
With superordinate: h5 = 5, so "short" doesn't apply (h5 ≮ 5)
-/
theorem short_more_informative_subordinate :
    RSA.Eval.getScore (S1 .basketballPlayer .subordinate (deg 5)) .short >
    RSA.Eval.getScore (S1 .basketballPlayer .superordinate (deg 5)) .short := by
  native_decide

-- Connection to Lassiter & Goodman (2017)

/-!
## Relation to Lassiter & Goodman (2017)

### What LG2017 Covers
- Threshold inference: P(θ | "tall")
- Context-sensitivity via different HEIGHT PRIORS
- Same semantics, different interpretations

### What TG2022 Adds
- Comparison class inference: P(c | "tall", k)
- KIND-specific expectations
- Polarity × expectations interaction

### The Key Extension

LG2017: Different comparison classes = different HEIGHT PRIORS
```
P_L1(h, θ | "tall", basketball) uses P(h | basketball)
P_L1(h, θ | "tall", jockey) uses P(h | jockey)
```

TG2022: Listener INFERS which comparison class speaker intended
```
P_L1(h, c | "tall", basketball) reasons about P(c | basketball)
```

The comparison class is no longer fixed by context - it's inferred!
This allows for the polarity × expectations interaction.

### Unified Model

A full model would combine both:
```
P_L1(h, θ, c | u, k) ∝ P_S1(u | h, θ, c) × P(h | k) × P(θ) × P(c | k)
```

For simplicity, we assume the threshold is implicitly determined by
the comparison class (θ = tallThreshold c k), avoiding the extra variable.
-/

-- Summary

/-
## Tessler & Goodman 2022: Key Results

### Main Equation
P_L1(h, c | u, k) ∝ P_S1(u | h, c, k) × P(h | k) × P(c | k)

### Main Prediction: Polarity × Expectations
- EXPECTED adjective → SUPERORDINATE comparison
- UNEXPECTED adjective → SUBORDINATE comparison

### Proved Theorems

1. **Basketball Player Predictions**
   - `tall_basketball_prefers_superordinate`: "tall" → people comparison
   - `short_basketball_prefers_subordinate`: "short" → basketball comparison
   - `basketball_polarity_reversal`: the asymmetry

2. **Jockey Predictions** (opposite pattern)
   - `short_jockey_prefers_superordinate`: "short" → people comparison
   - `tall_jockey_prefers_subordinate`: "tall" → jockey comparison
   - `jockey_polarity_reversal`: the asymmetry

3. **General Pattern**
   - `expected_leads_to_superordinate`: expected → superordinate
   - `person_no_asymmetry`: baseline has no preference

4. **Informativity**
   - `tall_more_informative_superordinate`: explains why tall → superordinate
   - `short_more_informative_subordinate`: explains why short → subordinate

### Connection to Phenomena

The predictions connect to `Phenomena/Vagueness/Data.lean`:
- `ContextShiftDatum`: Same adjective, different comparison classes
- `AntonymDatum`: Polarity asymmetry in interpretation

### Insight

The comparison class inference emerges from RSA reasoning about
INFORMATIVITY. Speakers choose utterances that maximize information
transfer, and listeners reason backward to infer what the speaker meant.

This explains why "tall basketball player" and "short basketball player"
trigger different comparison class inferences - without stipulating
different meanings for the adjective.
-/

end RSA.TesslerGoodman2022
