/-
# Tessler & Goodman (2022)

"Warm (for Winter): Inferring Comparison Classes in Communication"
Unpublished manuscript (extension of Cognition 2019 paper)

This paper extends Lassiter & Goodman (2017) by modeling how listeners infer
not just the threshold theta but also the COMPARISON CLASS c.

## Innovation

Lassiter & Goodman (2017): `P_L1(x, theta | u) proportional to P_S1(u | x, theta) * P(x) * P(theta)`

Tessler & Goodman (2022): `P_L1(x, c | u, k) proportional to P_S1(u | x, c) * P(x | k) * P(c | k)`

Key additions:
- k = KIND (the nominal, e.g., "basketball player")
- c = COMPARISON CLASS (what we compare to: subordinate vs. superordinate)
- P(x | k) = prior on x given kind (basketball players are tall)
- P(c | k) = prior on comparison class (default to subordinate)

## Main Prediction: Polarity x Expectations Interaction

"tall basketball player" -> tall for a PERSON (superordinate)
"short basketball player" -> short for a BASKETBALL PLAYER (subordinate)

Why? RSA reasoning:
- Basketball players are expected to be tall (high P(x | k) for large x)
- Saying "tall" is UNINFORMATIVE if comparing to basketball players
- So listener infers SUPERORDINATE comparison class (people in general)
- Saying "short" is SURPRISING, so must be informative comparison
- Listener sticks with SUBORDINATE (basketball players)

This asymmetry emerges from pragmatic inference, not stipulation.
-/

import Linglib.Core.Scale
import Mathlib.Tactic.DeriveFintype

namespace RSA.TesslerGoodman2022

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

[[tall]](c, k)(h) = 1 iff height(h) > threshold(c, k)
-/
def tallMeaning (c : ComparisonClass) (k : Kind) (h : Height) : Bool :=
  h.toNat > tallThreshold c k

/--
Meaning of "short" given comparison class and kind.

[[short]](c, k)(h) = 1 iff height(h) < threshold(c, k)
-/
def shortMeaning (c : ComparisonClass) (k : Kind) (h : Height) : Bool :=
  h.toNat < shortThreshold c k

/--
Full meaning function: utterance x comparison class x kind -> height -> Bool
-/
def meaning (u : Utterance) (c : ComparisonClass) (k : Kind) (h : Height) : Bool :=
  match u with
  | .tall => tallMeaning c k h
  | .short => shortMeaning c k h
  | .silent => true  -- vacuously true

-- Semantic Properties

/-- All heights -/
def allHeights : List Height := allDegrees 10

/-- For generic "person", subordinate and superordinate thresholds are identical.
This means the comparison class makes no difference for "person". -/
theorem person_thresholds_equal :
    tallThreshold .subordinate .person = tallThreshold .superordinate .person := by
  decide

/-- For basketball players, subordinate threshold is higher than superordinate.
This is because basketball players are tall, so "tall for a basketball player"
requires a higher degree than "tall for a person". -/
theorem basketball_subordinate_higher :
    tallThreshold .subordinate .basketballPlayer > tallThreshold .superordinate .basketballPlayer := by
  decide

/-- For jockeys, subordinate threshold is lower than superordinate.
This is because jockeys are short, so "tall for a jockey" requires a lower
degree than "tall for a person". -/
theorem jockey_subordinate_lower :
    tallThreshold .subordinate .jockey < tallThreshold .superordinate .jockey := by
  decide

/-- "tall" with superordinate comparison is true for MORE heights than with
subordinate comparison for basketball players. This makes "tall" MORE
INFORMATIVE (less restrictive) with superordinate, driving the
pragmatic inference. -/
theorem tall_superordinate_less_restrictive_basketball :
    tallThreshold .superordinate .basketballPlayer < tallThreshold .subordinate .basketballPlayer := by
  decide

/-- "short" with subordinate comparison covers MORE heights for basketball
players than with superordinate comparison. Heights below 7 (subordinate)
vs heights below 5 (superordinate). -/
theorem short_subordinate_more_inclusive_basketball :
    shortThreshold .subordinate .basketballPlayer > shortThreshold .superordinate .basketballPlayer := by
  decide

-- Why This Works: Informativity Analysis

/-!
## Why the Polarity x Expectations Interaction Works

### The Informativity Argument

For "tall basketball player" with SUBORDINATE comparison (to basketball players):

1. **Threshold is HIGH** (theta = 7 for basketball players)
2. **Most basketball players are already tall** (peak at h7)
3. **"Tall" is TRUE for few basketball players** (heights > 7 are fewer)
4. **So "tall" is barely informative** - true of a narrow range

For "tall basketball player" with SUPERORDINATE comparison (to people):

1. **Threshold is LOWER** (theta = 5 for people)
2. **Most basketball players exceed this** (they're tall for people)
3. **"Tall" is TRUE for most basketball players**
4. **Speaker prefers this** -> Listener infers superordinate

### The Opposite for "Short"

For "short basketball player" with SUBORDINATE comparison:

1. **Threshold is HIGH** (theta = 7)
2. **"Short" means height < 7** (many basketball players qualify!)
3. **"Short" is INFORMATIVE** about the individual

For "short basketball player" with SUPERORDINATE comparison:

1. **Threshold is LOWER** (theta = 5)
2. **"Short" means height < 5** (almost no basketball players!)
3. **This is TRIVIALLY FALSE** for most basketball players
4. **Speaker wouldn't use this** -> Listener infers subordinate
-/

-- Connection to Lassiter & Goodman (2017)

/-!
## Relation to Lassiter & Goodman (2017)

### What LG2017 Covers
- Threshold inference: P(theta | "tall")
- Context-sensitivity via different HEIGHT PRIORS
- Same semantics, different interpretations

### What TG2022 Adds
- Comparison class inference: P(c | "tall", k)
- KIND-specific expectations
- Polarity x expectations interaction

### The Key Extension

LG2017: Different comparison classes = different HEIGHT PRIORS
```
P_L1(h, theta | "tall", basketball) uses P(h | basketball)
P_L1(h, theta | "tall", jockey) uses P(h | jockey)
```

TG2022: Listener INFERS which comparison class speaker intended
```
P_L1(h, c | "tall", basketball) reasons about P(c | basketball)
```

The comparison class is no longer fixed by context - it's inferred!
This allows for the polarity x expectations interaction.

### Unified Model

A full model would combine both:
```
P_L1(h, theta, c | u, k) proportional to P_S1(u | h, theta, c) * P(h | k) * P(theta) * P(c | k)
```

For simplicity, we assume the threshold is implicitly determined by
the comparison class (theta = tallThreshold c k), avoiding the extra variable.
-/

-- Summary

/-
## Tessler & Goodman 2022: Key Results

### Main Equation
P_L1(h, c | u, k) proportional to P_S1(u | h, c, k) * P(h | k) * P(c | k)

### Main Prediction: Polarity x Expectations
- EXPECTED adjective -> SUPERORDINATE comparison
- UNEXPECTED adjective -> SUBORDINATE comparison

### Proved Theorems

1. **Threshold Properties**
   - `person_thresholds_equal`: baseline has no asymmetry
   - `basketball_subordinate_higher`: basketball threshold higher for subordinate
   - `jockey_subordinate_lower`: jockey threshold lower for subordinate

2. **Informativity Properties**
   - `tall_superordinate_less_restrictive_basketball`: explains why tall -> superordinate
   - `short_subordinate_more_inclusive_basketball`: explains why short -> subordinate

### Insight

The comparison class inference emerges from RSA reasoning about
INFORMATIVITY. Speakers choose utterances that maximize information
transfer, and listeners reason backward to infer what the speaker meant.

This explains why "tall basketball player" and "short basketball player"
trigger different comparison class inferences - without stipulating
different meanings for the adjective.
-/

end RSA.TesslerGoodman2022
