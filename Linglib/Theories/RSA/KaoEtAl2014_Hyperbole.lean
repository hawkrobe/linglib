/-
# Kao et al. (2014)

"Nonliteral understanding of number words"
PNAS 111(33): 12002-12007

This paper models hyperbole using QUD-sensitive RSA. The key insight is that
speakers may use literally false utterances to convey *affective* information.

## The Model

Meaning space: Price × Affect
- Price: the actual cost (e.g., $50, $500, $10000)
- Affect: the emotional state (e.g., annoyed, neutral)

QUDs (communicative goals):
- "price": speaker wants listener to infer exact price
- "affect": speaker wants listener to infer affect (not necessarily exact price)
- "both": speaker wants listener to infer both

The QUD-sensitive speaker (S1) optimizes informativity w.r.t. the *projected* meaning.
When QUD = "affect", a literally false but affectively-appropriate utterance can be optimal.

## Example: "It cost a million dollars"

If true price = $500 and affect = "annoyed":
- Under QUD "price": this utterance is bad (literally false)
- Under QUD "affect": this utterance is good (conveys "annoyed" despite false price)

L1 marginalizes over QUDs, recovering that the speaker was probably:
- Talking about something expensive (true affect)
- NOT meaning the literal price (unlikely QUD was "price")

## References

- Kao, Justine T., Jean Y. Wu, Leon Bergen, and Noah D. Goodman. (2014).
  "Nonliteral understanding of number words." PNAS 111(33): 12002-12007.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.RSA.Core

namespace RSA.KaoEtAl2014_Hyperbole

open RSA

-- ============================================================================
-- Domain: Prices and Affects
-- ============================================================================

/-- Price levels (simplified from continuous) -/
inductive Price where
  | p50      -- $50 (low)
  | p500     -- $500 (medium)
  | p10000   -- $10,000 (high)
  deriving Repr, DecidableEq, BEq

/-- Affect states -/
inductive Affect where
  | neutral
  | annoyed
  | amazed
  deriving Repr, DecidableEq, BEq

/-- Full meaning: price × affect -/
abbrev Meaning := Price × Affect

instance : BEq Meaning := instBEqProd

/-- Utterances (number expressions) -/
inductive Utterance where
  | fifty       -- "fifty dollars"
  | fiveHundred -- "five hundred dollars"
  | tenThousand -- "ten thousand dollars"
  | million     -- "a million dollars" (hyperbolic)
  deriving Repr, DecidableEq, BEq

/-- QUD / Communicative goal -/
inductive Goal where
  | price   -- care about exact price
  | affect  -- care about affect (allow hyperbole)
  | both    -- care about both (strict)
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Literal Semantics
-- ============================================================================

/--
Literal semantics: does utterance literally describe price?

Note: "million" is literally false for all actual prices in our domain.
This is key to hyperbole - L0 gives it probability 0, but S1 under QUD
"affect" can still choose it.
-/
def literal : Utterance → Price → Bool
  | .fifty, .p50 => true
  | .fifty, _ => false
  | .fiveHundred, .p500 => true
  | .fiveHundred, _ => false
  | .tenThousand, .p10000 => true
  | .tenThousand, _ => false
  | .million, _ => false  -- Never literally true!

/--
Full meaning semantics: utterance is true if it matches the price component.
(Affect doesn't affect truth conditions directly.)
-/
def meaningSemantics (u : Utterance) (m : Meaning) : Bool :=
  literal u m.1

-- ============================================================================
-- Affect Associations
-- ============================================================================

/--
Prior association between prices and affects.

This captures the intuition that:
- Low prices → neutral affect (it's cheap, who cares)
- High prices → annoyed/amazed affect (emotional reaction)
-/
def priceAffectPrior : Meaning → ℚ
  | (.p50, .neutral) => 8
  | (.p50, .annoyed) => 1
  | (.p50, .amazed) => 1
  | (.p500, .neutral) => 3
  | (.p500, .annoyed) => 5
  | (.p500, .amazed) => 2
  | (.p10000, .neutral) => 1
  | (.p10000, .annoyed) => 5
  | (.p10000, .amazed) => 4

/--
Utterance "arousal" - how emotionally charged is the utterance?

Higher numbers are more emotionally evocative.
"Million" is maximally arousing (hyperbole).
-/
def utteranceArousal : Utterance → ℚ
  | .fifty => 1
  | .fiveHundred => 2
  | .tenThousand => 4
  | .million => 10

/--
Extended semantics: includes affect compatibility.

An utterance is "compatible" with a meaning if:
1. It's literally true of the price, OR
2. It has high arousal and meaning has strong affect

This allows hyperbolic utterances to be somewhat compatible with
high-affect meanings even when literally false.
-/
def extendedSemantics (u : Utterance) (m : Meaning) : ℚ :=
  if literal u m.1 then 1
  else
    -- Soft penalty for literal falsity, reduced by arousal match
    match m.2 with
    | .neutral => 0  -- Hyperbole requires affect
    | .annoyed => utteranceArousal u / 20  -- Some compatibility
    | .amazed => utteranceArousal u / 20

-- ============================================================================
-- QUD Equivalence
-- ============================================================================

/-- QUD equivalence: when are two meanings "the same" for a given goal? -/
def qudEquiv : Goal → Meaning → Meaning → Bool
  | .price, m1, m2 => m1.1 == m2.1  -- Same price
  | .affect, m1, m2 => m1.2 == m2.2  -- Same affect
  | .both, m1, m2 => m1 == m2        -- Same everything

-- ============================================================================
-- Enumerations
-- ============================================================================

def allUtterances : List Utterance := [.fifty, .fiveHundred, .tenThousand, .million]
def allPrices : List Price := [.p50, .p500, .p10000]
def allAffects : List Affect := [.neutral, .annoyed, .amazed]
def allMeanings : List Meaning := allPrices.flatMap fun p => allAffects.map fun a => (p, a)
def allGoals : List Goal := [.price, .affect, .both]

-- ============================================================================
-- RSA Scenario
-- ============================================================================

/--
Hyperbole scenario with extended semantics.

Uses soft extended semantics that allows some compatibility between
hyperbolic utterances and high-affect meanings.
-/
def hyperboleScenario : RSAScenario :=
  RSAScenario.qud
    allUtterances allMeanings allGoals
    extendedSemantics
    qudEquiv
    priceAffectPrior
    (fun
      | .price => 1
      | .affect => 3  -- Bias toward affect QUD (common in conversation)
      | .both => 1)

/--
Strict scenario with Boolean semantics.

Only literally true utterances are valid.
This shows the contrast - without soft semantics, hyperbole can't work.
-/
def strictScenario : RSAScenario :=
  RSAScenario.qud
    allUtterances allMeanings allGoals
    (fun u m => boolToRat (meaningSemantics u m))
    qudEquiv
    priceAffectPrior

-- ============================================================================
-- Compute Distributions
-- ============================================================================

/-- L0 for "fifty dollars" -/
def l0_fifty : List (Meaning × ℚ) := RSA.L0 hyperboleScenario Utterance.fifty () () () Goal.price

/-- L0 for "million dollars" -/
def l0_million : List (Meaning × ℚ) := RSA.L0 hyperboleScenario Utterance.million () () () Goal.price

/-- S1 with meaning (p500, annoyed) and QUD "affect" -/
def s1_p500_annoyed_affect : List (Utterance × ℚ) :=
  RSA.S1 hyperboleScenario (Price.p500, Affect.annoyed) () () () Goal.affect

/-- S1 with meaning (p500, annoyed) and QUD "price" -/
def s1_p500_annoyed_price : List (Utterance × ℚ) :=
  RSA.S1 hyperboleScenario (Price.p500, Affect.annoyed) () () () Goal.price

/-- L1 for "million dollars" -/
def l1_million : List (Meaning × ℚ) := RSA.L1_world hyperboleScenario Utterance.million

/-- L1 goal distribution for "million dollars" -/
def l1_goal_million : List (Goal × ℚ) := RSA.L1_goal hyperboleScenario Utterance.million

-- ============================================================================
-- Evaluate
-- ============================================================================

#eval l0_fifty
-- L0("fifty"): should prefer (p50, *) meanings

#eval l0_million
-- L0("million"): soft compatibility with high-affect meanings

#eval s1_p500_annoyed_affect
-- S1(p500, annoyed | QUD=affect): should use hyperbole!

#eval s1_p500_annoyed_price
-- S1(p500, annoyed | QUD=price): should prefer "fiveHundred"

#eval l1_million
-- L1("million"): should infer high affect, uncertain price

#eval l1_goal_million
-- L1_goal("million"): should infer QUD was probably "affect"

-- ============================================================================
-- Key Predictions
-- ============================================================================

/-- Get probability from a distribution -/
def getProb {α : Type} [BEq α] (dist : List (α × ℚ)) (x : α) : ℚ :=
  RSA.getScore dist x

/--
**Hyperbole Prediction 1**: Under QUD "affect", S1 prefers hyperbole.

When the speaker cares about conveying affect (not exact price),
hyperbolic utterances become optimal.
-/
def s1_hyperbole_optimal : Bool :=
  -- For (p500, annoyed), S1 under "affect" QUD prefers "million" over literal "fiveHundred"
  let dist := s1_p500_annoyed_affect
  getProb dist Utterance.million > getProb dist Utterance.fiveHundred

#eval s1_hyperbole_optimal
-- Expected: true (hyperbole emerges)

/--
**Hyperbole Prediction 2**: Under QUD "price", S1 prefers literal.

When the speaker cares about exact price, they use the literal utterance.
-/
def s1_literal_under_price : Bool :=
  let dist := s1_p500_annoyed_price
  getProb dist Utterance.fiveHundred > getProb dist Utterance.million

#eval s1_literal_under_price
-- Expected: true

/--
**Hyperbole Prediction 3**: L1 hearing "million" infers high affect.

Despite the literal meaning being false, the pragmatic listener
correctly infers the speaker meant to convey strong affect.
-/
def l1_infers_affect : Bool :=
  let dist := l1_million
  -- P(annoyed | million) + P(amazed | million) > P(neutral | million)
  let pAnnoyed := allPrices.foldl (fun acc p => acc + getProb dist (p, Affect.annoyed)) 0
  let pAmazed := allPrices.foldl (fun acc p => acc + getProb dist (p, Affect.amazed)) 0
  let pNeutral := allPrices.foldl (fun acc p => acc + getProb dist (p, Affect.neutral)) 0
  pAnnoyed + pAmazed > pNeutral

#eval l1_infers_affect
-- Expected: true

/--
**Hyperbole Prediction 4**: L1 infers speaker's QUD was "affect".

When hearing hyperbole, the listener infers the speaker was probably
trying to communicate affect, not exact price.
-/
def l1_infers_affect_qud : Bool :=
  let dist := l1_goal_million
  getProb dist Goal.affect > getProb dist Goal.price

#eval l1_infers_affect_qud
-- Expected: true

-- ============================================================================
-- Contrast with Strict Semantics
-- ============================================================================

/-- Under strict semantics, "million" gets zero probability -/
def l0_million_strict : List (Meaning × ℚ) := RSA.L0 strictScenario Utterance.million () () () Goal.price

#eval l0_million_strict
-- All zeros (million is literally false for all meanings)

/-- S1 under strict semantics can't use hyperbole -/
def s1_strict_p500_annoyed_affect : List (Utterance × ℚ) :=
  RSA.S1 strictScenario (Price.p500, Affect.annoyed) () () () Goal.affect

#eval s1_strict_p500_annoyed_affect
-- "million" should have probability 0

-- ============================================================================
-- Summary
-- ============================================================================

/-
## How QUD-RSA Derives Hyperbole

1. **Standard RSA** (without QUDs):
   - L0 assigns 0 probability to literally false utterances
   - S1 never chooses hyperbolic utterances
   - Hyperbole can't emerge

2. **QUD-RSA**:
   - S1 optimizes w.r.t. *projected* meaning under QUD
   - Under QUD "affect", meanings with same affect are equivalent
   - "Million" evokes high arousal → compatible with high-affect meanings
   - S1 can rationally choose "million" to communicate "annoyed"

3. **L1 Inference**:
   - Listener marginalizes over possible QUDs
   - Hearing "million" → infers speaker probably had "affect" QUD
   - Correctly recovers high-affect meaning despite literal falsity

## Key Modeling Choices

1. **Extended semantics**: Allows soft compatibility between
   hyperbolic utterances and high-affect meanings

2. **Arousal**: Captures that "million" is more emotionally evocative
   than "fifty", even when both are literally false

3. **QUD prior**: Biased toward "affect" QUD, reflecting that
   affective communication is common in everyday speech

## References

- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
- Roberts (2012). Information structure in discourse.
- Kao & Goodman (2015). Let's talk (ironically) about the weather.
-/

end RSA.KaoEtAl2014_Hyperbole
