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

## Grounding

Price semantics is grounded in the `HasDegree` typeclass from `Fragments/Degrees.lean`.
The literal meaning of "fifty dollars" is `numeralExact 50 price` - the price equals $50.

## References

- Kao, Justine T., Jean Y. Wu, Leon Bergen, and Noah D. Goodman. (2014).
  "Nonliteral understanding of number words." PNAS 111(33): 12002-12007.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Domains.Degrees

namespace RSA.KaoEtAl2014_Hyperbole

open RSA.Eval RSA.Domains.Degrees Montague.Domain.Degrees

-- Domain: Items, Prices, and Affects

/--
Item types from the paper.

The paper uses three everyday items with distinct price distributions:
- Electric kettles: typically cheap ($50-$100)
- Laptops: moderate range ($500-$2000)
- Watches: highly variable ($50-$10000+)
-/
inductive Item where
  | electricKettle
  | laptop
  | watch
  deriving Repr, DecidableEq, BEq

/-- Price levels (simplified from continuous) -/
inductive PriceLevel where
  | p50      -- $50 (low)
  | p500     -- $500 (medium)
  | p10000   -- $10,000 (high)
  deriving Repr, DecidableEq, BEq

/-- Map PriceLevel to its numerical value -/
def PriceLevel.value : PriceLevel → ℚ
  | .p50 => 50
  | .p500 => 500
  | .p10000 => 10000

/--
A world state: an item with its actual price.

This is what the speaker knows and the listener is trying to infer.
-/
structure Price where
  item : Item
  price : PriceLevel
  deriving Repr, DecidableEq, BEq

/-- The cost of a Price world is just its price level's value -/
def Price.cost (p : Price) : ℚ := p.price.value

/-- Price implements HasDegree via its cost -/
instance : HasDegree Price where
  degree := Price.cost

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

/-- Map Utterance to its stated value -/
def Utterance.value : Utterance → ℚ
  | .fifty => 50
  | .fiveHundred => 500
  | .tenThousand => 10000
  | .million => 1000000

/--
QUD / Communicative goal (from Kao et al. 2014).

The speaker's goal determines what information they're trying to convey:

1. **price**: Exact price only (literal communication)
2. **valence**: Affect/emotion only (hyperbole-friendly)
3. **priceValence**: Both exact price AND affect
4. **approxPrice**: Approximate price (rounded, with pragmatic slack)
5. **approxPriceValence**: Approximate price AND affect

The approximate goals use rounding: f_a(s) = Round(s, 10).
This is the key to pragmatic halo - "1001" under approxPrice is equivalent to "1000".
-/
inductive Goal where
  | price            -- exact price only
  | valence          -- affect/valence only
  | priceValence     -- both exact price and valence
  | approxPrice      -- approximate (rounded) price only
  | approxPriceValence -- approximate price and valence
  deriving Repr, DecidableEq, BEq

-- World Prior P_S (Item-Specific Price Distributions)

/--
Price prior P_S from Experiment 3a.

Different items have different typical price distributions:
- Electric kettles: typically cheap, $50 most likely
- Laptops: moderate, $500 most likely
- Watches: variable, moderate prices common

These priors are crucial for hyperbole: "1000 dollars" for a kettle
is much more likely to be hyperbolic than for a laptop.
-/
def pricePrior (p : Price) : ℚ :=
  match p.item, p.price with
  -- Electric kettle: cheap items, high price is unlikely
  | .electricKettle, .p50 => 8
  | .electricKettle, .p500 => 2
  | .electricKettle, .p10000 => 1
  -- Laptop: moderate prices typical
  | .laptop, .p50 => 1
  | .laptop, .p500 => 6
  | .laptop, .p10000 => 3
  -- Watch: highly variable
  | .watch, .p50 => 3
  | .watch, .p500 => 4
  | .watch, .p10000 => 3

-- Compositional Literal Semantics

/-!
## Deriving "The X cost u dollars"

The utterances in this model are full sentences of the form:
  "The electric kettle cost 1000 dollars"

We derive this compositionally:

1. **X** (e.g., "the electric kettle") denotes an item in a price state
2. **"cost"** is a measure predicate: cost : Price → ℚ
3. **"u dollars"** is a degree phrase denoting degree u
4. **Composition**: ⟦The X cost u dollars⟧ = cost(X) = u

The world prior P_S(X) gives the probability of different price states
for different items, which is crucial for hyperbole interpretation.

This is grounded in Montague.Domain.Degrees infrastructure.
-/

/--
The "cost" measure predicate.

⟦cost⟧ = λx. price(x)

This is the denotation of "cost" as a measure verb that maps
an item (in a price state) to its price in dollars.
-/
def costPredicate : MeasurePredicate Price :=
  MeasurePredicate.fromHasDegree Price "price (USD)"

/--
Convert an utterance to its degree phrase denotation.

⟦"fifty dollars"⟧ = DegreePhrase(50, "dollars")
⟦"a million dollars"⟧ = DegreePhrase(1000000, "dollars")
-/
def Utterance.toDegreePhrase (u : Utterance) : DegreePhrase :=
  DegreePhrase.ofRat u.value "dollars"

/--
Compositional literal semantics for "The X cost u dollars".

⟦The X cost u dollars⟧ = cost(X) = u

Given:
- X : Price (the item in its actual price state, e.g., kettle at $500)
- u : Utterance (the stated price, e.g., "a million dollars")

The sentence is true iff the item's actual cost equals the stated amount.

This derives the truth conditions compositionally:
- costPredicate.μ : Price → ℚ (the measure function)
- u.toDegreePhrase.value : ℚ (the stated degree)
- measureSentence composes them: μ(X) = u
-/
def literalCompositional (u : Utterance) (world : Price) : Bool :=
  measureSentence costPredicate world u.toDegreePhrase

/--
Simple literal semantics (equivalent, for convenience).
-/
def literal (u : Utterance) (world : Price) : Bool :=
  numeralExact u.value world

/--
**Grounding theorem**: Compositional and simple semantics are equivalent.

This shows that the compositional derivation produces the same truth
conditions as the direct `numeralExact` check.
-/
theorem literal_eq_compositional (u : Utterance) (world : Price) :
    literal u world = literalCompositional u world := rfl

/--
**Grounding theorem**: Literal semantics decomposes into measure function and degree.

  ⟦The X cost u dollars⟧ = (cost(X) == u)
                        = (HasDegree.degree X == Utterance.value u)
-/
theorem literal_uses_degree (u : Utterance) (world : Price) :
    literal u world = (HasDegree.degree world == u.value) := rfl

/--
**Grounding theorem**: The cost predicate IS the HasDegree instance.
-/
theorem costPredicate_is_hasDegree :
    costPredicate.μ = HasDegree.degree := rfl

/--
**Grounding theorem**: Cost equals the price level's dollar value.
-/
theorem cost_is_price_value (world : Price) :
    costPredicate.μ world = world.price.value := rfl

/--
Full meaning semantics: utterance is true if it matches the price component.
(Affect doesn't affect truth conditions directly - it's inferred pragmatically.)
-/
def meaningSemantics (u : Utterance) (m : Meaning) : Bool :=
  literal u m.1

-- Affect Prior P_A (Experiment 3b)

/--
Affect prior P_A(a|s) from Experiment 3b.

The probability of having affect a given price state s.
Higher prices → more likely to have strong affect (annoyed/amazed).

This is independent of item type in the paper's model.
-/
def affectPrior (p : Price) (a : Affect) : ℚ :=
  match p.price, a with
  | .p50, .neutral => 8
  | .p50, .annoyed => 1
  | .p50, .amazed => 1
  | .p500, .neutral => 3
  | .p500, .annoyed => 5
  | .p500, .amazed => 2
  | .p10000, .neutral => 1
  | .p10000, .annoyed => 5
  | .p10000, .amazed => 4

/--
Combined world + affect prior: P_S(s) × P_A(a|s)

This is the prior over full meanings (price state × affect).
-/
def priceAffectPrior (m : Meaning) : ℚ :=
  pricePrior m.1 * affectPrior m.1 m.2

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

-- QUD Projection and Equivalence

/--
Round a price to the nearest base (default 10).

This implements f_a from the paper: f_a(s) = Round(s).
"51" and "50" both round to 50, so they're equivalent under approxPrice.
-/
def roundPrice (p : Price) (base : ℚ := 10) : ℚ :=
  roundToNearest p.cost base

/--
Check if two prices are equivalent under rounding.
-/
def priceRoundingEquiv (p1 p2 : Price) (base : ℚ := 10) : Bool :=
  roundPrice p1 base == roundPrice p2 base

/--
QUD equivalence: when are two meanings "the same" for a given goal?

This is the projection function from the paper:
- price: exact price match (f_e)
- valence: same affect only
- priceValence: exact price AND same affect
- approxPrice: rounded price match (f_a)
- approxPriceValence: rounded price AND same affect
-/
def qudEquiv : Goal → Meaning → Meaning → Bool
  | .price, m1, m2 => m1.1.cost == m2.1.cost           -- Exact price
  | .valence, m1, m2 => m1.2 == m2.2                   -- Same affect only
  | .priceValence, m1, m2 => m1 == m2                  -- Both exact
  | .approxPrice, m1, m2 => priceRoundingEquiv m1.1 m2.1  -- Rounded price
  | .approxPriceValence, m1, m2 =>                     -- Rounded price + affect
      priceRoundingEquiv m1.1 m2.1 && m1.2 == m2.2

-- Enumerations

def allUtterances : List Utterance := [.fifty, .fiveHundred, .tenThousand, .million]
def allPriceLevels : List PriceLevel := [.p50, .p500, .p10000]
def allItems : List Item := [.electricKettle, .laptop, .watch]
def allAffects : List Affect := [.neutral, .annoyed, .amazed]
def allGoals : List Goal := [.price, .valence, .priceValence, .approxPrice, .approxPriceValence]

/-- All price states for a given item -/
def allPricesForItem (item : Item) : List Price :=
  allPriceLevels.map fun p => { item := item, price := p }

/-- All meanings for a given item -/
def allMeaningsForItem (item : Item) : List Meaning :=
  (allPricesForItem item).flatMap fun p => allAffects.map fun a => (p, a)

-- For the main scenario, we focus on electric kettles (where hyperbole is most striking)
def allPrices : List Price := allPricesForItem .electricKettle
def allMeanings : List Meaning := allMeaningsForItem .electricKettle

-- RSA Scenario

/-- Goal prior for hyperbole scenario -/
def goalPrior : Goal → ℚ
  | .price => 1
  | .valence => 3           -- Bias toward valence QUD (common in conversation)
  | .priceValence => 1
  | .approxPrice => 2       -- Approximate price QUD fairly common
  | .approxPriceValence => 2

/-- Uniform goal prior for strict scenario -/
def uniformGoalPrior : Goal → ℚ := fun _ => 1

-- Compute Distributions

-- Helper: construct a kettle at a given price
def kettle (p : PriceLevel) : Price := { item := .electricKettle, price := p }

/-- L0 for a QUD scenario -/
def qudL0 (u : Utterance) (q : Goal) : List (Meaning × ℚ) :=
  RSA.Eval.L0 allUtterances allMeanings (fun _ _ => extendedSemantics)
    priceAffectPrior (fun _ _ => 1) u () () () q

/-- S1 for a QUD scenario -/
def qudS1 (m : Meaning) (q : Goal) : List (Utterance × ℚ) :=
  RSA.Eval.S1 allUtterances allMeanings (fun _ _ => extendedSemantics)
    priceAffectPrior (fun _ _ => 1) qudEquiv (fun _ => 0) 1 m () () () q

/-- L1 world distribution for QUD scenario -/
def qudL1_world (u : Utterance) : List (Meaning × ℚ) :=
  RSA.Eval.qudL1_world allUtterances allMeanings allGoals
    extendedSemantics priceAffectPrior goalPrior qudEquiv 1 (fun _ => 0) u

/-- L1 goal distribution for QUD scenario -/
def qudL1_goal (u : Utterance) : List (Goal × ℚ) :=
  RSA.Eval.L1_goal allUtterances allMeanings [()] [()] [()] allGoals
    (fun _ _ => extendedSemantics) priceAffectPrior (fun _ => 1) (fun _ => 1) (fun _ => 1) goalPrior
    (fun _ _ => 1) qudEquiv (fun _ => 0) 1 u

/-- L0 for "fifty dollars" -/
def l0_fifty : List (Meaning × ℚ) := qudL0 Utterance.fifty Goal.price

/-- L0 for "million dollars" -/
def l0_million : List (Meaning × ℚ) := qudL0 Utterance.million Goal.price

/-- S1 with meaning (kettle at $500, annoyed) and QUD "affect" -/
def s1_p500_annoyed_affect : List (Utterance × ℚ) :=
  qudS1 (kettle .p500, Affect.annoyed) Goal.valence

/-- S1 with meaning (kettle at $500, annoyed) and QUD "price" -/
def s1_p500_annoyed_price : List (Utterance × ℚ) :=
  qudS1 (kettle .p500, Affect.annoyed) Goal.price

/-- L1 for "million dollars" -/
def l1_million : List (Meaning × ℚ) := qudL1_world Utterance.million

/-- L1 goal distribution for "million dollars" -/
def l1_goal_million : List (Goal × ℚ) := qudL1_goal Utterance.million

-- Evaluate

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

-- Key Predictions


/--
**Hyperbole Prediction 1**: Under QUD "affect", S1 prefers hyperbole.

When the speaker cares about conveying affect (not exact price),
hyperbolic utterances become optimal.
-/
def s1_hyperbole_optimal : Bool :=
  -- For (p500, annoyed), S1 under "affect" QUD prefers "million" over literal "fiveHundred"
  let dist := s1_p500_annoyed_affect
  getScore dist Utterance.million > getScore dist Utterance.fiveHundred

#eval s1_hyperbole_optimal
-- Expected: true (hyperbole emerges)

/--
**Hyperbole Prediction 2**: Under QUD "price", S1 prefers literal.

When the speaker cares about exact price, they use the literal utterance.
-/
def s1_literal_under_price : Bool :=
  let dist := s1_p500_annoyed_price
  getScore dist Utterance.fiveHundred > getScore dist Utterance.million

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
  let pAnnoyed := allPrices.foldl (fun acc p => acc + getScore dist (p, Affect.annoyed)) 0
  let pAmazed := allPrices.foldl (fun acc p => acc + getScore dist (p, Affect.amazed)) 0
  let pNeutral := allPrices.foldl (fun acc p => acc + getScore dist (p, Affect.neutral)) 0
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
  getScore dist Goal.valence > getScore dist Goal.price

#eval l1_infers_affect_qud
-- Expected: true

-- Contrast with Strict Semantics

/-- Strict (Boolean) semantics -/
def strictSemantics (u : Utterance) (m : Meaning) : ℚ :=
  boolToRat (meaningSemantics u m)

/-- Under strict semantics, "million" gets zero probability -/
def l0_million_strict : List (Meaning × ℚ) :=
  RSA.Eval.L0 allUtterances allMeanings (fun _ _ => strictSemantics)
    priceAffectPrior (fun _ _ => 1) Utterance.million () () () Goal.price

#eval l0_million_strict
-- All zeros (million is literally false for all meanings)

/-- S1 under strict semantics can't use hyperbole -/
def s1_strict_p500_annoyed_affect : List (Utterance × ℚ) :=
  RSA.Eval.S1 allUtterances allMeanings (fun _ _ => strictSemantics)
    priceAffectPrior (fun _ _ => 1) qudEquiv (fun _ => 0) 1
    (kettle .p500, Affect.annoyed) () () () Goal.valence

#eval s1_strict_p500_annoyed_affect
-- "million" should have probability 0

-- Summary

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
