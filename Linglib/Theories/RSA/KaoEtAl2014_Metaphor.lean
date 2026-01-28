/-
# Kao et al. (2014)

"A computational model of linguistic humor in puns"
CogSci 2014 Proceedings

This paper models metaphor using QUD-sensitive RSA. The key insight is that
metaphorical utterances communicate *features* associated with categories,
even when the category itself is literally false.

## The Model

Meaning space: Category × Features
- Category: the referent (e.g., person, fire, weapon)
- Features: properties (e.g., dangerous, unpredictable, powerful)

QUDs (communicative goals):
- "category": speaker wants listener to infer the literal category
- "feature_i": speaker wants listener to infer specific feature(s)

The QUD-sensitive speaker (S1) optimizes informativity w.r.t. the *projected* meaning.
When QUD = "feature", a literally false category can be optimal if it evokes the feature.

## Example: "John is a shark"

If John is a person but dangerous:
- Under QUD "category": this utterance is bad (John is not literally a shark)
- Under QUD "dangerous": this utterance is good (sharks are prototypically dangerous)

L1 marginalizes over QUDs, recovering that the speaker was probably:
- Talking about John being dangerous (feature)
- NOT meaning John is literally a shark (unlikely QUD was "category")

## References

- Kao, Justine T., Roger Levy, and Noah D. Goodman. (2014).
  "A computational model of linguistic humor in puns." CogSci 2014.
- Kao et al. (2014). "Nonliteral understanding of number words." PNAS.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.RSA.Core

namespace RSA.KaoEtAl2014_Metaphor

open RSA RSA

-- ============================================================================
-- Domain: Categories and Features
-- ============================================================================

/-- Categories (referents in the domain) -/
inductive Category where
  | person    -- The literal referent (e.g., "John")
  | shark     -- Metaphor vehicle (dangerous)
  | fire      -- Metaphor vehicle (dangerous, unpredictable)
  | blanket   -- Metaphor vehicle (warm, comforting)
  deriving Repr, DecidableEq, BEq

/-- Feature dimensions -/
inductive Feature where
  | dangerous      -- f1
  | unpredictable  -- f2
  | comforting     -- f3
  deriving Repr, DecidableEq, BEq

/-- Full meaning: category × feature profile -/
structure Meaning where
  category : Category
  dangerous : Bool
  unpredictable : Bool
  comforting : Bool
  deriving Repr, DecidableEq, BEq

/-- Utterances (category labels) -/
inductive Utterance where
  | person   -- "He's a person"
  | shark    -- "He's a shark"
  | fire     -- "He's a fire" / "He's on fire"
  | blanket  -- "He's a blanket"
  deriving Repr, DecidableEq, BEq

/-- QUD / Communicative goal -/
inductive Goal where
  | category      -- care about literal category
  | dangerous     -- care about dangerous feature
  | unpredictable -- care about unpredictable feature
  | comforting    -- care about comforting feature
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Category-Feature Associations (from elicitation data)
-- ============================================================================

/-
These priors capture typical feature associations with categories.
In the actual paper, these come from norming studies.

P(feature | category):
- shark: high dangerous, low unpredictable, low comforting
- fire: high dangerous, high unpredictable, low comforting
- blanket: low dangerous, low unpredictable, high comforting
- person: variable (we're asking about a specific person)
-/

/-- Feature profile for each category (prototypical values) -/
def categoryFeatures : Category → (Bool × Bool × Bool)
  | .person  => (false, false, false)  -- Baseline: neutral person
  | .shark   => (true, false, false)   -- Dangerous but predictable
  | .fire    => (true, true, false)    -- Dangerous AND unpredictable
  | .blanket => (false, false, true)   -- Comforting

/-- Make a meaning from category with its prototypical features -/
def prototypicalMeaning (c : Category) : Meaning :=
  let (d, u, cf) := categoryFeatures c
  { category := c, dangerous := d, unpredictable := u, comforting := cf }

-- ============================================================================
-- Literal Semantics
-- ============================================================================

/--
Literal semantics: does utterance literally describe the category?

Note: utterances only match their literal category.
"Shark" is literally false for persons, but metaphorically informative.
-/
def literal : Utterance → Category → Bool
  | .person, .person => true
  | .shark, .shark => true
  | .fire, .fire => true
  | .blanket, .blanket => true
  | _, _ => false

/--
Full meaning semantics: utterance is true if it matches the category component.
(Features don't affect truth conditions directly.)
-/
def meaningSemantics (u : Utterance) (m : Meaning) : Bool :=
  literal u m.category

-- ============================================================================
-- Extended Semantics (Soft Feature Match)
-- ============================================================================

/--
Feature-based compatibility score.

An utterance is "compatible" with a meaning if:
1. It's literally true of the category, OR
2. The category evoked by the utterance shares features with the meaning

This allows metaphorical utterances to be somewhat compatible with
meanings that share features, even when literally false.
-/
def featureMatch (u : Utterance) (m : Meaning) : ℚ :=
  let evoked := prototypicalMeaning (match u with
    | .person => .person | .shark => .shark | .fire => .fire | .blanket => .blanket)
  let matchCount : ℕ :=
    (if evoked.dangerous == m.dangerous then 1 else 0) +
    (if evoked.unpredictable == m.unpredictable then 1 else 0) +
    (if evoked.comforting == m.comforting then 1 else 0)
  -- More feature matches → higher compatibility
  (matchCount : ℚ) / 3

/--
Extended semantics: combines literal meaning with feature compatibility.

If literally true: full compatibility (1)
If literally false: feature match score (0 to 1)
-/
def extendedSemantics (u : Utterance) (m : Meaning) : ℚ :=
  if literal u m.category then 1
  else featureMatch u m

-- ============================================================================
-- QUD Equivalence
-- ============================================================================

/-- QUD equivalence: when are two meanings "the same" for a given goal? -/
def qudEquiv : Goal → Meaning → Meaning → Bool
  | .category, m1, m2 => m1.category == m2.category
  | .dangerous, m1, m2 => m1.dangerous == m2.dangerous
  | .unpredictable, m1, m2 => m1.unpredictable == m2.unpredictable
  | .comforting, m1, m2 => m1.comforting == m2.comforting

-- ============================================================================
-- Meaning Space
-- ============================================================================

/--
Meanings in our domain: a person with various feature combinations.

We focus on "John" being described - the category is always person,
but the features vary. The speaker uses animal/object metaphors
to communicate John's features.
-/
def allMeanings : List Meaning :=
  -- Person with different feature profiles
  [ { category := .person, dangerous := false, unpredictable := false, comforting := false }
  , { category := .person, dangerous := true, unpredictable := false, comforting := false }
  , { category := .person, dangerous := false, unpredictable := true, comforting := false }
  , { category := .person, dangerous := false, unpredictable := false, comforting := true }
  , { category := .person, dangerous := true, unpredictable := true, comforting := false }
  , { category := .person, dangerous := true, unpredictable := false, comforting := true }
  , { category := .person, dangerous := false, unpredictable := true, comforting := true }
  , { category := .person, dangerous := true, unpredictable := true, comforting := true }
  ]

/-- All utterances -/
def allUtterances : List Utterance := [.person, .shark, .fire, .blanket]

/-- All goals -/
def allGoals : List Goal := [.category, .dangerous, .unpredictable, .comforting]

-- ============================================================================
-- Prior Over Meanings
-- ============================================================================

/--
Prior over meanings.

We use a uniform prior over feature combinations for a person.
In a richer model, this would come from world knowledge.
-/
def meaningPrior : Meaning → ℚ := fun _ => 1

-- ============================================================================
-- Prior Over Goals
-- ============================================================================

/--
Prior over QUDs/goals.

Feature QUDs are more common than category QUD in conversational contexts
where metaphor is used. (We already know it's a person.)
-/
def goalPrior : Goal → ℚ
  | .category => 1      -- Rarely just confirming category
  | .dangerous => 3     -- Often communicating danger
  | .unpredictable => 2 -- Sometimes unpredictability
  | .comforting => 2    -- Sometimes comfort

-- ============================================================================
-- RSA Scenario
-- ============================================================================

/--
Metaphor scenario with extended semantics.

Uses soft extended semantics that allows some compatibility between
metaphorical utterances and feature-matching meanings.
-/
def metaphorScenario : RSAScenario :=
  RSAScenario.qud
    allUtterances allMeanings allGoals
    extendedSemantics
    qudEquiv
    meaningPrior
    goalPrior

/--
Strict scenario with Boolean semantics.

Only literally true utterances are valid.
This shows the contrast - without soft semantics, metaphor can't work.
-/
def strictScenario : RSAScenario :=
  RSAScenario.qud
    allUtterances allMeanings allGoals
    (fun u m => boolToRat (meaningSemantics u m))
    qudEquiv
    meaningPrior

-- ============================================================================
-- Compute Distributions
-- ============================================================================

/-- A dangerous person -/
def dangerousPerson : Meaning :=
  { category := .person, dangerous := true, unpredictable := false, comforting := false }

/-- A dangerous and unpredictable person -/
def volatilePerson : Meaning :=
  { category := .person, dangerous := true, unpredictable := true, comforting := false }

/-- A comforting person -/
def comfortingPerson : Meaning :=
  { category := .person, dangerous := false, unpredictable := false, comforting := true }

/-- L0 for "shark" -/
def l0_shark : List (Meaning × ℚ) := RSA.L0 metaphorScenario Utterance.shark () () () Goal.dangerous

/-- S1 with dangerous person and QUD "dangerous" -/
def s1_dangerous_goal : List (Utterance × ℚ) :=
  RSA.S1 metaphorScenario dangerousPerson () () () Goal.dangerous

/-- S1 with dangerous person and QUD "category" -/
def s1_category_goal : List (Utterance × ℚ) :=
  RSA.S1 metaphorScenario dangerousPerson () () () Goal.category

/-- S1 with volatile person and QUD "dangerous" -/
def s1_volatile_dangerous : List (Utterance × ℚ) :=
  RSA.S1 metaphorScenario volatilePerson () () () Goal.dangerous

/-- S1 with comforting person and QUD "comforting" -/
def s1_comforting_goal : List (Utterance × ℚ) :=
  RSA.S1 metaphorScenario comfortingPerson () () () Goal.comforting

/-- L1 for "shark" -/
def l1_shark : List (Meaning × ℚ) := RSA.L1_world metaphorScenario Utterance.shark

/-- L1 goal distribution for "shark" -/
def l1_goal_shark : List (Goal × ℚ) := RSA.L1_goal metaphorScenario Utterance.shark

/-- L1 for "fire" -/
def l1_fire : List (Meaning × ℚ) := RSA.L1_world metaphorScenario Utterance.fire

/-- L1 for "blanket" -/
def l1_blanket : List (Meaning × ℚ) := RSA.L1_world metaphorScenario Utterance.blanket

-- ============================================================================
-- Evaluate
-- ============================================================================

#eval l0_shark
-- L0("shark"): soft compatibility with dangerous meanings

#eval s1_dangerous_goal
-- S1(dangerous person | QUD=dangerous): should prefer "shark"!

#eval s1_category_goal
-- S1(dangerous person | QUD=category): should prefer "person"

#eval s1_volatile_dangerous
-- S1(volatile person | QUD=dangerous): "fire" might be preferred

#eval s1_comforting_goal
-- S1(comforting person | QUD=comforting): should prefer "blanket"

#eval l1_shark
-- L1("shark"): should infer dangerous, category=person

#eval l1_goal_shark
-- L1_goal("shark"): should infer QUD was probably "dangerous"

#eval l1_fire
-- L1("fire"): should infer dangerous + unpredictable

#eval l1_blanket
-- L1("blanket"): should infer comforting

-- ============================================================================
-- Key Predictions
-- ============================================================================

/-- Get probability from a distribution -/
def getProb {α : Type} [BEq α] (dist : List (α × ℚ)) (x : α) : ℚ :=
  RSA.getScore dist x

/--
**Metaphor Prediction 1**: Under QUD "dangerous", S1 prefers "shark".

When the speaker cares about conveying danger (not category),
metaphorical utterances become optimal.
-/
def s1_shark_preferred_for_danger : Bool :=
  let dist := s1_dangerous_goal
  getProb dist Utterance.shark > getProb dist Utterance.person

#eval s1_shark_preferred_for_danger
-- Expected: true (metaphor emerges)

/--
**Metaphor Prediction 2**: Under QUD "category", S1 prefers "person".

When the speaker cares about literal category, they use the literal utterance.
-/
def s1_person_under_category : Bool :=
  let dist := s1_category_goal
  getProb dist Utterance.person > getProb dist Utterance.shark

#eval s1_person_under_category
-- Expected: true

/--
**Metaphor Prediction 3**: L1 hearing "shark" infers dangerous.

Despite the literal meaning being false, the pragmatic listener
correctly infers the speaker meant to convey danger.
-/
def l1_shark_infers_dangerous : Bool :=
  let dist := l1_shark
  -- P(dangerous=true | shark) > P(dangerous=false | shark)
  let pDangerous := allMeanings.filter (·.dangerous) |>.foldl
    (fun acc m => acc + getProb dist m) 0
  let pNotDangerous := allMeanings.filter (! ·.dangerous) |>.foldl
    (fun acc m => acc + getProb dist m) 0
  pDangerous > pNotDangerous

#eval l1_shark_infers_dangerous
-- Expected: true

/--
**Metaphor Prediction 4**: L1 infers speaker's QUD was probably a feature.

When hearing metaphor, the listener infers the speaker was probably
trying to communicate a feature, not literal category.
-/
def l1_infers_feature_qud : Bool :=
  let dist := l1_goal_shark
  let pFeature := getProb dist Goal.dangerous + getProb dist Goal.unpredictable +
                  getProb dist Goal.comforting
  let pCategory := getProb dist Goal.category
  pFeature > pCategory

#eval l1_infers_feature_qud
-- Expected: true

/--
**Metaphor Prediction 5**: "Fire" conveys both dangerous AND unpredictable.

"Fire" should evoke unpredictability more than "shark".
-/
def fire_more_unpredictable_than_shark : Bool :=
  let fireUnpred := allMeanings.filter (·.unpredictable) |>.foldl
    (fun acc m => acc + getProb l1_fire m) 0
  let sharkUnpred := allMeanings.filter (·.unpredictable) |>.foldl
    (fun acc m => acc + getProb l1_shark m) 0
  fireUnpred > sharkUnpred

#eval fire_more_unpredictable_than_shark
-- Expected: true

-- ============================================================================
-- Contrast with Strict Semantics
-- ============================================================================

/-- Under strict semantics, metaphor gets zero compatibility -/
def l0_shark_strict : List (Meaning × ℚ) := RSA.L0 strictScenario Utterance.shark () () () Goal.dangerous

#eval l0_shark_strict
-- All zeros for person meanings (shark is literally false)

/-- S1 under strict semantics can't use metaphor -/
def s1_strict_dangerous : List (Utterance × ℚ) :=
  RSA.S1 strictScenario dangerousPerson () () () Goal.dangerous

#eval s1_strict_dangerous
-- "shark" should have probability 0 (can only use "person")

-- ============================================================================
-- Connection to Kao et al. (2014) Hyperbole
-- ============================================================================

/-
## Structural Parallel: Metaphor vs Hyperbole

Both use the same QUD-RSA architecture:

| Component     | Hyperbole (PNAS)      | Metaphor (CogSci)           |
|---------------|----------------------|------------------------------|
| Meaning       | Price × Affect       | Category × Features          |
| QUDs          | price, affect, both  | category, dangerous, etc.    |
| Literal false | "million" for $500   | "shark" for person           |
| Communicates  | Affect despite price | Feature despite category     |

The shared insight: speakers can rationally choose literally false utterances
when optimizing for a QUD that projects away from the literally false dimension.

## Key Difference

- **Hyperbole**: Scalar exaggeration (more extreme value on same dimension)
- **Metaphor**: Cross-category mapping (different category with shared features)

Both emerge from the same pragmatic mechanism: QUD-sensitive optimization.
-/

-- ============================================================================
-- Summary
-- ============================================================================

/-
## How QUD-RSA Derives Metaphor

1. **Standard RSA** (without QUDs):
   - L0 assigns 0 probability to literally false utterances
   - S1 never chooses metaphorical utterances
   - Metaphor can't emerge

2. **QUD-RSA**:
   - S1 optimizes w.r.t. *projected* meaning under QUD
   - Under QUD "dangerous", meanings with same danger value are equivalent
   - "Shark" evokes danger → compatible with dangerous meanings
   - S1 can rationally choose "shark" to communicate "dangerous"

3. **L1 Inference**:
   - Listener marginalizes over possible QUDs
   - Hearing "shark" → infers speaker probably had "dangerous" QUD
   - Correctly recovers dangerous meaning despite literal falsity

## Key Modeling Choices

1. **Extended semantics**: Feature match score for category-feature compatibility

2. **Feature structure**: Multiple binary features (dangerous, unpredictable, comforting)

3. **QUD prior**: Biased toward feature QUDs, reflecting that
   feature communication is common in metaphor contexts

## Unified QUD-RSA Framework

This module, together with KaoEtAl2014.lean (hyperbole), demonstrates that
QUD-RSA provides a unified account of non-literal language:

- **Hyperbole**: QUD on affect allows literally false prices
- **Metaphor**: QUD on features allows literally false categories
- **Irony** (future work): QUD on speaker attitude allows opposite meanings

The Core/QUD.lean infrastructure supports all these applications.

## References

- Kao et al. (2014). A computational model of linguistic humor in puns. CogSci.
- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
- Roberts (2012). Information structure in discourse.
-/

end RSA.KaoEtAl2014_Metaphor
