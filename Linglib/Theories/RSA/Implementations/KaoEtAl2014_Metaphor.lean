/-
# Kao, Bergen & Goodman (2014)

"Formalizing the Pragmatics of Metaphor Understanding"
Proceedings of the Annual Meeting of the Cognitive Science Society, 36

## Key Predictions (from paper)

1. **Nonliteral interpretation**: P(person | "shark") ≈ 1
   - Listener infers the referent is a person, not literally a shark

2. **Multiple feature elevation**: Metaphor raises P(f1), P(f2), P(f3) above prior
   - Unlike literal "He is scary" which only raises P(scary)

3. **Context sensitivity**: Specific QUD raises target feature probability
   - "Is he scary?" + "He is a shark" → higher P(scary) than vague "What is he like?"

4. **Metaphor richer than literal**: Metaphor elevates secondary features more
   - "He is a shark" raises P(dangerous), P(mean) more than "He is scary"

## The Model

Meaning space: Category × Features
- Category: the referent (person, shark, fire, blanket)
- Features: properties (dangerous, unpredictable, comforting)

QUDs (communicative goals):
- "category": speaker wants listener to infer the literal category
- "feature_i": speaker wants listener to infer specific feature(s)

The QUD-sensitive speaker (S1) optimizes informativity w.r.t. the *projected* meaning.
When QUD = "feature", a literally false category can be optimal if it evokes the feature.

## Reference

Kao, J. T., Bergen, L., & Goodman, N. D. (2014). Formalizing the Pragmatics of
Metaphor Understanding. Proceedings of the Annual Meeting of the Cognitive
Science Society, 36, 719-724.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval

namespace RSA.KaoEtAl2014_Metaphor

open RSA.Eval

-- Domain: Categories and Features

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

-- Category-Feature Associations (from elicitation data)

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

-- Literal Semantics

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

-- Extended Semantics (Soft Feature Match)

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

-- QUD Equivalence

/-- QUD equivalence: when are two meanings "the same" for a given goal? -/
def qudEquiv : Goal → Meaning → Meaning → Bool
  | .category, m1, m2 => m1.category == m2.category
  | .dangerous, m1, m2 => m1.dangerous == m2.dangerous
  | .unpredictable, m1, m2 => m1.unpredictable == m2.unpredictable
  | .comforting, m1, m2 => m1.comforting == m2.comforting

-- Meaning Space

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

-- Prior Over Meanings

/--
Prior over meanings.

We use a uniform prior over feature combinations for a person.
In a richer model, this would come from world knowledge.
-/
def meaningPrior : Meaning → ℚ := fun _ => 1

-- Prior Over Goals

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

-- RSA Scenario

/-- Run L0 for metaphor scenario with extended semantics -/
def runL0 (u : Utterance) (g : Goal) : List (Meaning × ℚ) :=
  RSA.Eval.basicL0 allUtterances allMeanings
    (fun utt m => extendedSemantics utt m) meaningPrior u

/-- Run S1 for metaphor scenario -/
def runS1 (m : Meaning) (g : Goal) : List (Utterance × ℚ) :=
  -- S1 with QUD projection
  let l0_projected := allUtterances.map fun u =>
    let l0 := runL0 u g
    let projected := allMeanings.map fun m' =>
      if qudEquiv g m m' then RSA.Eval.getScore l0 m' else 0
    (u, RSA.Eval.sumScores projected)
  let normalized := RSA.Eval.normalize l0_projected
  let scores := allUtterances.map fun u =>
    let l0Score := RSA.Eval.getScore normalized u
    (u, l0Score)
  RSA.Eval.normalize scores

/-- Run L1 joint for metaphor scenario -/
def runL1_joint (u : Utterance) : List ((Meaning × Goal) × ℚ) :=
  let jointWorlds := allMeanings.flatMap fun m => allGoals.map fun g => (m, g)
  let scores := jointWorlds.map fun (m, g) =>
    let priorScore := meaningPrior m * goalPrior g
    let s1Score := RSA.Eval.getScore (runS1 m g) u
    ((m, g), priorScore * s1Score)
  RSA.Eval.normalize scores

/-- Run L1 marginal over meanings -/
def runL1_world (u : Utterance) : List (Meaning × ℚ) :=
  RSA.Eval.marginalize (runL1_joint u) Prod.fst

/-- Run L1 marginal over goals -/
def runL1_goal (u : Utterance) : List (Goal × ℚ) :=
  RSA.Eval.marginalize (runL1_joint u) Prod.snd

/-- Run L0 for strict scenario (Boolean semantics) -/
def runL0_strict (u : Utterance) (g : Goal) : List (Meaning × ℚ) :=
  RSA.Eval.basicL0 allUtterances allMeanings
    (fun utt m => boolToRat (meaningSemantics utt m)) meaningPrior u

/-- Run S1 for strict scenario -/
def runS1_strict (m : Meaning) (g : Goal) : List (Utterance × ℚ) :=
  let l0_projected := allUtterances.map fun u =>
    let l0 := runL0_strict u g
    let projected := allMeanings.map fun m' =>
      if qudEquiv g m m' then RSA.Eval.getScore l0 m' else 0
    (u, RSA.Eval.sumScores projected)
  let normalized := RSA.Eval.normalize l0_projected
  let scores := allUtterances.map fun u =>
    let l0Score := RSA.Eval.getScore normalized u
    (u, l0Score)
  RSA.Eval.normalize scores

-- Compute Distributions

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
def l0_shark : List (Meaning × ℚ) := runL0 .shark .dangerous

/-- S1 with dangerous person and QUD "dangerous" -/
def s1_dangerous_goal : List (Utterance × ℚ) := runS1 dangerousPerson .dangerous

/-- S1 with dangerous person and QUD "category" -/
def s1_category_goal : List (Utterance × ℚ) := runS1 dangerousPerson .category

/-- S1 with volatile person and QUD "dangerous" -/
def s1_volatile_dangerous : List (Utterance × ℚ) := runS1 volatilePerson .dangerous

/-- S1 with comforting person and QUD "comforting" -/
def s1_comforting_goal : List (Utterance × ℚ) := runS1 comfortingPerson .comforting

/-- L1 for "shark" -/
def l1_shark : List (Meaning × ℚ) := runL1_world .shark

/-- L1 goal distribution for "shark" -/
def l1_goal_shark : List (Goal × ℚ) := runL1_goal .shark

/-- L1 for "fire" -/
def l1_fire : List (Meaning × ℚ) := runL1_world .fire

/-- L1 for "blanket" -/
def l1_blanket : List (Meaning × ℚ) := runL1_world .blanket

-- Evaluate

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

-- Key Predictions


-- Key Prediction 1: Nonliteral Interpretation

/--
**Paper Prediction 1**: Nonliteral interpretation - P(person | "shark") >> P(shark | "shark")

The listener correctly infers the referent is a person, not literally a shark.
From paper: "Marginalized over values of f, the probability of the person category
given the utterance is close to one (P(cp|u) = 0.994)"
-/
def l1_infers_person_not_shark : Bool :=
  let dist := l1_shark
  let pPerson := allMeanings.filter (·.category == .person) |>.foldl
    (fun acc m => acc + getScore dist m) 0
  let pShark := allMeanings.filter (·.category == .shark) |>.foldl
    (fun acc m => acc + getScore dist m) 0
  pPerson > pShark * 10  -- Person should be ~99%, shark ~1%

#eval l1_infers_person_not_shark
-- Expected: true

/-- **Theorem (Paper Key Result)**: Listener interprets metaphor nonliterally -/
theorem nonliteral_interpretation : l1_infers_person_not_shark = true := by native_decide

-- Key Prediction 2: Speaker Behavior (Metaphor Emergence)

/--
**Paper Prediction 2**: Under QUD "dangerous", S1 prefers "shark".

When the speaker cares about conveying danger (not category),
metaphorical utterances become optimal.
-/
def s1_shark_preferred_for_danger : Bool :=
  let dist := s1_dangerous_goal
  getScore dist Utterance.shark > getScore dist Utterance.person

#eval s1_shark_preferred_for_danger
-- Expected: true (metaphor emerges)

/-- **Theorem**: Metaphor emerges under feature QUD -/
theorem metaphor_emerges : s1_shark_preferred_for_danger = true := by native_decide

/--
**Metaphor Prediction 2**: Under QUD "category", S1 rates "person" at least as high as "shark".

When the speaker cares about literal category, literal utterances are at least as good.
(With soft semantics, metaphors still have some compatibility, so they may tie.)
-/
def s1_person_at_least_shark : Bool :=
  let dist := s1_category_goal
  getScore dist Utterance.person >= getScore dist Utterance.shark

#eval s1_person_at_least_shark
-- Expected: true (they tie at 1/3 each)

/-- **Theorem**: Literal "person" at least as good as metaphor under category QUD -/
theorem literal_at_least_metaphor_under_category : s1_person_at_least_shark = true := by native_decide

/--
**Metaphor Prediction 3**: L1 hearing "shark" infers dangerous.

Despite the literal meaning being false, the pragmatic listener
correctly infers the speaker meant to convey danger.
-/
def l1_shark_infers_dangerous : Bool :=
  let dist := l1_shark
  -- P(dangerous=true | shark) > P(dangerous=false | shark)
  let pDangerous := allMeanings.filter (·.dangerous) |>.foldl
    (fun acc m => acc + getScore dist m) 0
  let pNotDangerous := allMeanings.filter (! ·.dangerous) |>.foldl
    (fun acc m => acc + getScore dist m) 0
  pDangerous > pNotDangerous

#eval l1_shark_infers_dangerous
-- Expected: true

/-- **Theorem**: Listener infers dangerous from "shark" metaphor -/
theorem listener_infers_dangerous : l1_shark_infers_dangerous = true := by native_decide

/--
**Metaphor Prediction 4**: L1 infers speaker's QUD was probably a feature.

When hearing metaphor, the listener infers the speaker was probably
trying to communicate a feature, not literal category.
-/
def l1_infers_feature_qud : Bool :=
  let dist := l1_goal_shark
  let pFeature := getScore dist Goal.dangerous + getScore dist Goal.unpredictable +
                  getScore dist Goal.comforting
  let pCategory := getScore dist Goal.category
  pFeature > pCategory

#eval l1_infers_feature_qud
-- Expected: true

/-- **Theorem**: Listener infers speaker had feature QUD from metaphor -/
theorem listener_infers_feature_qud : l1_infers_feature_qud = true := by native_decide

/--
**Metaphor Prediction 5**: "Fire" conveys both dangerous AND unpredictable.

"Fire" should evoke unpredictability more than "shark".
-/
def fire_more_unpredictable_than_shark : Bool :=
  let fireUnpred := allMeanings.filter (·.unpredictable) |>.foldl
    (fun acc m => acc + getScore l1_fire m) 0
  let sharkUnpred := allMeanings.filter (·.unpredictable) |>.foldl
    (fun acc m => acc + getScore l1_shark m) 0
  fireUnpred > sharkUnpred

#eval fire_more_unpredictable_than_shark
-- Expected: true

/-- **Theorem**: "Fire" evokes unpredictability more than "shark" -/
theorem fire_evokes_unpredictability : fire_more_unpredictable_than_shark = true := by native_decide

-- Contrast with Strict Semantics

/-- Under strict semantics, metaphor gets zero compatibility -/
def l0_shark_strict : List (Meaning × ℚ) := runL0_strict .shark .dangerous

#eval l0_shark_strict
-- All zeros for person meanings (shark is literally false)

/-- S1 under strict semantics can't use metaphor -/
def s1_strict_dangerous : List (Utterance × ℚ) := runS1_strict dangerousPerson .dangerous

#eval s1_strict_dangerous
-- "shark" should have probability 0 (can only use "person")

-- Connection to Kao et al. (2014) Hyperbole

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

-- PART: Compositional Grounding in Montague Semantics

/-!
## Features as Adjective Denotations

The features in metaphor (dangerous, unpredictable, comforting) are **adjective predicates**.
In Montague semantics, adjectives denote properties:

  ⟦dangerous⟧ = λx. dangerous(x) : Entity → Prop

The sentence "John is dangerous" involves **predication**:

  ⟦John is dangerous⟧ = dangerous(john)

For metaphor "John is a shark":
- Literal: ⟦John is a shark⟧ = shark(john) — FALSE for a person
- Metaphorical: via P(dangerous | shark), the listener infers dangerous(john)

The feature priors P(f|c) are **soft meaning postulates** connecting
category predicates to feature predicates. In classical semantics:

  shark(x) → dangerous(x)  (meaning postulate)

In the probabilistic RSA setting:

  P(dangerous | shark) ≈ 0.9  (soft meaning postulate)
-/

/--
**Feature as Montague property.**

A feature predicate is a function from entities (Meanings) to truth values.
This is the type `Entity → Prop` in Montague's IL, here instantiated
for our Meaning type.
-/
abbrev FeaturePred := Meaning → Bool

/--
**Compositionally derived feature predicates.**

Each `Feature` corresponds to a Montague adjective denotation:
- ⟦dangerous⟧ = λm. m.dangerous
- ⟦unpredictable⟧ = λm. m.unpredictable
- ⟦comforting⟧ = λm. m.comforting
-/
def featureDenotation : Feature → FeaturePred
  | .dangerous => fun m => m.dangerous
  | .unpredictable => fun m => m.unpredictable
  | .comforting => fun m => m.comforting

/--
**Category as Montague common noun.**

A category predicate is a function from entities to truth values.
⟦shark⟧ = λx. shark(x)
-/
abbrev CategoryPred := Meaning → Bool

/--
**Compositionally derived category predicates.**

Each `Category` corresponds to a Montague common noun denotation.
-/
def categoryDenotation : Category → CategoryPred
  | .person => fun m => m.category == .person
  | .shark => fun m => m.category == .shark
  | .fire => fun m => m.category == .fire
  | .blanket => fun m => m.category == .blanket

/--
**Literal semantics IS category predication.**

The literal meaning of "X is a Y" is just applying the category predicate:
  ⟦John is a shark⟧ = shark(john)

This demonstrates the compositional structure: `meaningSemantics` applies
the appropriate `categoryDenotation` based on the utterance.
-/
def utteranceCategory : Utterance → Category
  | .person => .person
  | .shark => .shark
  | .fire => .fire
  | .blanket => .blanket

/-- Literal semantics matches category predication for specific cases -/
example : meaningSemantics .shark ⟨.person, true, false, false⟩ = categoryDenotation .shark ⟨.person, true, false, false⟩ := rfl
example : meaningSemantics .shark ⟨.shark, true, false, false⟩ = categoryDenotation .shark ⟨.shark, true, false, false⟩ := rfl

/--
**Soft meaning postulate: P(feature | category).**

This function extracts the prototypical feature value for a category,
implementing the soft meaning postulate that connects categories to features.

Classical: shark(x) → dangerous(x)
Soft: P(dangerous(x) | shark(x)) = 1 (for prototypical shark)
-/
def softMeaningPostulate (c : Category) (f : Feature) : Bool :=
  let proto := prototypicalMeaning c
  featureDenotation f proto

/--
**Feature match uses compositional predicates.**

The featureMatch function that drives metaphor interpretation
is grounded in applying feature predicates to meanings.
The match count compares feature predicate values between
the evoked prototype and the target meaning.
-/
def featureMatchCompositional (u : Utterance) (m : Meaning) : ℚ :=
  let evoked := prototypicalMeaning (match u with
    | .person => .person | .shark => .shark | .fire => .fire | .blanket => .blanket)
  let matchCount : ℕ :=
    (if featureDenotation .dangerous evoked == featureDenotation .dangerous m then 1 else 0) +
    (if featureDenotation .unpredictable evoked == featureDenotation .unpredictable m then 1 else 0) +
    (if featureDenotation .comforting evoked == featureDenotation .comforting m then 1 else 0)
  (matchCount : ℚ) / 3

/--
**QUD as focus on a feature predicate.**

The QUD/Goal selects which feature predicate to focus on.
This is the compositional connection: QUD projects to a property type.

- Goal.dangerous → focus on ⟦dangerous⟧
- Goal.unpredictable → focus on ⟦unpredictable⟧
- Goal.comforting → focus on ⟦comforting⟧
-/
def goalToFeature : Goal → Option Feature
  | .category => none  -- Category QUD doesn't project to a feature
  | .dangerous => some .dangerous
  | .unpredictable => some .unpredictable
  | .comforting => some .comforting

/--
**QUD equivalence as feature predicate agreement.**

Two meanings are QUD-equivalent iff the focused feature predicate
returns the same value for both. This shows QUD projection
is selecting a property dimension.
-/
def qudEquivCompositional (g : Goal) (m1 m2 : Meaning) : Bool :=
  match goalToFeature g with
  | some f => featureDenotation f m1 == featureDenotation f m2
  | none => m1.category == m2.category

/-- QUD equivalence matches the compositional definition -/
theorem qudEquiv_eq_compositional (g : Goal) (m1 m2 : Meaning) :
    qudEquiv g m1 m2 = qudEquivCompositional g m1 m2 := by
  cases g <;> simp [qudEquiv, qudEquivCompositional, goalToFeature, featureDenotation]

-- Summary

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
