/-
# Kao, Bergen & Goodman (2014): Metaphor Understanding Data

Empirical data from "Formalizing the Pragmatics of Metaphor Understanding"
Proceedings of the Annual Meeting of the Cognitive Science Society, 36, 719-724.
-/

import Mathlib.Data.Rat.Defs

/-!
## Experimental Design

- 32 animal categories (shark, lion, ant, etc.)
- 3 features per category elicited from participants (Experiment 1a)
- Feature priors P(f|category) collected (Experiment 1b)
- Metaphor interpretation experiment (Experiment 2):
  - 2 conditions: Vague QUD ("What is he like?") vs Specific QUD ("Is he scary?")
  - 2 utterance types: Literal ("He is scary") vs Metaphorical ("He is a shark")
  - Participants rate P(f1), P(f2), P(f3) for the person described

## Key Empirical Findings

### 1. Metaphor conveys multiple features
Given metaphorical utterance, all three features elevated above prior:
- P(f1|metaphor) > P(f1|person_prior): t(63) = 15.74, p < 0.0001
- P(f2|metaphor) > P(f2|person_prior): t(63) = 7.29, p < 0.0001
- P(f3|metaphor) > P(f3|person_prior): t(63) = 5.91, p < 0.0001

### 2. Literal only conveys target feature
Given literal utterance "He is f1":
- P(f1|literal) > P(f1|person_prior): t(63) = 59.19, p < 0.00001
- P(f2|literal) ≈ P(f2|person_prior): t(63) = -0.13, p = 0.89 (n.s.)
- P(f3|literal) ≈ P(f3|person_prior): t(63) = 0.03, p = 0.97 (n.s.)

### 3. Context sensitivity for metaphor (not literal)
Metaphorical utterances:
- P(f1|metaphor, specific_QUD) > P(f1|metaphor, vague_QUD): F(1,62) = 10.16, p < 0.005

Literal utterances:
- P(f1|literal, specific_QUD) ≈ P(f1|literal, vague_QUD): F(1,62) = 2.73, p = 0.1 (n.s.)

### 4. Model fit
- Model-human correlation: r = 0.6, p < 0.001 (192 items)
- Correlation for f1 (most salient feature): r = 0.7, p < 0.0001
- Predicted reliability of human ratings: 0.828

## Reference

Kao, J. T., Bergen, L., & Goodman, N. D. (2014). Formalizing the Pragmatics of
Metaphor Understanding. Proceedings of the Annual Meeting of the Cognitive
Science Society, 36, 719-724.
-/

namespace Phenomena.Nonliteral.Metaphor.Studies.KaoBergenGoodman2014

-- Experimental Categories and Features (Table 1 from paper)

/-- Animal categories used in the experiment -/
inductive Animal where
  | ant | bat | bear | bee | bird | buffalo | cat | cow
  | dog | dolphin | duck | elephant | fish | fox | frog | goat
  | goose | horse | kangaroo | lion | monkey | owl | ox | penguin
  | pig | rabbit | shark | sheep | tiger | whale | wolf | zebra
  deriving DecidableEq, Repr, BEq

/-- Example feature sets (f1, f2, f3) for selected animals -/
structure AnimalFeatures where
  animal : Animal
  f1 : String  -- Most salient feature
  f2 : String  -- Second feature
  f3 : String  -- Third feature
  deriving Repr

/-- Sample of animal features from Table 1 -/
def sampleFeatures : List AnimalFeatures := [
  ⟨.shark, "scary", "dangerous", "mean"⟩,
  ⟨.lion, "ferocious", "scary", "strong"⟩,
  ⟨.ant, "small", "strong", "busy"⟩,
  ⟨.owl, "wise", "quiet", "nocturnal"⟩,
  ⟨.pig, "dirty", "fat", "smelly"⟩,
  ⟨.fox, "sly", "smart", "pretty"⟩,
  ⟨.dog, "loyal", "friendly", "happy"⟩,
  ⟨.wolf, "scary", "mean", "angry"⟩
]

-- Key Quantitative Findings

/-- Model-human correlation (r = 0.6) -/
def modelHumanCorrelation : ℚ := 60/100

/-- Correlation for f1 features (r = 0.7) -/
def f1Correlation : ℚ := 70/100

/-- Predicted reliability of human ratings -/
def humanReliability : ℚ := 828/1000

/-- Model's P(person | "shark") from paper -/
def modelPPersonGivenShark : ℚ := 994/1000

-- Key Qualitative Predictions (Theory-Derived)

/--
The paper identifies these key qualitative predictions:

1. **Nonliteral interpretation**: P(person|metaphor) >> P(animal|metaphor)
2. **Feature elevation**: P(fi|metaphor) > P(fi|prior) for all i
3. **Metaphor vs literal**: Metaphor elevates more features than literal
4. **Context sensitivity**: Specific QUD increases target feature probability
-/
inductive KeyPrediction where
  | nonliteralInterpretation  -- Listener infers person, not animal
  | multipleFeatureElevation  -- All features raised above prior
  | metaphorRicherThanLiteral -- Metaphor updates more dimensions
  | contextSensitivity        -- QUD affects interpretation
  deriving DecidableEq, Repr

/-- All key predictions from the paper -/
def keyPredictions : List KeyPrediction := [
  .nonliteralInterpretation,
  .multipleFeatureElevation,
  .metaphorRicherThanLiteral,
  .contextSensitivity
]

end Phenomena.Nonliteral.Metaphor.Studies.KaoBergenGoodman2014
