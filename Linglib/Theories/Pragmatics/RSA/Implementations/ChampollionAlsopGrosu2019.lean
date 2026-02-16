/-
# Free Choice Disjunction as a Rational Speech Act

Formalization of Champollion, Alsop & Grosu (2019)
"Free choice disjunction as a rational speech act"
SALT 29: 238-257.

## The Key Innovation

Standard RSA cannot derive free choice because disjunction is always less
informative than its disjuncts. This paper solves the problem by adding
**semantic uncertainty** (Bergen et al. 2016): speakers and listeners reason
about which interpretation function (LF) is being used.

The two interpretation functions represent optional exhaustification (Fox 2007):
- I₁: Literal meanings (unexhaustified)
- I₂: Strengthened meanings (exhaustified)

## How Free Choice Emerges

1. Speaker wants to convey "Only One" (you may choose either fruit)
2. If speaker says "You may A", hearer might interpret via I₂ as "Only A"
3. To avoid this misunderstanding, speaker uses disjunction
4. Hearer reasons: "Speaker chose Or to prevent me thinking Only A or Only B"
5. Hearer infers: Only One or Any Number → Free choice!

## Results

- FCI is robust to prior manipulation (pure pragmatic reasoning)
- EI is prior-sensitive (world knowledge determines if "not both" is inferred)
- No FCI under negation (falls out automatically)

## References

- Champollion, Alsop & Grosu (2019). Free choice disjunction as RSA. SALT 29.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Franke (2011). Quantity implicatures, exhaustive interpretation.
-/

import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic
import Linglib.Phenomena.Modality.FreeChoice

namespace RSA.FreeChoice

open RSA.Eval
open LURSA

-- SECTION 1: States (Table 2 in the paper)

/-!
## State Space

The paper defines five states based on permission structure:

| State | ◇A | ◇B | ◇(A∨B) | ◇(A∧B) | FCI? | EI? |
|-------|----|----|--------|--------|------|-----|
| Only A | T | F | T | F | no | yes |
| Only B | F | T | T | F | no | yes |
| Only One | T | T | T | F | yes | yes |
| Any Number | T | T | T | T | yes | no |
| Only Both | T | T | T | T | no | no |

Note: "Only Both" means you may ONLY take both together (not either alone).
-/

/-- The five states from Champollion et al. (2019) Table 2 -/
inductive FCState where
  | onlyA : FCState      -- May take apple only (not pear)
  | onlyB : FCState      -- May take pear only (not apple)
  | onlyOne : FCState    -- May take either, but not both (FCI + EI)
  | anyNumber : FCState  -- May take any combination (FCI, no EI)
  | onlyBoth : FCState   -- May only take both together (no FCI, no EI)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Does free choice inference hold at this state? -/
def hasFCI : FCState → Bool
  | .onlyA => false
  | .onlyB => false
  | .onlyOne => true
  | .anyNumber => true
  | .onlyBoth => false

/-- Does exclusivity inference hold at this state? -/
def hasEI : FCState → Bool
  | .onlyA => true
  | .onlyB => true
  | .onlyOne => true
  | .anyNumber => false
  | .onlyBoth => false

/-- All states -/
def allStates : List FCState :=
  [.onlyA, .onlyB, .onlyOne, .anyNumber, .onlyBoth]

-- SECTION 2: Utterances

/-- The four utterances from the paper (5) -/
inductive Utterance where
  | a : Utterance    -- "You may take an apple"
  | b : Utterance    -- "You may take a pear"
  | or_ : Utterance  -- "You may take an apple or a pear"
  | and_ : Utterance -- "You may take an apple and a pear"
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All utterances -/
def allUtterances : List Utterance := [.a, .b, .or_, .and_]

-- SECTION 3: Interpretation Functions (6) and (7)

/-!
## Two Interpretation Functions

**I₁ (literal/unexhaustified)**: Standard modal logic meanings
- ⟦A⟧^I₁ = {Only A, Only One, Any Number, Only Both}
- ⟦B⟧^I₁ = {Only B, Only One, Any Number, Only Both}
- ⟦Or⟧^I₁ = all 5 states
- ⟦And⟧^I₁ = {Any Number, Only Both}

**I₂ (exhaustified)**: Strengthened via covert Exh (Fox 2007)
- ⟦A⟧^I₂ = {Only A}  (A ∧ ¬◇B)
- ⟦B⟧^I₂ = {Only B}  (B ∧ ¬◇A)
- ⟦Or⟧^I₂ = {Only A, Only B, Only One, Any Number}  (excludes Only Both)
- ⟦And⟧^I₂ = {Only Both}  (strengthened to "only both together")
-/

/-- Interpretation function I₁: literal/unexhaustified meanings -/
def I1 : Utterance → FCState → Bool
  | .a, .onlyA => true
  | .a, .onlyB => false
  | .a, .onlyOne => true
  | .a, .anyNumber => true
  | .a, .onlyBoth => true
  | .b, .onlyA => false
  | .b, .onlyB => true
  | .b, .onlyOne => true
  | .b, .anyNumber => true
  | .b, .onlyBoth => true
  | .or_, _ => true  -- True at all states
  | .and_, .onlyA => false
  | .and_, .onlyB => false
  | .and_, .onlyOne => false
  | .and_, .anyNumber => true
  | .and_, .onlyBoth => true

/-- Interpretation function I₂: exhaustified meanings -/
def I2 : Utterance → FCState → Bool
  | .a, .onlyA => true
  | .a, _ => false  -- Exhaustified: only onlyA
  | .b, .onlyB => true
  | .b, _ => false  -- Exhaustified: only onlyB
  | .or_, .onlyBoth => false  -- Excludes "only both" state
  | .or_, _ => true
  | .and_, .onlyBoth => true  -- Exhaustified: only onlyBoth
  | .and_, _ => false

/-- Create lexicon from interpretation function -/
def lexiconOf (interp : Utterance → FCState → Bool) : Lexicon Utterance FCState :=
  Lexicon.ofBool interp

/-- The two lexica -/
def lexicon1 : Lexicon Utterance FCState := lexiconOf I1
def lexicon2 : Lexicon Utterance FCState := lexiconOf I2

instance : BEq (Lexicon Utterance FCState) where
  beq l1 l2 := allUtterances.all λ u =>
    allStates.all λ w => l1.meaning u w == l2.meaning u w

-- SECTION 4: RSA Scenario

/-- Uniform prior over states -/
def uniformPrior : FCState → ℚ := λ _ => 1

/-- The free choice RSA scenario with lexical uncertainty -/
def fcScenario (α : ℕ := 100) (worldPrior : FCState → ℚ := uniformPrior) : LUScenario where
  Utterance := Utterance
  World := FCState
  baseLexicon := lexicon1
  lexica := [lexicon1, lexicon2]
  lexPrior := λ _ => 1  -- Uniform over interpretation functions
  worldPrior := worldPrior
  utterances := allUtterances
  worlds := allStates
  α := α

-- SECTION 5: Model Predictions (Tables 3-6)

/-!
## L0 Behavior (Tables 3 and 4)

L0 interprets literally given a specific interpretation function.

**L0 given I₁** (Table 3):
| | Only A | Only B | Only One | Any Number | Only Both |
|---|--------|--------|----------|------------|-----------|
| A | 0.25 | 0 | 0.25 | 0.25 | 0.25 |
| B | 0 | 0.25 | 0.25 | 0.25 | 0.25 |
| Or | 0.2 | 0.2 | 0.2 | 0.2 | 0.2 |
| And | 0 | 0 | 0 | 0.5 | 0.5 |

**L0 given I₂** (Table 4):
| | Only A | Only B | Only One | Any Number | Only Both |
|---|--------|--------|----------|------------|-----------|
| A | 1 | 0 | 0 | 0 | 0 |
| B | 0 | 1 | 0 | 0 | 0 |
| Or | 0.25 | 0.25 | 0.25 | 0.25 | 0 |
| And | 0 | 0 | 0 | 0 | 1 |
-/

#eval L0_given (fcScenario) lexicon1 .a
#eval L0_given (fcScenario) lexicon1 .or_
#eval L0_given (fcScenario) lexicon2 .a
#eval L0_given (fcScenario) lexicon2 .or_

/-!
## L1 Behavior (Table 5)

The key result: L1 derives free choice!

**L1 with uniform prior, α = 100** (Table 5):
| | Only A | Only B | Only One | Any Number | Only Both |
|---|--------|--------|----------|------------|-----------|
| A | 0.8 | 0 | 0.2 | 0 | 0 |
| B | 0 | 0.8 | 0.2 | 0 | 0 |
| **Or** | **0** | **0** | **0.5** | **0.5** | **0** |
| And | 0 | 0 | 0 | 0.33 | 0.67 |

The Or row shows **free choice**: all probability goes to FCI states!
-/

#eval L1 (fcScenario) .or_
#eval L1 (fcScenario) .a
#eval L1 (fcScenario) .and_

-- SECTION 6: Free Choice Derivation

/-- Get L1 probability for a state given an utterance -/
def l1Prob (u : Utterance) (w : FCState) (α : ℕ := 100) : ℚ :=
  getScore (L1 (fcScenario α) u) w

/-- Get L1 probability for FCI states (Only One + Any Number) -/
def l1FCIProb (u : Utterance) (α : ℕ := 100) : ℚ :=
  l1Prob u .onlyOne α + l1Prob u .anyNumber α

/-- Get L1 probability for non-FCI states (Only A + Only B + Only Both) -/
def l1NonFCIProb (u : Utterance) (α : ℕ := 100) : ℚ :=
  l1Prob u .onlyA α + l1Prob u .onlyB α + l1Prob u .onlyBoth α

#eval l1FCIProb .or_      -- Should be ~1.0
#eval l1NonFCIProb .or_   -- Should be ~0.0

/-- FCI derivation: L1 assigns essentially all probability to FCI states for Or -/
theorem fci_derived : l1FCIProb .or_ 100 > 99/100 := by native_decide

/-- Non-FCI states get essentially no probability for Or -/
theorem non_fci_suppressed : l1NonFCIProb .or_ 100 < 1/100 := by native_decide

-- SECTION 7: EI is Prior-Sensitive (Table 6)

/-!
## Exclusivity Inference Depends on Priors

Unlike FCI, the exclusivity inference (EI) is sensitive to world priors.

**Asymmetric prior** (75% on Any Number):
| | Only A | Only B | Only One | Any Number | Only Both |
|---|--------|--------|----------|------------|-----------|
| Or | 0 | 0 | 0.08 | **0.92** | 0 |

With this prior, EI is weak (92% goes to non-EI state Any Number).
But FCI still holds (0% on non-FCI states Only A, Only B, Only Both).
-/

/-- Prior that favors Any Number (no exclusivity) -/
def anyNumberPrior : FCState → ℚ
  | .anyNumber => 75
  | _ => 625/100  -- 6.25 each for the other 4 states

/-- Scenario with prior favoring Any Number -/
def fcScenarioAnyNumber := fcScenario 100 anyNumberPrior

#eval L1 fcScenarioAnyNumber .or_

/-- With any-number prior, EI is weak (most probability on non-EI state) -/
def l1EIProb_anyNumber : ℚ :=
  getScore (L1 fcScenarioAnyNumber .or_) .onlyOne

def l1NonEIProb_anyNumber : ℚ :=
  getScore (L1 fcScenarioAnyNumber .or_) .anyNumber

#eval l1EIProb_anyNumber     -- Should be low (~0.08)
#eval l1NonEIProb_anyNumber  -- Should be high (~0.92)

/-- EI is sensitive to priors: Any Number prior → weak EI -/
theorem ei_prior_sensitive : l1NonEIProb_anyNumber > 9/10 := by native_decide

/-- But FCI still holds even with the asymmetric prior -/
def l1FCIProb_anyNumber : ℚ :=
  getScore (L1 fcScenarioAnyNumber .or_) .onlyOne +
  getScore (L1 fcScenarioAnyNumber .or_) .anyNumber

theorem fci_robust_to_prior : l1FCIProb_anyNumber > 99/100 := by native_decide

-- SECTION 8: Explanation of the Mechanism

/-!
## Why Free Choice Emerges

The derivation works as follows:

### Step 1: S1's Dilemma

S1 wants to convey "Only One" (FCI + EI state).

**Option 1: Say "You may A"**
- If L0 uses I₁: L0 could infer Only A, Only One, Any Number, or Only Both
- If L0 uses I₂: L0 will infer Only A (100%)
- Risk: Hearer might think "Only A" (forbidding B)

**Option 2: Say "You may A or B"**
- If L0 uses I₁: L0 samples from all 5 states
- If L0 uses I₂: L0 samples from Only A, Only B, Only One, Any Number
- No risk of single-fruit interpretation

### Step 2: S1's Choice

S1 prefers "Or" because it avoids the risk of I₂ misinterpretation.

### Step 3: L1's Inference

L1 reasons: "S1 chose Or instead of A or B. Why?"
→ "To avoid me thinking Only A or Only B"
→ "Must be Only One or Any Number"
→ **Free Choice!**

### The Key Insight

The semantic uncertainty (I₁ vs I₂) creates an **avoidance pattern**:
- A and B are "risky" (might be interpreted as exclusive)
- Or is "safe" (always allows both options)

This asymmetry drives the free choice inference.
-/

-- SECTION 9: Connection to Phenomena Data

/-!
## Connection to Empirical Data

The model predicts the patterns in `Phenomena.FreeChoice.Data`:

1. **Free Choice Permission** (`coffeeOrTea`):
   - "You may have coffee or tea" → "You may have coffee AND you may have tea"
   - Derived: L1 assigns ~100% to FCI states

2. **Exclusivity Cancelability**:
   - EI ("not both") is sensitive to world knowledge
   - FCI is robust across priors

3. **Ross's Paradox** (`postOrBurn`):
   - "Post the letter" semantically entails "Post or burn"
   - But pragmatically, adding "or burn" triggers free choice
   - The asymmetry comes from the alternative structure
-/

/-- Free choice is predicted -/
theorem predicts_free_choice :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isPragmaticInference = true := rfl

/-- The inference is not semantic -/
theorem fc_not_semantic :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isSemanticEntailment = false := rfl

-- SECTION 10: Comparison with Other Approaches

/-!
## Comparison: Three Approaches to Free Choice

| Aspect | This paper | Bar-Lev & Fox 2020 | Fox 2007 |
|--------|------------|-------------------|----------|
| Framework | RSA + LU | Neo-Gricean Exh | Grammatical Exh |
| Mechanism | Semantic uncertainty | Innocent Inclusion | Recursive Exh |
| Nature | Probabilistic | Categorical | Categorical |
| FCI strength | Gradient | Categorical | Categorical |
| EI explanation | Prior-sensitive | Not addressed | Optional Exh |
| Negation | Automatic | Requires stipulation | Maximize Strength |

### Advantages of the RSA Approach

1. **Explains FCI/EI asymmetry**: FCI is pragmatic reasoning; EI is world knowledge
2. **Automatic negation handling**: RSA strengthens, so no FCI under negation
3. **Gradient predictions**: Can model experimental data on inference strength
4. **Unified mechanism**: Same framework handles scalar implicatures
-/

-- SECTION 11: Without Conjunction Alternative

/-!
## Robustness: Model Without "And" (Tables 7-8)

The model derives FCI even without the conjunction alternative.
This requires either:
- Removing the Only Both state, or
- Adding a null utterance

We implement the null utterance version (Table 8).
-/

/-- Utterances with null option -/
inductive UtteranceWithNull where
  | a : UtteranceWithNull
  | b : UtteranceWithNull
  | or_ : UtteranceWithNull
  | null : UtteranceWithNull  -- Saying nothing
  deriving DecidableEq, BEq, Repr, Inhabited

def allUtterancesWithNull : List UtteranceWithNull := [.a, .b, .or_, .null]

/-- I₁ with null (true everywhere) -/
def I1_null : UtteranceWithNull → FCState → Bool
  | .a, .onlyA => true
  | .a, .onlyB => false
  | .a, .onlyOne => true
  | .a, .anyNumber => true
  | .a, .onlyBoth => true
  | .b, .onlyA => false
  | .b, .onlyB => true
  | .b, .onlyOne => true
  | .b, .anyNumber => true
  | .b, .onlyBoth => true
  | .or_, _ => true
  | .null, _ => true  -- Null is always "true" (uninformative)

/-- I₂ with null -/
def I2_null : UtteranceWithNull → FCState → Bool
  | .a, .onlyA => true
  | .a, _ => false
  | .b, .onlyB => true
  | .b, _ => false
  | .or_, .onlyBoth => false
  | .or_, _ => true
  | .null, _ => true  -- Null remains uninformative

def lexiconNull1 : Lexicon UtteranceWithNull FCState := Lexicon.ofBool I1_null
def lexiconNull2 : Lexicon UtteranceWithNull FCState := Lexicon.ofBool I2_null

instance : BEq (Lexicon UtteranceWithNull FCState) where
  beq l1 l2 := allUtterancesWithNull.all λ u =>
    allStates.all λ w => l1.meaning u w == l2.meaning u w

/-- Scenario without And, with null utterance -/
def fcScenarioNull : LUScenario where
  Utterance := UtteranceWithNull
  World := FCState
  baseLexicon := lexiconNull1
  lexica := [lexiconNull1, lexiconNull2]
  lexPrior := λ _ => 1
  worldPrior := λ _ => 1
  utterances := allUtterancesWithNull
  worlds := allStates
  α := 100

#eval L1 fcScenarioNull .or_
#eval L1 fcScenarioNull .null

/-- FCI still holds without And (Table 8) -/
def l1FCIProb_null : ℚ :=
  getScore (L1 fcScenarioNull .or_) .onlyOne +
  getScore (L1 fcScenarioNull .or_) .anyNumber

theorem fci_without_and : l1FCIProb_null > 99/100 := by native_decide

/-- Only Both is conveyed by null utterance -/
def l1OnlyBoth_null : ℚ :=
  getScore (L1 fcScenarioNull .null) .onlyBoth

#eval l1OnlyBoth_null  -- Should be 1.0

-- Summary

/-!
## Summary

### Definitions
- `FCState`: The 5 states (Only A, Only B, Only One, Any Number, Only Both)
- `Utterance`: The 4 utterances (A, B, Or, And)
- `I1`, `I2`: Two interpretation functions (literal vs exhaustified)
- `fcScenario`: The RSA scenario with lexical uncertainty

### Results
- `fci_derived`: L1 assigns >99% to FCI states for Or
- `fci_robust_to_prior`: FCI holds even with asymmetric priors
- `ei_prior_sensitive`: EI is cancelable via world knowledge
- `fci_without_and`: FCI works without conjunction alternative

### Theoretical Contribution
The paper bridges grammatical (Fox 2007) and game-theoretic (Franke 2011)
approaches by using RSA with semantic uncertainty (Bergen et al. 2016).
The key insight is that LF ambiguity creates avoidance patterns that
drive pragmatic inference.

### References
- Champollion, Alsop & Grosu (2019). Free choice disjunction as RSA. SALT 29.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
- Fox (2007). Free choice and the theory of scalar implicatures.
-/

end RSA.FreeChoice
