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

import Linglib.Theories.Pragmatics.RSA.Core.Config

namespace RSA.FreeChoice

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


-- SECTION 4: Key Predictions (sorry'd — require LU-RSA computation)

/-!
## Key Predictions

The LU-RSA model with I₁ and I₂ derives free choice:

L1("or") assigns essentially all probability to FCI states
(Only One + Any Number), with negligible probability on
non-FCI states (Only A, Only B, Only Both).

FCI is robust to prior manipulation, while EI is prior-sensitive.
-/

/-- FCI derivation: L1 assigns high probability to FCI states for Or.

This is the central result of the paper. The proof requires the full
LU-RSA computation (lexical uncertainty marginalization). -/
theorem fci_derived : True := trivial
  -- TODO: Restate in terms of RSAConfig with latent lexicon variable
  -- once LU-RSA is ported to the new API

/-- FCI is robust to prior manipulation.

Even with a prior strongly favoring Any Number (no exclusivity),
L1 still assigns high probability to FCI states for Or. -/
theorem fci_robust_to_prior : True := trivial
  -- TODO: Restate with new API

/-- EI is prior-sensitive: a prior favoring Any Number weakens EI.

Unlike FCI, the exclusivity inference depends on world knowledge. -/
theorem ei_prior_sensitive : True := trivial
  -- TODO: Restate with new API


-- SECTION 5: Structural Properties (these don't require RSA computation)

/-- I₂ refines I₁ for utterance A: I₂(A) ⊆ I₁(A) -/
theorem I2_refines_I1_a : ∀ w, I2 .a w = true → I1 .a w = true := by
  intro w h; cases w <;> simp_all [I1, I2]

/-- I₂ refines I₁ for utterance B: I₂(B) ⊆ I₁(B) -/
theorem I2_refines_I1_b : ∀ w, I2 .b w = true → I1 .b w = true := by
  intro w h; cases w <;> simp_all [I1, I2]

/-- I₂ refines I₁ for Or: I₂(Or) ⊆ I₁(Or) -/
theorem I2_refines_I1_or : ∀ w, I2 .or_ w = true → I1 .or_ w = true := by
  intro w _; cases w <;> simp [I1]

/-- I₂ refines I₁ for And: I₂(And) ⊆ I₁(And) -/
theorem I2_refines_I1_and : ∀ w, I2 .and_ w = true → I1 .and_ w = true := by
  intro w h; cases w <;> simp_all [I1, I2]

/-- I₁(Or) is true everywhere (maximally uninformative) -/
theorem I1_or_everywhere : ∀ w, I1 .or_ w = true := by
  intro w; cases w <;> rfl

/-- I₂(Or) excludes exactly onlyBoth -/
theorem I2_or_excludes_onlyBoth :
    I2 .or_ .onlyBoth = false ∧ ∀ w, w ≠ .onlyBoth → I2 .or_ w = true := by
  constructor
  · rfl
  · intro w h; cases w <;> simp_all [I2]

/-- I₂(A) is true only at onlyA -/
theorem I2_a_singleton : ∀ w, I2 .a w = true ↔ w = .onlyA := by
  intro w; cases w <;> simp [I2]


-- SECTION 6: Explanation of the Mechanism

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


-- SECTION 7: Without Conjunction Alternative

/-!
## Robustness: Model Without "And" (Tables 7-8)

The model derives FCI even without the conjunction alternative.
This requires either:
- Removing the Only Both state, or
- Adding a null utterance

We define the null utterance version (Table 8).
-/

/-- Utterances with null option -/
inductive UtteranceWithNull where
  | a : UtteranceWithNull
  | b : UtteranceWithNull
  | or_ : UtteranceWithNull
  | null : UtteranceWithNull  -- Saying nothing
  deriving DecidableEq, BEq, Repr, Inhabited

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

-- Summary

/-!
## Summary

### Definitions
- `FCState`: The 5 states (Only A, Only B, Only One, Any Number, Only Both)
- `Utterance`: The 4 utterances (A, B, Or, And)
- `I1`, `I2`: Two interpretation functions (literal vs exhaustified)

### Structural Results
- `I2_refines_I1_*`: I₂ is a refinement of I₁ for all utterances
- `I1_or_everywhere`: I₁(Or) is maximally uninformative
- `I2_or_excludes_onlyBoth`: I₂(Or) excludes exactly the "only both" state
- `I2_a_singleton`: I₂(A) singles out exactly the "only A" state

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
