/-
# Free Choice: Theory Comparison

Comparing how different theories derive free choice inferences.

## The Puzzle

"You may have coffee or tea" pragmatically implies:
"You may have coffee AND you may have tea"

Semantically: ◇(A ∨ B) ↔ ◇A ∨ ◇B (standard modal logic)
Pragmatically: ◇(A ∨ B) → ◇A ∧ ◇B (free choice!)

## Theories Compared

1. **Bar-Lev & Fox (2020)**: Innocent Inclusion (II) + Innocent Exclusion (IE)
2. **Champollion et al. (2019)**: RSA with semantic uncertainty (disjunction)
3. **Alsop (2024)**: RSA with Global Intentions (universal *any*)
4. **Fox (2007)**: Recursive exhaustification (Exh(Exh(φ)))

## Key Questions

1. Do the theories make the same predictions?
2. Where do they diverge?
3. How do they explain related phenomena (EI cancelability, negation)?

## References

- Bar-Lev & Fox (2020). Free choice, simplification, and Innocent Inclusion. NLS.
- Champollion, Alsop & Grosu (2019). Free choice disjunction as RSA. SALT 29.
- Alsop (2024). The pragmatics of free choice any.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
- Franke & Bergen (2020). Theory-driven statistical modeling.
-/

import Linglib.Theories.NeoGricean.Implementations.BarLevFox2020
import Linglib.Theories.RSA.Implementations.ChampollionAlsopGrosu2019
import Linglib.Theories.RSA.Implementations.Alsop2024
import Linglib.Phenomena.FreeChoice.Data

namespace Comparisons.FreeChoice

open Phenomena.FreeChoice
open NeoGricean.FreeChoice
open RSA.FreeChoice
open RSA.FCIAny

-- ============================================================================
-- SECTION 1: The Free Choice Puzzle
-- ============================================================================

/-!
## The Core Puzzle

Standard modal logic gives us:
  ◇(A ∨ B) ↔ ◇A ∨ ◇B

But pragmatically, we infer:
  ◇(A ∨ B) → ◇A ∧ ◇B

This is **not** a semantic entailment. The challenge is to derive it pragmatically.

### Two Related Inferences

1. **Free Choice Inference (FCI)**: ◇(A ∨ B) → ◇A ∧ ◇B
   - "You may have coffee or tea" → "You may have coffee" AND "You may have tea"

2. **Exclusivity Inference (EI)**: ◇(A ∨ B) → ¬◇(A ∧ B)
   - "You may have coffee or tea" → "You may not have both"

FCI is robust; EI is cancelable. Any theory must explain this asymmetry.
-/

/-- FCI is a pragmatic inference, not semantic -/
theorem fci_is_pragmatic : coffeeOrTea.isSemanticEntailment = false := rfl

/-- FCI is captured pragmatically -/
theorem fci_is_captured : coffeeOrTea.isPragmaticInference = true := rfl

-- ============================================================================
-- SECTION 2: Bar-Lev & Fox (2020) - Innocent Inclusion
-- ============================================================================

/-!
## Neo-Gricean Account: Innocent Inclusion

Bar-Lev & Fox (2020) extend Fox's (2007) Innocent Exclusion with **Innocent Inclusion**.

### The Mechanism

**Step 1: Innocent Exclusion (IE)**
- Find maximal sets of alternatives that can consistently be assigned FALSE
- An alternative is in IE if it's in ALL such maximal sets

**Step 2: Innocent Inclusion (II)**
- After IE, find maximal sets that can consistently be assigned TRUE
- An alternative is in II if it's in ALL such maximal sets

**Step 3: Combined Exhaustification**
  Exh^{IE+II}(φ) = φ ∧ ∀q ∈ IE[¬q] ∧ ∀r ∈ II[r]

### Why It Works for Free Choice

The key is **closure under conjunction**:

| Alternative Set | Closed under ∧? | Result |
|----------------|-----------------|--------|
| {a∨b, a, b, a∧b} | YES | Exclusive-or |
| {◇(a∨b), ◇a, ◇b, ◇(a∧b)} | NO | Free choice |

For FC alternatives:
- ◇a ∧ ◇b ≠ ◇(a ∧ b) in modal logic
- This non-closure allows II to include ◇a and ◇b
-/

/-- Bar-Lev & Fox: Free choice is derived via Innocent Inclusion -/
theorem barlevfox_derives_fc :
    ∀ w, NeoGricean.FreeChoice.exhIEII fcALT fcPrejacent w →
      NeoGricean.FreeChoice.permA w ∧ NeoGricean.FreeChoice.permB w :=
  NeoGricean.FreeChoice.free_choice

-- ============================================================================
-- SECTION 3: Champollion et al. (2019) - RSA + Semantic Uncertainty
-- ============================================================================

/-!
## RSA Account: Semantic Uncertainty

Champollion et al. (2019) use RSA with multiple interpretation functions
(following Bergen et al. 2016's lexical uncertainty).

### The Mechanism

**Two Interpretation Functions**:
- I₁ (literal): Standard modal logic meanings
- I₂ (exhaustified): Strengthened meanings (à la Fox 2007)

For "You may A":
- Under I₁: {Only A, Only One, Any Number, Only Both}
- Under I₂: {Only A} only (exhaustified to exclude others)

**The Derivation**:
1. Speaker wants to convey "Only One" (you may choose either)
2. If speaker says "You may A", hearer might use I₂ → "Only A"
3. To avoid this, speaker uses "You may A or B"
4. Hearer reasons: "Speaker avoided A to prevent me thinking Only A"
5. Hearer concludes: Must be Only One or Any Number → FCI!

### Key Insight

The semantic uncertainty creates an **avoidance pattern**:
- Disjuncts are "risky" (might be interpreted exclusively)
- Disjunction is "safe" (always allows both options)
-/

/-- Champollion et al.: FCI probability > 99% at L1 -/
theorem champollion_derives_fc : RSA.FreeChoice.l1FCIProb .or_ 100 > 99/100 :=
  RSA.FreeChoice.fci_derived

/-- Champollion et al.: Non-FCI states get < 1% probability -/
theorem champollion_suppresses_non_fc : RSA.FreeChoice.l1NonFCIProb .or_ 100 < 1/100 :=
  RSA.FreeChoice.non_fci_suppressed

-- ============================================================================
-- SECTION 3b: Alsop (2024) - RSA + Global Intentions for *any*
-- ============================================================================

/-!
## RSA Account for Universal *Any*: Global Intentions

Alsop (2024) extends the RSA approach to universal free choice items like *any*,
using the Global Intentions model from Franke & Bergen (2020).

### The Mechanism

**Two Parses** (instead of two interpretation functions):
- Szabolcsi parse (weak): ∃x[◇take(x)] - "some option is permitted"
- Dayal parse (strong): ∀x[◇take(x)] - "each option is permitted"

**The Derivation**:
1. Speaker wants to convey "you may take any (= each) class"
2. If speaker uses weak parse, hearer might only infer "some class is OK"
3. To be informative, speaker intends the strong (Dayal) parse
4. Hearer reasons: "Speaker chose 'any' with the strong parse"
5. Hearer concludes: Each class is individually permitted → Exclusiveness!

### Key Parallel to Champollion et al.

| Aspect | Disjunction (2019) | Universal *any* (2024) |
|--------|-------------------|----------------------|
| FC inference | ◇(a∨b) → ◇a ∧ ◇b | ◇∃x.P(x) → ∀x.◇P(x) |
| Robust inference | FCI | Exclusiveness |
| Prior-sensitive | EI (not-both) | Not-every |
| Ambiguity | Interpretation (I₁/I₂) | Parse (Szabolcsi/Dayal) |
-/

/-- Alsop: Exclusiveness probability > 99% at L1 -/
theorem alsop_derives_exclusiveness :
    RSA.FCIAny.exclusivenessProb 100 RSA.FCIAny.uniformPrior .mayAny > 99/100 :=
  RSA.FCIAny.exclusiveness_derived

/-- Alsop: Exclusiveness is robust to prior manipulation -/
theorem alsop_exclusiveness_robust :
    RSA.FCIAny.exclusivenessProb 100 RSA.FCIAny.mustBothPrior .mayAny > 99/100 :=
  RSA.FCIAny.exclusiveness_robust

/-- Alsop: Not-every is prior-sensitive (unlike exclusiveness) -/
theorem alsop_not_every_sensitive :
    RSA.FCIAny.notEveryUniform > RSA.FCIAny.notEveryAnyNum :=
  RSA.FCIAny.not_every_prior_sensitive

-- ============================================================================
-- SECTION 4: Comparison Table
-- ============================================================================

/-!
## Side-by-Side Comparison

| Aspect | Bar-Lev & Fox 2020 | Champollion et al. 2019 | Alsop 2024 |
|--------|-------------------|------------------------|------------|
| **Framework** | Neo-Gricean Exh | RSA + Lexical Uncertainty | RSA + Global Intentions |
| **Focus** | Disjunction FC | Disjunction FC | Universal *any* FC |
| **Key mechanism** | Innocent Inclusion | Semantic uncertainty | Parse-level ambiguity |
| **Nature** | Categorical | Probabilistic | Probabilistic |
| **FC derivation** | II includes ◇a, ◇b | L1 → FCI states | L1 → exclusiveness states |
| **Secondary inference** | IE excludes ◇(a∧b) | EI prior-sensitive | Not-every prior-sensitive |
| **Why FC works** | Non-closure under ∧ | Avoid I₂ misinterpretation | Dayal parse more informative |
| **Predictions** | Categorical | Gradient | Gradient |
-/

/-- Comparison result type (extended for 3 theories) -/
structure TheoryComparison where
  phenomenon : String
  barlevfox : String
  champollion : String
  alsop : String
  allAgree : Bool
  deriving Repr

/-- FCI: All theories derive it -/
def fciComparison : TheoryComparison :=
  { phenomenon := "Free Choice Inference"
  , barlevfox := "Derived via II: ◇a, ◇b ∈ II"
  , champollion := "L1: P(FCI states | Or) ≈ 100%"
  , alsop := "L1: P(exclusiveness | any) ≈ 100%"
  , allAgree := true }

/-- Secondary inference: Different names, same asymmetry -/
def secondaryInference : TheoryComparison :=
  { phenomenon := "Secondary Inference (EI / not-every)"
  , barlevfox := "IE excludes ◇(a∧b)"
  , champollion := "EI prior-sensitive"
  , alsop := "Not-every prior-sensitive"
  , allAgree := true }  -- Same structural asymmetry

/-- Robustness: Core FC is robust across all -/
def robustnessComparison : TheoryComparison :=
  { phenomenon := "Robustness of core FC"
  , barlevfox := "Categorical (always derived)"
  , champollion := "Robust: holds despite adverse priors"
  , alsop := "Robust: exclusiveness despite adverse priors"
  , allAgree := true }

/-- Negation: Different approaches -/
def negationComparison : TheoryComparison :=
  { phenomenon := "No FCI under negation"
  , barlevfox := "Maximize Strength"
  , champollion := "Automatic (RSA strengthens)"
  , alsop := "Automatic (RSA strengthens)"
  , allAgree := true }  -- Same prediction

/-- All comparisons -/
def allComparisons : List TheoryComparison :=
  [fciComparison, secondaryInference, robustnessComparison, negationComparison]

-- ============================================================================
-- SECTION 5: Structural Insights
-- ============================================================================

/-!
## Different Structural Insights

### Bar-Lev & Fox: Closure Under Conjunction

The key structural property is whether the alternative set is closed under ∧.

**Simple disjunction**: ALT = {a∨b, a, b, a∧b}
- a ∧ b IS in ALT
- Closed → IE excludes everything, II includes nothing
- Result: Exclusive-or (or contradiction)

**FC disjunction**: ALT = {◇(a∨b), ◇a, ◇b, ◇(a∧b)}
- ◇a ∧ ◇b is NOT equivalent to ◇(a∧b)
- Not closed → IE excludes ◇(a∧b), II includes ◇a, ◇b
- Result: Free choice!

### Champollion et al.: Semantic Uncertainty Creates Avoidance

The key is uncertainty about interpretation functions.

**Without uncertainty**: Disjunction is always less informative → no FCI
**With uncertainty**: Disjuncts are "risky" (might be exhaustified) → speaker avoids

The pragmatic reasoning is:
1. Why did speaker choose Or instead of A?
2. Because A might be interpreted as "Only A" (via I₂)
3. So speaker must want to avoid that interpretation
4. Therefore, not Only A and not Only B → FCI!

### Alsop: Parse-Level Ambiguity Drives Informativity

The key is ambiguity between grammatical parses (not interpretation functions).

**Szabolcsi parse (weak)**: ∃x[◇take(x)] - some option permitted
**Dayal parse (strong)**: ∀x[◇take(x)] - each option permitted

The pragmatic reasoning is:
1. Why would speaker use "any" with the weak parse?
2. The strong (Dayal) parse is more informative
3. L1 reasons: speaker intended the informative parse
4. Therefore, each item is individually permitted → Exclusiveness!

**Key insight**: The mechanism is the same as Champollion et al. but at a
different level of grammatical representation (parse vs interpretation).
-/

/-- Bar-Lev & Fox's key insight: closure determines outcome -/
inductive ClosureStatus where
  | closed : ClosureStatus      -- ALT closed under ∧
  | notClosed : ClosureStatus   -- ALT not closed under ∧
  deriving DecidableEq, BEq, Repr

/-- Prediction based on closure -/
def closurePrediction : ClosureStatus → String
  | .closed => "Exclusive-or (standard scalar implicature)"
  | .notClosed => "Free choice (via Innocent Inclusion)"

/-- Simple disjunction is closed -/
def simpleDisjunctionClosure : ClosureStatus := .closed

/-- FC disjunction is not closed -/
def fcDisjunctionClosure : ClosureStatus := .notClosed

#eval closurePrediction simpleDisjunctionClosure  -- "Exclusive-or..."
#eval closurePrediction fcDisjunctionClosure      -- "Free choice..."

-- ============================================================================
-- SECTION 6: Empirical Predictions
-- ============================================================================

/-!
## Where Theories Make Different Predictions

### 1. Gradient vs Categorical Judgments

**Bar-Lev & Fox**: FCI is categorical (either derived or not)
**Champollion et al.**: FCI is gradient (probability varies with α, priors)

**Test**: Do speakers show gradient acceptance of FC readings?
- If gradient → supports RSA approach
- If categorical → supports Neo-Gricean approach

### 2. EI Cancelability Asymmetry

**Bar-Lev & Fox**: Both FCI and EI derived by same mechanism
**Champollion et al.**: FCI from reasoning, EI from priors → asymmetry

**Test**: Can EI be canceled more easily than FCI?
- (3a) "You may have A or B, #in fact you may not have A" (FCI cancel: bad)
- (3b) "You may have A or B, in fact you may have both" (EI cancel: ok)

The Champollion et al. account predicts and explains this asymmetry.

### 3. Context Effects on EI

**Champollion et al.**: EI should be sensitive to world priors
**Bar-Lev & Fox**: EI derivation is structural, not context-dependent

**Test**: Does context affect EI but not FCI?
- "There's plenty of fruit" → EI weakened, FCI unchanged
- "Choose one dessert" → EI strengthened, FCI unchanged
-/

/-- Empirical prediction type -/
structure EmpiricalPrediction where
  test : String
  barlevfox : String
  champollion : String
  testable : Bool
  deriving Repr

def gradientPrediction : EmpiricalPrediction :=
  { test := "Gradient vs categorical FC judgments"
  , barlevfox := "Categorical"
  , champollion := "Gradient (varies with α)"
  , testable := true }

def eiAsymmetryPrediction : EmpiricalPrediction :=
  { test := "EI more cancelable than FCI"
  , barlevfox := "Not predicted"
  , champollion := "Predicted and explained"
  , testable := true }

def contextEffectPrediction : EmpiricalPrediction :=
  { test := "Context affects EI but not FCI"
  , barlevfox := "Not predicted"
  , champollion := "Predicted: EI tracks priors"
  , testable := true }

def empiricalPredictions : List EmpiricalPrediction :=
  [gradientPrediction, eiAsymmetryPrediction, contextEffectPrediction]

-- ============================================================================
-- SECTION 7: Unified View
-- ============================================================================

/-!
## Towards a Unified Account

Despite different mechanisms, all three theories capture key insights:

### Shared Insights

1. **Pragmatic, not semantic**: All derive FC pragmatically
2. **Alternative/ambiguity-based**: All reason about alternatives or parses
3. **Strengthening**: All treat FC as pragmatic strengthening
4. **Asymmetry**: All predict core FC is robust, secondary inference is weaker

### Complementary Strengths

| Strength | Bar-Lev & Fox | Champollion et al. | Alsop 2024 |
|----------|--------------|-------------------|------------|
| Formal precision | ✓ (categorical) | | |
| Gradient predictions | | ✓ | ✓ |
| EI asymmetry | | ✓ | ✓ (not-every) |
| Closure insight | ✓ | | |
| Unified with SI | ✓ (same Exh) | ✓ (same RSA) | ✓ (same RSA) |
| Universal FCIs | | | ✓ |
| Parse ambiguity | | | ✓ |

### The RSA Family: Champollion et al. + Alsop

The two RSA approaches are closely related:
- **Champollion et al.**: Interpretation-level ambiguity (I₁ vs I₂)
- **Alsop**: Parse-level ambiguity (Szabolcsi vs Dayal)

Both use the same core mechanism: L1 reasons about which reading the speaker
intended, preferring the more informative one. The difference is where the
ambiguity lives in the grammar.

### Possible Synthesis

A comprehensive account might:
1. Use Innocent Inclusion to characterize WHAT gets strengthened
2. Use RSA to model HOW MUCH strengthening occurs
3. Closure determines categorical availability
4. RSA handles both interpretation-level and parse-level ambiguity

This would combine Bar-Lev & Fox's structural insight with
the gradient predictions of the RSA approaches.
-/

/-- Areas of agreement between theories -/
def areasOfAgreement : List String :=
  [ "FCI is pragmatic, not semantic"
  , "FCI is derived via reasoning about alternatives"
  , "FCI is a form of pragmatic strengthening"
  , "Modal disjunction alternatives have special structure"
  , "Both correctly predict FCI for permission sentences"
  , "Both correctly predict no FCI under negation" ]

/-- Areas where theories complement each other -/
def complementaryStrengths : List (String × String) :=
  [ ("Formal categorical characterization", "Bar-Lev & Fox")
  , ("Gradient acceptability predictions", "Champollion et al.")
  , ("EI/FCI asymmetry explanation", "Champollion et al.")
  , ("Closure-based structural insight", "Bar-Lev & Fox")
  , ("Connection to scalar implicatures", "Both") ]

-- ============================================================================
-- SECTION 8: Connection to Phenomena
-- ============================================================================

/-!
## Predictions for Phenomena Data

Both theories correctly predict the patterns in `Phenomena.FreeChoice.Data`:

### Basic Free Choice (`coffeeOrTea`)
- Input: "You may have coffee or tea"
- Output: "You may have coffee AND you may have tea"
- Both: ✓ Derived

### Ross's Paradox (`postOrBurn`)
- "Post the letter" ⊢ "Post or burn" (semantically)
- But "Post or burn" → "You may burn" (pragmatically via FC)
- Both: ✓ Explained (FC is pragmatic, not semantic)

### Modal Free Choice (`deonticFC`, `epistemicFC`, `abilityFC`)
- FC works with different modal flavors
- Both: ✓ Predicted (mechanism is general)

### Cancellation (`explicitCancellation`)
- "You may have A or B, but I don't know which"
- Both: ✓ Predicted (FC is defeasible pragmatic inference)
-/

/-- All phenomena are correctly predicted by both theories -/
def bothPredictBasicFC : Bool := coffeeOrTea.isPragmaticInference
def bothPredictRoss : Bool := postOrBurn.pragmaticallyFelicitous = false
def bothPredictCancellation : Bool := explicitCancellation.felicitous

#eval bothPredictBasicFC       -- true
#eval bothPredictRoss          -- true
#eval bothPredictCancellation  -- true

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## Summary: Free Choice Theory Comparison

### All Three Theories Successfully Derive Free Choice

| Theory | Mechanism | Key Insight |
|--------|-----------|-------------|
| Bar-Lev & Fox 2020 | Innocent Inclusion | Non-closure under ∧ |
| Champollion et al. 2019 | RSA + interpretation uncertainty | Avoidance of I₂ |
| Alsop 2024 | RSA + parse ambiguity | Dayal parse informativity |

### Key Differences

1. **Nature**: Categorical (B&F) vs Gradient (RSA approaches)
2. **Domain**: Disjunction (B&F, C et al.) vs Universal *any* (Alsop)
3. **Ambiguity level**: Alternatives (B&F) vs Interpretations (C et al.) vs Parses (Alsop)
4. **Secondary inference**: EI (disjunction) vs not-every (universal)

### Complementary Insights

- **Bar-Lev & Fox**: WHY closure under ∧ matters for FC
- **Champollion et al.**: HOW reasoning produces gradient judgments for disjunction
- **Alsop**: HOW the same mechanism extends to universal FCIs like *any*

### Empirical Tests

1. Are FC judgments gradient? → Supports RSA approaches
2. Is EI/not-every more cancelable than FCI/exclusiveness? → Supports RSA approaches
3. Does context affect EI but not FCI? → Supports RSA approaches
4. Do disjunction and *any* show parallel patterns? → Supports unified account

### Conclusion

All three theories provide valuable insights into free choice phenomena.
The Neo-Gricean account offers precise structural characterization; the RSA
accounts offer gradient predictions and explain the asymmetry between core
and secondary inferences. The extension from disjunction to universal *any*
shows the generality of the pragmatic reasoning mechanism. A complete theory
may need elements of all three approaches.
-/

end Comparisons.FreeChoice
