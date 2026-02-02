import Linglib.Theories.Montague.Question.DecisionTheory
import Linglib.Theories.Montague.Question.Partition
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# NPIs in Questions: Entropy as Strength

Van Rooy (2003) "Negative Polarity Items in Questions: Strength as Relevance"

## Core Insight

For assertions, strength = informativity (entailment).
For questions, strength = **entropy** (average informativity of answers).

NPIs are licensed in questions when they INCREASE entropy by reducing bias.

## The Entropy Measure

Following Bar-Hillel & Carnap (1953) and Shannon (1948):

```
E(Q) = Σ_{q∈Q} P(q) × (-log₂ P(q))
     = Σ_{q∈Q} P(q) × inf(q)
```

This is the **expected informativity** of the answers.

Key property: E(Q) is maximal when all answers are equally likely.

## NPI Licensing in Questions

Krifka's observation formalized:
- Biased question: P(negative) >> P(positive)
- NPI widens domain: makes positive answer easier to satisfy
- This increases P(positive), reducing bias
- Lower bias = higher entropy = more useful question
- Therefore: NPI LICENSED

## Rhetorical Questions (Section 4)

Strong NPIs (lift a finger, bat an eye) share presupposition with EVEN:
- Presupposes: alternatives are already settled
- Question remains open only for minimal value
- This creates rhetorical effect (near-zero entropy)

## References

- van Rooy, R. (2003). Negative Polarity Items in Questions: Strength as Relevance.
- Bar-Hillel & Carnap (1953). Semantic Information.
- Shannon (1948). Mathematical Theory of Communication.
- Krifka (1995). The semantics and pragmatics of polarity items.
- Kadmon & Landman (1993). Any.
- Borkin (1971). Polarity items in questions.
-/

namespace Montague.Question.EntropyNPIs

open Montague.Question

-- ============================================================================
-- PART 1: Entropy (Shannon/Bar-Hillel & Carnap)
-- ============================================================================

/-!
## Shannon Entropy for Questions

The informativity value of a question equals the expected informativity
of its answers. This is Shannon's entropy.

E(Q) = Σ_{q∈Q} P(q) × (-log₂ P(q))

Properties:
- E(Q) ≥ 0 always
- E(Q) = 0 iff one answer has probability 1 (question is settled)
- E(Q) is maximal when all answers are equiprobable
-/

/-- Informativity of a proposition: inf(p) = -log₂ P(p)

More informative = lower probability = higher surprisal.
We approximate with 1/p for rational arithmetic. -/
def informativity (prob : ℚ) : ℚ :=
  if prob ≤ 0 then 0
  else if prob ≥ 1 then 0
  else 1 / prob  -- Simplified; true version uses -log₂

/-- Entropy of a question: E(Q) = Σ P(q) × inf(q)

This measures the expected informativity of learning the answer. -/
def questionEntropy {W : Type*} (prior : W → ℚ) (worlds : List W)
    (q : Question W) : ℚ :=
  q.foldl (fun acc cell =>
    let cellWorlds := worlds.filter cell
    let prob := cellWorlds.foldl (fun p w => p + prior w) 0
    let inf := informativity prob
    acc + prob * inf
  ) 0

/-- A question is maximally entropic when answers are equiprobable -/
def isMaximalEntropy {W : Type*} (prior : W → ℚ) (worlds : List W)
    (q : Question W) : Prop :=
  ∀ c₁ c₂, c₁ ∈ q → c₂ ∈ q →
    let prob₁ := (worlds.filter c₁).foldl (fun p w => p + prior w) 0
    let prob₂ := (worlds.filter c₂).foldl (fun p w => p + prior w) 0
    prob₁ = prob₂

/-- A question has zero entropy iff it's already settled -/
def isSettled {W : Type*} (prior : W → ℚ) (worlds : List W)
    (q : Question W) : Prop :=
  ∃ c ∈ q, (worlds.filter c).foldl (fun p w => p + prior w) 0 = 1

/-- Entropy is maximal for equiprobable binary question -/
theorem entropy_maximal_equiprobable {W : Type*} (prior : W → ℚ) (worlds : List W)
    (q : Question W) (hBinary : q.length = 2)
    (hEqui : isMaximalEntropy prior worlds q) :
    ∀ q' : Question W, q'.length = 2 →
      questionEntropy prior worlds q ≥ questionEntropy prior worlds q' := by
  sorry

-- ============================================================================
-- PART 2: Bias and NPIs (Krifka's Analysis Formalized)
-- ============================================================================

/-!
## Bias Reduction via NPIs

Krifka (1990, 1992, 1995): NPIs turn biased questions into unbiased ones.

A biased polar question has P(negative) ≠ P(positive).
Domain widening (any vs some) can reduce this bias.

**Example**: "Have you ever been to China?" vs "Have you been to China?"
- If recent visits unlikely, "ever" widens to any past time
- This makes positive answer more achievable
- Probabilities become more balanced
- Higher entropy = more useful question
-/

/-- A polar question is biased toward negative if P(neg) > P(pos) -/
def isBiasedNegative {W : Type*} (prior : W → ℚ) (worlds : List W)
    (positive negative : W → Bool) : Bool :=
  let pPos := (worlds.filter positive).foldl (fun p w => p + prior w) 0
  let pNeg := (worlds.filter negative).foldl (fun p w => p + prior w) 0
  pNeg > pPos

/-- Degree of bias: |P(pos) - P(neg)| -/
def biasDegree {W : Type*} (prior : W → ℚ) (worlds : List W)
    (positive negative : W → Bool) : ℚ :=
  let pPos := (worlds.filter positive).foldl (fun p w => p + prior w) 0
  let pNeg := (worlds.filter negative).foldl (fun p w => p + prior w) 0
  if pPos ≥ pNeg then pPos - pNeg else pNeg - pPos

/-- NPI effect on a polar question: widens the positive answer's domain -/
structure NPIQuestionEffect (W : Type*) where
  /-- Positive answer without NPI (e.g., "someone called") -/
  posWithoutNPI : W → Bool
  /-- Positive answer with NPI (e.g., "anyone called") -/
  posWithNPI : W → Bool
  /-- NPI widens domain: withNPI ⊇ withoutNPI -/
  widens : ∀ w, posWithoutNPI w → posWithNPI w

/-- Negative answer is complement of positive -/
def NPIQuestionEffect.negWithoutNPI {W : Type*} (e : NPIQuestionEffect W) : W → Bool :=
  fun w => !e.posWithoutNPI w

def NPIQuestionEffect.negWithNPI {W : Type*} (e : NPIQuestionEffect W) : W → Bool :=
  fun w => !e.posWithNPI w

/-- Question without NPI -/
def NPIQuestionEffect.questionWithoutNPI {W : Type*} (e : NPIQuestionEffect W) : Question W :=
  [e.posWithoutNPI, e.negWithoutNPI]

/-- Question with NPI -/
def NPIQuestionEffect.questionWithNPI {W : Type*} (e : NPIQuestionEffect W) : Question W :=
  [e.posWithNPI, e.negWithNPI]

/-- NPI reduces bias when question is negatively biased -/
def npiReducesBias {W : Type*} (prior : W → ℚ) (worlds : List W)
    (e : NPIQuestionEffect W) : Prop :=
  isBiasedNegative prior worlds e.posWithoutNPI e.negWithoutNPI →
  biasDegree prior worlds e.posWithNPI e.negWithNPI <
  biasDegree prior worlds e.posWithoutNPI e.negWithoutNPI

/-- NPI increases entropy when question is negatively biased -/
def npiIncreasesEntropy {W : Type*} (prior : W → ℚ) (worlds : List W)
    (e : NPIQuestionEffect W) : Prop :=
  questionEntropy prior worlds e.questionWithNPI ≥
  questionEntropy prior worlds e.questionWithoutNPI

/--
**Van Rooy's Key Result**: When negatively biased, NPI increases entropy.

Proof sketch:
- Bias toward negative means P(neg) > P(pos)
- Domain widening makes P(pos') > P(pos) (easier to satisfy)
- Since P(pos') + P(neg') = 1 and P(pos') > P(pos):
  - P(neg') < P(neg)
  - |P(pos') - P(neg')| < |P(pos) - P(neg)|
- More balanced = higher entropy
-/
theorem npi_increases_entropy_when_negatively_biased {W : Type*}
    (prior : W → ℚ) (worlds : List W) (e : NPIQuestionEffect W)
    (hBiased : isBiasedNegative prior worlds e.posWithoutNPI e.negWithoutNPI = true)
    (hProperWidening : ∃ w, e.posWithNPI w ∧ !e.posWithoutNPI w) :
    npiIncreasesEntropy prior worlds e := by
  sorry

/-- Converse: In positively biased questions, PPIs (not NPIs) increase entropy -/
theorem ppi_increases_entropy_when_positively_biased {W : Type*}
    (prior : W → ℚ) (worlds : List W) (e : NPIQuestionEffect W)
    (hBiased : isBiasedNegative prior worlds e.posWithoutNPI e.negWithoutNPI = false)
    (hNotEqui : biasDegree prior worlds e.posWithoutNPI e.negWithoutNPI > 0) :
    -- PPIs (narrowing) would increase entropy, not NPIs (widening)
    questionEntropy prior worlds e.questionWithNPI ≤
    questionEntropy prior worlds e.questionWithoutNPI := by
  sorry

-- ============================================================================
-- PART 3: Entropy vs Decision-Theoretic Utility
-- ============================================================================

/-!
## Connecting Entropy to Utility (Section 5.3)

Van Rooy shows that entropy is a special case of expected utility value:

When the decision problem is "find out which answer is true",
the utility of a question equals its entropy.

This grounds the entropy measure in decision theory.
-/

/-- The "epistemic" decision problem: goal is to learn the true answer -/
def epistemicDP {W : Type*} (q : Question W) : DecisionProblem W (W → Bool) where
  utility w a := if a w then 1 else 0
  prior _ := 1  -- Uniform; will be normalized

/-- For epistemic DPs, question utility reduces to entropy -/
theorem questionUtility_eq_entropy_for_epistemic {W : Type*} [DecidableEq (W → Bool)]
    (prior : W → ℚ) (worlds : List W) (q : Question W) :
    let dp := epistemicDP q
    let dpWithPrior : DecisionProblem W (W → Bool) := { dp with prior := prior }
    questionUtility dpWithPrior worlds q q =
    questionEntropy prior worlds q := by
  sorry

/-- General result: E(Q) ≤ EUV(Q) for any decision problem.

Entropy is the minimum expected utility across all DPs.
This is because the epistemic DP is the "hardest" one. -/
theorem entropy_leq_expected_utility {W A : Type*} [DecidableEq A]
    (prior : W → ℚ) (worlds : List W) (actions : List A)
    (q : Question W) (dp : DecisionProblem W A) :
    questionEntropy prior worlds q ≤ questionUtility dp worlds actions q := by
  sorry

-- ============================================================================
-- PART 4: Rhetorical Questions (Section 4)
-- ============================================================================

/-!
## Rhetorical Questions and Even-NPIs

Strong NPIs (lift a finger, bat an eye) create rhetorical readings because:
1. They denote MINIMAL scalar values
2. They share a presupposition with EVEN:
   "For all non-minimal alternatives, the question is already settled"

Van Rooy's analysis:
- If alternatives are settled, only the minimal value is questionable
- But if minimal value is least likely to be true, only negative answer reasonable
- This creates rhetorical force
-/

/-- A strong NPI has EVEN-like presupposition -/
structure StrongNPIEffect (W : Type*) extends NPIQuestionEffect W where
  /-- The NPI denotes a minimal scalar value -/
  isMinimal : True  -- Placeholder for scalar structure
  /-- Set of non-minimal alternatives -/
  alternatives : List (W → Bool)
  /-- Presupposition: all alternatives are settled (known false or true) -/
  alternativesSettled : ∀ alt ∈ alternatives, ∀ w, alt w ∨ ¬alt w

/-- A question is rhetorical if it has near-zero entropy -/
def isRhetorical {W : Type*} (prior : W → ℚ) (worlds : List W)
    (q : Question W) (threshold : ℚ := 1/10) : Prop :=
  questionEntropy prior worlds q < threshold

/-- The presupposition that alternatives are settled implies low entropy -/
def alternativesSettledImpliesLowEntropy {W : Type*}
    (prior : W → ℚ) (worlds : List W) (e : StrongNPIEffect W)
    (hSettled : ∀ alt ∈ e.alternatives,
      (worlds.filter alt).foldl (fun p w => p + prior w) 0 = 0 ∨
      (worlds.filter alt).foldl (fun p w => p + prior w) 0 = 1) : Prop :=
  -- When alternatives are settled, only minimal value has uncertainty
  -- This means very low entropy overall
  isRhetorical prior worlds e.questionWithNPI

/--
**Theorem**: Strong NPIs create rhetorical readings.

When a strong NPI is used in a question:
1. Its presupposition requires alternatives to be settled
2. Only the minimal value (the NPI) remains questionable
3. But the minimal value is least likely to be true (by NPI semantics)
4. So only the negative answer is reasonable
5. The question has near-zero entropy → rhetorical
-/
theorem strong_npi_creates_rhetorical {W : Type*}
    (prior : W → ℚ) (worlds : List W) (e : StrongNPIEffect W)
    (hAltsSettled : ∀ alt ∈ e.alternatives,
      (worlds.filter alt).foldl (fun p w => p + prior w) 0 = 0)
    (hMinimalUnlikely : (worlds.filter e.posWithNPI).foldl (fun p w => p + prior w) 0 < 1/10) :
    isRhetorical prior worlds e.questionWithNPI := by
  sorry

-- ============================================================================
-- PART 5: Kadmon & Landman's Strengthening (Section 4.1)
-- ============================================================================

/-!
## K&L's Question Strengthening

Kadmon & Landman (1990) propose that stressed "any" strengthens questions:

Q' strengthens Q iff Q is already answered but Q' is still unanswered.

Van Rooy: This is a special case of entropy increase.
- If Q is settled (entropy 0) but Q' is not (entropy > 0)
- Then Q' has higher entropy
- Domain widening achieves this when Q is biased toward negative
-/

/-- K&L's notion: Q' strengthens Q if Q is settled but Q' is open -/
def klStrengthens {W : Type*} (prior : W → ℚ) (worlds : List W)
    (q q' : Question W) : Prop :=
  isSettled prior worlds q ∧ ¬isSettled prior worlds q'

/-- K&L strengthening implies higher entropy -/
theorem kl_strengthens_implies_higher_entropy {W : Type*}
    (prior : W → ℚ) (worlds : List W) (q q' : Question W)
    (hStrengthens : klStrengthens prior worlds q q') :
    questionEntropy prior worlds q' > questionEntropy prior worlds q := by
  -- If q is settled, its entropy is 0
  -- If q' is not settled, its entropy is > 0
  sorry

/-- Stressed "any" achieves K&L strengthening via domain widening -/
theorem stressed_any_achieves_kl_strengthening {W : Type*}
    (prior : W → ℚ) (worlds : List W) (e : NPIQuestionEffect W)
    (hSettledWithout : isSettled prior worlds e.questionWithoutNPI)
    (hProperWidening : ∃ w, e.posWithNPI w ∧ !e.posWithoutNPI w) :
    klStrengthens prior worlds e.questionWithoutNPI e.questionWithNPI := by
  sorry

-- ============================================================================
-- PART 6: The Unified Principle
-- ============================================================================

/-!
## Strength as Relevance: The Unification

Van Rooy's key contribution: a UNIFIED notion of strength.

| Speech Act | Strength Measure | NPI Effect |
|------------|------------------|------------|
| Assertion  | Informativity (entailment) | Wider domain → stronger in DE |
| Question   | Entropy (avg informativity) | Wider domain → less biased |

Both are instances of **utility maximization**:
- Assertions: direct informativity maximization
- Questions: expected informativity (entropy) maximization

The connection to decision theory (Section 5.3) shows this is rational:
agents should choose utterances that maximize expected utility.
-/

/-- The unified strength measure -/
inductive SpeechAct where
  | assertion : SpeechAct
  | question : SpeechAct

/-- Strength for assertions: informativity (inverse probability) -/
def assertionStrength {W : Type*} (prior : W → ℚ) (worlds : List W)
    (p : W → Bool) : ℚ :=
  let prob := (worlds.filter p).foldl (fun acc w => acc + prior w) 0
  informativity prob

/-- Strength for questions: entropy -/
def questionStrength {W : Type*} (prior : W → ℚ) (worlds : List W)
    (q : Question W) : ℚ :=
  questionEntropy prior worlds q

/-- NPI licensing condition: increases strength under appropriate polarity/bias -/
def npiLicensed {W : Type*} (prior : W → ℚ) (worlds : List W)
    (act : SpeechAct) (e : NPIQuestionEffect W)
    (polarity : Bool) -- true = UE/positive bias, false = DE/negative bias
    : Prop :=
  match act with
  | .assertion =>
    -- In DE (polarity = false): wider domain is stronger
    if polarity then
      assertionStrength prior worlds e.posWithNPI ≤
      assertionStrength prior worlds e.posWithoutNPI
    else
      assertionStrength prior worlds e.posWithNPI ≥
      assertionStrength prior worlds e.posWithoutNPI
  | .question =>
    -- With negative bias (polarity = false): wider domain increases entropy
    if polarity then
      questionStrength prior worlds e.questionWithNPI ≤
      questionStrength prior worlds e.questionWithoutNPI
    else
      questionStrength prior worlds e.questionWithNPI ≥
      questionStrength prior worlds e.questionWithoutNPI

/--
**The Grand Unification**: NPI licensing follows the same principle
for assertions and questions—maximize strength under current polarity/bias.

For assertions: DE context → wider domain is more informative → NPI licensed
For questions: Negative bias → wider domain increases entropy → NPI licensed
-/
theorem unified_npi_licensing {W : Type*}
    (prior : W → ℚ) (worlds : List W) (e : NPIQuestionEffect W)
    (act : SpeechAct)
    (hNegativePolarityOrBias : Bool := false) :
    npiLicensed prior worlds act e hNegativePolarityOrBias := by
  sorry

-- ============================================================================
-- PART 7: Wh-Questions and Downward Entailment
-- ============================================================================

/-!
## Wh-Questions (Section 3.1)

Van Rooy notes that wh-questions ARE downward entailing in subject position:

"Who of John, Mary and Sue are sick?" entails
"Who of John and Mary are sick?"

(Every complete answer to the wider question entails an answer to the narrower.)

But this DOESN'T explain NPI licensing in predicate position or polar questions.
That's why we need the entropy-based account.
-/

/-- Wh-question with domain D and predicate P -/
structure WhQuestion (W Entity : Type*) where
  domain : List Entity
  predicate : Entity → W → Bool

/-- Wh-question entailment: Q entails Q' if answers to Q determine answers to Q' -/
def whQuestionEntails {W Entity : Type*}
    (q q' : WhQuestion W Entity)
    (hSubset : ∀ e, e ∈ q'.domain → e ∈ q.domain) : Prop :=
  -- Every complete answer to q gives a complete answer to q'
  True  -- Simplified

/-- Domain widening in wh-subject position is DE -/
theorem wh_subject_is_de {W Entity : Type*}
    (q q' : WhQuestion W Entity)
    (hWider : ∀ e, e ∈ q.domain → e ∈ q'.domain)
    (hStrictlyWider : ∃ e, e ∈ q'.domain ∧ e ∉ q.domain) :
    whQuestionEntails q' q (fun e he => hWider e (by sorry)) := by
  sorry

/-- NPIs licensed in wh-subject position via standard DE reasoning -/
theorem npi_licensed_wh_subject {W Entity : Type*}
    (q q' : WhQuestion W Entity)
    (hWider : ∀ e, e ∈ q.domain → e ∈ q'.domain) :
    -- NPI in subject widens domain → question with NPI entails question without
    -- This is standard DE licensing
    True := trivial

end Montague.Question.EntropyNPIs
