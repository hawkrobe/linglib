/-
# Continuous-Incremental RSA (CI-RSA)

Implements Waldon & Degen (2021) "Modeling cross-linguistic production of
referring expressions" (SCiL 2021).

## Overview

CI-RSA synthesizes two RSA extensions:
1. **Incremental RSA** (Cohn-Gordon et al. 2018): Word-by-word production
2. **Continuous semantics** (Degen et al. 2020): Noisy adjective reliability

## Key Equations

**Continuous lexical semantics** (v^i = reliability of item i):
  L^C(r, i) = v^i if i true of r, else 1 - v^i

**String interpretation** (average over continuations):
  X^C(c, i, r) = Σ_{u continues c+i} [[u]]^C(r) / |continuations|

**Incremental listener**:
  L0^INCR(r | c, i) ∝ X^C(c, i, r) · P(r)

**Incremental speaker**:
  S1^INCR(i | c, r) ∝ exp(α · (log L0^INCR(r | c, i) - C(i)))

**Full utterance** (chain rule):
  S1(u | r) = ∏_j S1^INCR(i_j | [i_1...i_{j-1}], r)

## Predictions

1. **Color/size asymmetry**: Redundant color > redundant size (English)
2. **Cross-linguistic**: English > Spanish-postnom. in redundant color
3. **Novel**: Spanish should flip (redundant size > redundant color)

## Connections

This implementation connects to the broader RSA ecosystem:

- **Continuous semantics**: Shares theoretical foundation with
  `RSA.ContinuousSemantics` (DegenEtAl2020.lean). Both use noisy adjective
  semantics where v^color > v^size, explaining redundant modification.

- **Noise theory**: The lexContinuous function instantiates the unified
  noise channel from `RSA.Core.Noise`. See `lexContinuous_as_noiseChannel`.

- **Reference games**: Uses the reference game infrastructure from
  `Linglib.Fragments.ReferenceGames`.

- **Word order**: Captures cross-linguistic variation in adjective ordering
  (prenominal English vs postnominal Spanish).

## References

- Waldon & Degen (2021). Modeling cross-linguistic production of referring
  expressions. SCiL 2021, pp. 206-215.
- Cohn-Gordon et al. (2018). An incremental iterated response model.
- Degen et al. (2020). When redundancy is useful. Psychological Review.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Noise
import Linglib.Fragments.ReferenceGames

namespace RSA.Implementations.WaldonDegen2021

-- ============================================================================
-- PART 1: Reference Game Setup
-- ============================================================================

/-- Features for reference game objects. -/
inductive Feature where
  | big | small | blue | red
  deriving DecidableEq, Repr, BEq

/-- A referent has size and color features. -/
structure Referent where
  size : Feature   -- big or small
  color : Feature  -- blue or red
  deriving DecidableEq, Repr, BEq

def bigBlue : Referent := ⟨.big, .blue⟩
def bigRed : Referent := ⟨.big, .red⟩
def smallBlue : Referent := ⟨.small, .blue⟩
def smallRed : Referent := ⟨.small, .red⟩

/-- Size-sufficient scene: {big_blue, big_red, small_blue}, target = small_blue -/
def ssScene : List Referent := [bigBlue, bigRed, smallBlue]

/-- Color-sufficient scene: {small_red, big_red, small_blue}, target = small_blue -/
def csScene : List Referent := [smallRed, bigRed, smallBlue]

-- ============================================================================
-- PART 2: Lexical Items and Utterances
-- ============================================================================

/-- Lexical items in referring expressions. -/
inductive LexItem where
  | blue | red | big | small | pin
  | start | stop  -- Boundary markers
  deriving DecidableEq, Repr, BEq

/-- An utterance is an ordered sequence of lexical items. -/
abbrev Utterance := List LexItem

/-- Check if lexical item is true of referent. -/
def itemTrueOf (i : LexItem) (r : Referent) : Bool :=
  match i with
  | .blue => r.color == .blue
  | .red => r.color == .red
  | .big => r.size == .big
  | .small => r.size == .small
  | .pin => true
  | .start | .stop => true

/-- Discrete utterance meaning: conjunction of item meanings. -/
def uttTrueOf (u : Utterance) (r : Referent) : Bool :=
  u.all (itemTrueOf · r)

-- ============================================================================
-- PART 3: Continuous Semantics (Degen et al. 2020)
-- ============================================================================

/-- Semantic reliability values v^i for lexical items.
    Color adjectives are more reliable than size adjectives. -/
def semanticValue (i : LexItem) : ℚ :=
  match i with
  | .blue | .red => 95/100      -- v^color = 0.95
  | .big | .small => 80/100     -- v^size = 0.8
  | .pin => 1                   -- Nouns fully reliable
  | .start | .stop => 1

/-- Continuous lexical interpretation L^C(r, i).
    Returns v^i if true, (1 - v^i) if false. -/
def lexContinuous (r : Referent) (i : LexItem) : ℚ :=
  let v := semanticValue i
  if itemTrueOf i r then v else 1 - v

/-- Continuous utterance meaning [[u]]^C(r) = ∏_{i∈u} L^C(r, i). -/
def uttContinuous (r : Referent) (u : Utterance) : ℚ :=
  u.foldl (fun acc i => acc * lexContinuous r i) 1

-- ============================================================================
-- Grounding: Connection to unified noise theory
-- ============================================================================

/-- lexContinuous is an instance of the unified noise channel.

This connects Waldon & Degen (2021) to the unified noise theory in
RSA.Core.Noise. The continuous lexical semantics L^C(r, i) is exactly
the noise channel with:
- onMatch = v^i (semantic value / reliability)
- onMismatch = 1 - v^i
- b = 1 if item i is true of referent r, 0 otherwise

Note: This uses the simplified Waldon & Degen parameterization where
mismatch = 1 - match, rather than the more general Degen et al. (2020)
formulation with independent match/mismatch parameters.
-/
theorem lexContinuous_as_noiseChannel (r : Referent) (i : LexItem) :
    lexContinuous r i =
    RSA.Noise.noiseChannel (semanticValue i) (1 - semanticValue i)
      (boolToRat (itemTrueOf i r)) := by
  simp only [lexContinuous, RSA.Noise.noiseChannel, boolToRat]
  split <;> ring

-- ============================================================================
-- PART 4: Language-Specific Grammars
-- ============================================================================

/-- Word order type for different languages. -/
inductive WordOrder where
  | prenominal      -- English: Adj Adj N
  | postnominal     -- Spanish-postnom: N Adj Adj
  deriving DecidableEq, Repr

/-- Generate all grammatical utterances for a language and scene. -/
def grammaticalUtterances (order : WordOrder) (scene : List Referent)
    (target : Referent) : List Utterance :=
  let singleAdj := match order with
    | .prenominal => [[LexItem.blue, LexItem.pin], [LexItem.red, LexItem.pin],
                      [LexItem.big, LexItem.pin], [LexItem.small, LexItem.pin]]
    | .postnominal => [[LexItem.pin, LexItem.blue], [LexItem.pin, LexItem.red],
                       [LexItem.pin, LexItem.big], [LexItem.pin, LexItem.small]]
  let doubleAdj := match order with
    | .prenominal =>
      -- English: size before color (small blue pin)
      [[LexItem.small, LexItem.blue, LexItem.pin],
       [LexItem.small, LexItem.red, LexItem.pin],
       [LexItem.big, LexItem.blue, LexItem.pin],
       [LexItem.big, LexItem.red, LexItem.pin]]
    | .postnominal =>
      -- Spanish-postnom: color before size (pin blue small)
      [[LexItem.pin, LexItem.blue, LexItem.small],
       [LexItem.pin, LexItem.blue, LexItem.big],
       [LexItem.pin, LexItem.red, LexItem.small],
       [LexItem.pin, LexItem.red, LexItem.big]]
  -- Filter to utterances true of target
  (singleAdj ++ doubleAdj).filter (uttTrueOf · target)

-- ============================================================================
-- PART 5: Incremental String Interpretation
-- ============================================================================

/-- Get all grammatical continuations of a partial utterance. -/
def continuations (partialUtt : Utterance) (order : WordOrder)
    (allUtts : List Utterance) : List Utterance :=
  allUtts.filter fun u => partialUtt.isPrefixOf u

/-- Incremental string interpretation X^C(c, i, r).
    Averages continuous semantics over all grammatical completions. -/
def stringInterpretation (context : Utterance) (nextWord : LexItem)
    (r : Referent) (order : WordOrder) (allUtts : List Utterance) : ℚ :=
  let partialUtt := context ++ [nextWord]
  let conts := continuations partialUtt order allUtts
  if conts.isEmpty then 0
  else
    let total := conts.foldl (fun acc u => acc + uttContinuous r u) 0
    total / conts.length

-- ============================================================================
-- PART 6: Incremental RSA (Cohn-Gordon et al. 2018)
-- ============================================================================

/-- Incremental literal listener L0^INCR(r | c, i).
    Proportional to string meaning times prior. -/
def l0Incremental (context : Utterance) (nextWord : LexItem)
    (scene : List Referent) (order : WordOrder) (allUtts : List Utterance)
    : List (Referent × ℚ) :=
  let scores := scene.map fun r =>
    (r, stringInterpretation context nextWord r order allUtts)
  let total := scores.foldl (fun acc (_, s) => acc + s) 0
  if total == 0 then scores.map fun (r, _) => (r, 0)
  else scores.map fun (r, s) => (r, s / total)

/-- Incremental speaker S1^INCR(i | c, r).
    Soft-maximizes utility of next word.

    Note: Uses rational approximation of softmax via power series. -/
def s1Incremental (context : Utterance) (target : Referent)
    (scene : List Referent) (order : WordOrder) (allUtts : List Utterance)
    (α : ℕ) (cost : LexItem → ℚ) : List (LexItem × ℚ) :=
  -- Get available next words
  let availableWords : List LexItem := match context with
    | [] => match order with
            | .prenominal => [LexItem.blue, LexItem.red, LexItem.big, LexItem.small]
            | .postnominal => [LexItem.pin]
    | _ =>
      let conts := continuations context order allUtts
      let nextWords := conts.filterMap fun u =>
        if context.length < u.length then u[context.length]? else none
      (nextWords ++ [LexItem.stop]).eraseDups
  -- Compute L0 probability for target for each word
  let scores : List (LexItem × ℚ) := availableWords.map fun w =>
    let l0dist := l0Incremental context w scene order allUtts
    let l0prob := match l0dist.find? (fun p => p.1 == target) with
      | some (_, prob) => prob
      | none => 0
    -- Utility ∝ (L0 prob)^α (simplified softmax without cost for now)
    let score := if l0prob > 0 then l0prob ^ α else 0
    (w, score)
  -- Normalize
  let total := scores.foldl (fun acc p => acc + p.2) 0
  if total == 0 then scores.map fun (w, _) => (w, 0)
  else scores.map fun (w, s) => (w, s / total)

-- ============================================================================
-- PART 7: Full Utterance Probability (Chain Rule)
-- ============================================================================

/-- Full utterance probability via chain rule.
    S1(u | r) = ∏_j S1^INCR(i_j | [i_1...i_{j-1}], r) -/
def utteranceProb (u : Utterance) (target : Referent)
    (scene : List Referent) (order : WordOrder) (allUtts : List Utterance)
    (α : ℕ) (cost : LexItem → ℚ) : ℚ :=
  let rec go (context : Utterance) (remaining : Utterance) (prob : ℚ) : ℚ :=
    match remaining with
    | [] => prob
    | w :: ws =>
      let dist := s1Incremental context target scene order allUtts α cost
      let wProb := match dist.find? (fun p => p.1 == w) with
        | some (_, prob) => prob
        | none => 0
      go (context ++ [w]) ws (prob * wProb)
  go [] u 1

-- ============================================================================
-- PART 8: Model Predictions
-- ============================================================================

/-- Default cost function: 0.1 per adjective. -/
def defaultCost (i : LexItem) : ℚ :=
  match i with
  | .blue | .red | .big | .small => 1/10
  | _ => 0

/-- Compute redundant modification probability. -/
def redundantModProb (order : WordOrder) (scene : List Referent)
    (target : Referent) (α : ℕ) : ℚ :=
  let allUtts := grammaticalUtterances order scene target
  -- The redundant utterance is "small blue pin" or its translation
  let redundantUtt := match order with
    | .prenominal => [LexItem.small, LexItem.blue, LexItem.pin]
    | .postnominal => [LexItem.pin, LexItem.blue, LexItem.small]
  utteranceProb redundantUtt target scene order allUtts α defaultCost

/-- **Main Prediction 1**: English color/size asymmetry.
    Redundant color in SS > Redundant size in CS. -/
def englishColorSizeAsymmetry (α : ℕ) : Bool :=
  let redundantColorSS := redundantModProb .prenominal ssScene smallBlue α
  let redundantSizeCS := redundantModProb .prenominal csScene smallBlue α
  redundantColorSS > redundantSizeCS

/-- **Main Prediction 2**: Cross-linguistic variation.
    English redundant color > Spanish-postnom redundant color. -/
def crossLinguisticVariation (α : ℕ) : Bool :=
  let englishColor := redundantModProb .prenominal ssScene smallBlue α
  let spanishColor := redundantModProb .postnominal ssScene smallBlue α
  englishColor > spanishColor

/-- **Novel Prediction**: Spanish flip.
    In Spanish-postnom, redundant size > redundant color. -/
def spanishFlipPrediction (α : ℕ) : Bool :=
  let spanishColorSS := redundantModProb .postnominal ssScene smallBlue α
  let spanishSizeCS := redundantModProb .postnominal csScene smallBlue α
  spanishSizeCS > spanishColorSS

-- ============================================================================
-- PART 9: Evaluation
-- ============================================================================

#eval grammaticalUtterances .prenominal ssScene smallBlue
#eval grammaticalUtterances .postnominal ssScene smallBlue

-- Note: Full evaluation requires implementing the exponential/log utilities
-- The structure above captures the model; full numerical predictions would
-- require more careful handling of rational arithmetic for exp/log.

end RSA.Implementations.WaldonDegen2021
