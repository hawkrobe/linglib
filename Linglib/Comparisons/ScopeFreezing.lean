/-
# Scope Freezing: Theory Comparison

Comparing how different theories explain scope freezing phenomena.

## Theories Compared

1. **Minimalism**: QR + Scope Economy + Locality constraints
2. **CCG**: Derivational ambiguity (scope = derivation structure)
3. **Processing**: Memory cost for inverse scope computation

## Key Questions

1. Do the theories make the same predictions?
2. Where do they diverge?
3. Is freezing categorical (grammar) or gradient (processing/pragmatics)?

## References

- Fox (2000). Economy and Scope.
- Steedman (2000). The Syntactic Process.
- Bruening (2001). QR obeys Superiority.
- Scontras et al. (2017). Scope ambiguity processing.
-/

import Linglib.Theories.Core.Interfaces.ScopeTheory
import Linglib.Phenomena.Quantification.ScopeFreezing
import Linglib.Theories.Minimalism.Phenomena.Scope
import Linglib.Theories.CCG.Phenomena.Scope

namespace Comparisons.ScopeFreezing

open ScopeTheory
open Phenomena.Quantification.ScopeFreezing
open Minimalism.Phenomena.Scope
open CCG.Scope

-- CCG Analysis of Freezing Contexts

/-!
## CCG Explanation of Scope Freezing

In CCG, scope ambiguity arises from derivational ambiguity:
- **Type-raising** allows arguments to take scope
- **Composition** allows non-canonical derivations
- When only ONE derivation exists → scope is frozen

### CCG Predictions

| Context | CCG Explanation |
|---------|----------------|
| Possessor | Complex DP has single derivation; possessor is pre-combined |
| Double object | Argument structure differs from PP dative; single derivation |
| Passive | By-phrase combines late; limited derivational options |
| Heavy NP | Not structural; CCG predicts ambiguity |
-/

/-- CCG analysis of a freezing context -/
inductive CCGFreezingReason where
  | singleDerivation    -- Only one parse exists
  | noTypeRaising       -- Type-raising not available in this config
  | argumentStructure   -- Different argument structure forces scope
  | notFrozen           -- CCG predicts ambiguity
  deriving DecidableEq, BEq, Repr, Inhabited

/-- CCG's analysis of each freezing context -/
def ccgAnalyzeContext : FreezingContext → CCGFreezingReason
  | .none => .notFrozen
  | .possessor => .singleDerivation  -- Possessor DP is pre-built
  | .doubleObject => .argumentStructure  -- DOC has different structure
  | .passive => .singleDerivation  -- By-phrase limited
  | .heavyNP => .notFrozen  -- Structure same; CCG predicts ambiguous
  | .weakCrossover => .notFrozen  -- Binding issue, not derivational
  | .adjunct => .singleDerivation
  | .attitude => .singleDerivation

/-- Does CCG predict freezing? -/
def ccgPredictsFreezing (ctx : FreezingContext) : Bool :=
  ccgAnalyzeContext ctx != .notFrozen

-- Processing/Gradient Account

/-!
## Processing Explanation

Processing accounts (Anderson 2004, Scontras et al. 2017) argue:
- Inverse scope requires **reanalysis** or **memory operations**
- Cost scales with **complexity** of intervening material
- Freezing = cost exceeds threshold (gradient, not categorical)

### Processing Predictions

| Context | Processing Explanation |
|---------|----------------------|
| Possessor | Complex subject increases memory load |
| Double object | Two objects increase complexity |
| Passive | By-phrase is late; reanalysis costly |
| Heavy NP | Complexity directly increases cost |
-/

/-- Complexity factors that affect inverse scope processing -/
structure ProcessingComplexity where
  /-- Words in subject -/
  subjectLength : Nat
  /-- Embedding depth -/
  embeddingDepth : Nat
  /-- Number of scope-bearing elements -/
  scopeBearers : Nat := 2
  deriving Repr

/-- Estimate processing cost (arbitrary units) -/
def estimateCost (c : ProcessingComplexity) : Nat :=
  c.subjectLength + c.embeddingDepth * 3 + c.scopeBearers

/-- Processing threshold for inverse scope availability -/
def inverseThreshold : Nat := 10

/-- Does processing predict freezing (gradient)? -/
def processingPredictsFreezing (c : ProcessingComplexity) : Bool :=
  estimateCost c > inverseThreshold

-- Theory Comparison

/-- Predictions from all three theories -/
structure TheoryPredictions where
  context : FreezingContext
  minimalism : Bool  -- Predicts freezing?
  ccg : Bool
  processing : Bool
  observed : Availability
  deriving Repr

/-- Compare theories on a freezing context -/
def comparePredictions (ctx : FreezingContext) (obs : Availability)
    (complexity : ProcessingComplexity := ⟨5, 1, 2⟩) : TheoryPredictions :=
  { context := ctx
  , minimalism := predictsFreezing ctx
  , ccg := ccgPredictsFreezing ctx
  , processing := processingPredictsFreezing complexity
  , observed := obs }

-- Key Comparisons

/-- Possessor freezing: all theories agree -/
def possessorComparison : TheoryPredictions :=
  comparePredictions .possessor .surfaceOnly ⟨8, 1, 2⟩

/-- Double object: all theories agree -/
def doubleObjectComparison : TheoryPredictions :=
  comparePredictions .doubleObject .surfaceOnly ⟨6, 2, 3⟩  -- 6+6+3=15 > 10

/-- Heavy NP: theories DIVERGE -/
def heavyNPComparison : TheoryPredictions :=
  comparePredictions .heavyNP .surfaceOnly ⟨15, 1, 2⟩

/-- Baseline: all theories agree (ambiguous) -/
def baselineComparison : TheoryPredictions :=
  comparePredictions .none .ambiguous ⟨3, 0, 2⟩

-- Divergence Detection

/-- Check if all theories agree -/
def theoriesAgree (p : TheoryPredictions) : Bool :=
  let frozen := p.observed == .surfaceOnly
  (p.minimalism == frozen) && (p.ccg == frozen) && (p.processing == frozen)

/-- Find where theories diverge -/
def theoriesDiverge (p : TheoryPredictions) : Bool :=
  !theoriesAgree p

/-- Heavy NP is the key divergence case -/
theorem heavy_np_diverges :
    theoriesDiverge heavyNPComparison = true := by native_decide

/-- Possessor has agreement -/
theorem possessor_agrees :
    theoriesAgree possessorComparison = true := by native_decide

-- Detailed Divergence Analysis

/-!
## Where Theories Diverge

### Heavy NP
- **Minimalism**: No grammatical barrier → predicts AMBIGUOUS
- **CCG**: Same derivations available → predicts AMBIGUOUS
- **Processing**: High complexity → predicts FROZEN
- **Observed**: Frozen (gradient)

**Verdict**: Processing explains heavy NP; grammar theories fail.

### Gradient Passive Judgments
- **Minimalism**: Adjunct island → predicts categorical freezing
- **CCG**: Single derivation → predicts categorical freezing
- **Processing**: Moderate cost → predicts gradient
- **Observed**: Gradient (weaker than possessor)

**Verdict**: Processing captures gradience; grammar theories predict categorical.

### Context Effects (Hypothetical)
If context can rescue "frozen" readings:
- **Minimalism**: No rescue possible (grammatical)
- **CCG**: No rescue possible (derivational)
- **Processing/RSA**: Rescue possible with strong context

**Test**: Find contexts where "frozen" readings become available.
-/

/-- Divergence types -/
inductive DivergenceType where
  | grammarVsProcessing  -- Grammar says ok, processing says frozen
  | processingVsGrammar  -- Processing says ok, grammar says frozen
  | allAgree             -- No divergence
  deriving DecidableEq, BEq, Repr

/-- Classify the divergence -/
def classifyDivergence (p : TheoryPredictions) : DivergenceType :=
  let frozen := p.observed == .surfaceOnly
  let grammarPredicts := p.minimalism || p.ccg
  if grammarPredicts == frozen && p.processing == frozen then
    .allAgree
  else if !grammarPredicts && frozen then
    .grammarVsProcessing  -- Grammar allows, but frozen (processing explains)
  else if grammarPredicts && !frozen then
    .processingVsGrammar  -- Grammar blocks, but available (grammar wrong)
  else
    .allAgree

/-- Heavy NP is grammar-vs-processing divergence -/
theorem heavy_np_is_processing_case :
    classifyDivergence heavyNPComparison = .grammarVsProcessing := by
  native_decide

-- Accuracy Comparison

/-- Count correct predictions for a theory -/
def countCorrect (predictions : List TheoryPredictions)
    (theory : TheoryPredictions → Bool) : Nat :=
  predictions.filter (λ p =>
    let frozen := p.observed == .surfaceOnly
    theory p == frozen
  ) |>.length

def allComparisons : List TheoryPredictions :=
  [ possessorComparison
  , doubleObjectComparison
  , heavyNPComparison
  , baselineComparison ]

/-- Minimalism accuracy -/
def minimalismAccuracy : Nat :=
  countCorrect allComparisons (·.minimalism)

/-- CCG accuracy -/
def ccgAccuracy : Nat :=
  countCorrect allComparisons (·.ccg)

/-- Processing accuracy -/
def processingAccuracy : Nat :=
  countCorrect allComparisons (·.processing)

#eval minimalismAccuracy   -- 3/4 (misses heavy NP)
#eval ccgAccuracy          -- 3/4 (misses heavy NP)
#eval processingAccuracy   -- 4/4

-- Theoretical Implications

/-!
## Theoretical Implications

### What the Comparison Shows

1. **Grammar theories (Minimalism, CCG) agree on most cases**
   - Both predict possessor, double object, passive freezing
   - Both fail on heavy NP (no grammatical barrier)

2. **Processing fills the gap**
   - Explains heavy NP via complexity
   - Explains gradient judgments
   - Compatible with grammar accounts for clear cases

3. **Possible synthesis**
   - Grammar determines AVAILABLE readings
   - Processing/pragmatics determines PREFERRED readings
   - "Freezing" may be a mix: some grammatical, some processing

### Open Questions

1. **Is possessor freezing truly categorical?**
   - Need experimental data comparing possessor vs heavy NP

2. **Can context rescue frozen readings?**
   - Would distinguish grammar from processing accounts

3. **Cross-linguistic variation?**
   - Some languages show different freezing patterns
   - Scrambling languages may differ (Antonyuk 2015)

### Proposed Test Cases

```
Baseline: "A student attended every seminar" (ambiguous)
Possessor: "A student's teacher attended every seminar" (frozen?)
Heavy: "A student from the university attended every seminar" (frozen?)
```

If possessor is MORE frozen than heavy NP, grammar contributes.
If they're equally frozen, processing suffices.

### RSA Rescue Prediction

See `RSA/Implementations/ScopeFreezing.lean`: takes `possessor_frozen.observed`
(from phenomena data, which grammar predicts) as interpretation prior,
then `rsa_can_rescue_frozen` proves world priors can rescue.
Frozen: P(inverse) = 2%; Rescued: P(inverse) > 50%.
-/

-- Summary

/-!
## Summary: Scope Freezing Comparison

### Agreement
| Context | Minimalism | CCG | Processing | Observed |
|---------|------------|-----|------------|----------|
| Baseline | ✗ | ✗ | ✗ | Ambiguous |
| Possessor | ✓ | ✓ | ✓ | Frozen |
| Double obj | ✓ | ✓ | ✓ | Frozen |
| Heavy NP | ✗ | ✗ | ✓ | Frozen |

(✓ = predicts frozen, ✗ = predicts ambiguous)

### Key Divergence
**Heavy NP**: Only processing predicts freezing.
- Minimalism: No phase/island barrier
- CCG: Same derivations available
- Processing: High memory cost

### Theoretical Conclusion
Scope freezing is likely a **mixed phenomenon**:
- Some cases are grammatical (possessor, double object)
- Some cases are processing-based (heavy NP)
- Gradient judgments suggest processing plays a role even in "grammatical" cases

### Empirical Need
Controlled experiments comparing:
- Possessor vs heavy NP freezing strength
- Context effects on frozen readings
- Cross-linguistic patterns
-/

end Comparisons.ScopeFreezing
