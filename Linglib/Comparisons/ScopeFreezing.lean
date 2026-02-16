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

import Linglib.Core.Interface
import Linglib.Core.ProcessingModel
import Linglib.Phenomena.Quantification.Data
import Linglib.Phenomena.Quantification.Bridge_Minimalism
import Linglib.Theories.Syntax.CCG.Scope

namespace Comparisons.ScopeFreezing

open ScopeTheory
open ProcessingModel
open Phenomena.Quantification.Data
open Phenomena.Quantification.Bridge_Minimalism
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

-- Processing/Gradient Account via ProcessingProfile

/-!
## Processing Explanation

Processing accounts (Anderson 2004, Scontras et al. 2017) argue:
- Inverse scope requires **reanalysis** or **memory operations**
- Cost scales with **complexity** of intervening material
- Freezing = processing profile of frozen condition Pareto-dominates baseline

### Processing Predictions

| Context | Processing Explanation |
|---------|----------------------|
| Possessor | Complex subject increases locality and referential load |
| Double object | Two objects increase referential load and boundaries |
| Passive | By-phrase increases locality; reanalysis costly |
| Heavy NP | Complexity directly increases locality and referential load |
-/

-- ============================================================================
-- Concrete Processing Profiles for Scope Conditions
-- ============================================================================

/-- Baseline: "A student attended every seminar" — short, simple. -/
def baseline_scope : ProcessingProfile :=
  { locality := 3, boundaries := 0, referentialLoad := 0, ease := 0 }

/-- Possessor: "A student's teacher attended every seminar" — complex subject. -/
def possessor_scope : ProcessingProfile :=
  { locality := 5, boundaries := 0, referentialLoad := 2, ease := 0 }

/-- Double object: "A teacher gave every student a book" — two objects. -/
def doubleObject_scope : ProcessingProfile :=
  { locality := 4, boundaries := 0, referentialLoad := 2, ease := 0 }

/-- Heavy NP: "A student from the local university attended every seminar" -/
def heavyNP_scope : ProcessingProfile :=
  { locality := 8, boundaries := 0, referentialLoad := 1, ease := 0 }

/-- Scope condition type for typeclass instance. -/
inductive ScopeCondition where
  | baseline
  | possessor
  | doubleObject
  | heavyNP
  deriving Repr, DecidableEq, BEq

instance : HasProcessingProfile ScopeCondition where
  profile
    | .baseline     => baseline_scope
    | .possessor    => possessor_scope
    | .doubleObject => doubleObject_scope
    | .heavyNP      => heavyNP_scope

/-- Does the processing model predict freezing (harder than baseline)? -/
def processingPredictsFreezing (ctx : ScopeCondition) : Bool :=
  (HasProcessingProfile.profile ctx |>.compare baseline_scope) == .harder

-- Theory Comparison

/-- Predictions from all three theories -/
structure TheoryPredictions where
  context : FreezingContext
  minimalism : Bool  -- Predicts freezing?
  ccg : Bool
  /-- Processing comparison against baseline (Pareto dominance) -/
  processing : CompareResult
  observed : Availability
  deriving Repr

/-- Does the processing prediction match observation?
Frozen observed → processing should be harder than baseline.
Ambiguous observed → processing should not be harder. -/
def processingMatchesObserved (p : TheoryPredictions) : Bool :=
  let frozen := p.observed == .surfaceOnly
  match p.processing with
  | .harder => frozen
  | .easier | .equal | .incomparable => !frozen

/-- Compare theories on a freezing context -/
def comparePredictions (ctx : FreezingContext) (obs : Availability)
    (condition : ScopeCondition) : TheoryPredictions :=
  { context := ctx
  , minimalism := predictsFreezing ctx
  , ccg := ccgPredictsFreezing ctx
  , processing := HasProcessingProfile.profile condition |>.compare baseline_scope
  , observed := obs }

-- Key Comparisons

/-- Possessor freezing: all theories agree -/
def possessorComparison : TheoryPredictions :=
  comparePredictions .possessor .surfaceOnly .possessor

/-- Double object: all theories agree -/
def doubleObjectComparison : TheoryPredictions :=
  comparePredictions .doubleObject .surfaceOnly .doubleObject

/-- Heavy NP: theories DIVERGE -/
def heavyNPComparison : TheoryPredictions :=
  comparePredictions .heavyNP .surfaceOnly .heavyNP

/-- Baseline: all theories agree (ambiguous) -/
def baselineComparison : TheoryPredictions :=
  comparePredictions .none .ambiguous .baseline

-- Divergence Detection

/-- Check if all theories agree -/
def theoriesAgree (p : TheoryPredictions) : Bool :=
  let frozen := p.observed == .surfaceOnly
  let processingPredicts := p.processing == .harder
  (p.minimalism == frozen) && (p.ccg == frozen) && (processingPredicts == frozen)

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
- **Processing**: Pareto harder than baseline → predicts FROZEN
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
  let processingPredicts := p.processing == .harder
  if grammarPredicts == frozen && processingPredicts == frozen then
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
  countCorrect allComparisons (λ p => p.processing == .harder)

#eval minimalismAccuracy   -- 3/4 (misses heavy NP)
#eval ccgAccuracy          -- 3/4 (misses heavy NP)
#eval processingAccuracy   -- 4/4

-- Ordering Predictions (via shared infrastructure)

/-- Verify processing ordering predictions against empirical data. -/
def scopeOrderingPredictions : List (OrderingPrediction ScopeCondition) := [
  { harder := .possessor, easier := .baseline,
    description := "Possessor harder than baseline" },
  { harder := .doubleObject, easier := .baseline,
    description := "Double object harder than baseline" },
  { harder := .heavyNP, easier := .baseline,
    description := "Heavy NP harder than baseline" }
]

/-- All scope ordering predictions verified by Pareto dominance. -/
theorem all_scope_ordering_predictions_verified :
    scopeOrderingPredictions.all verifyOrdering = true := by native_decide

-- Theoretical Implications

/-!
## Theoretical Implications

### What the Comparison Shows

1. **Grammar theories (Minimalism, CCG) agree on most cases**
   - Both predict possessor, double object, passive freezing
   - Both fail on heavy NP (no grammatical barrier)

2. **Processing fills the gap**
   - Explains heavy NP via Pareto-harder profile
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
- Processing: Pareto harder than baseline

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
