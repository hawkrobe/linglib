/-
# ImplicatureTheory: Abstract Interface for Scalar Implicature Predictions

This typeclass defines what it means for a theory to make predictions about
scalar implicatures. The interface is **theory-neutral**: it doesn't assume
Neo-Gricean belief states, RSA probabilities, or any particular mechanism.

## Design Principle

Different theories use different mechanisms:
- NeoGricean: Belief states + competence (Bel_S(¬ψ))
- RSA: Probabilistic reasoning (P_L1(some_not_all) > P_L1(all))
- Grammatical: Local vs global computation

But they all make **predictions** about when implicatures arise.
This interface captures that common ground.

## Key Challenge

NeoGricean makes **categorical** predictions (Bel_S(¬all)), while RSA makes
**probabilistic** predictions (P_L1(some_not_all) > P_L1(all)). The interface
accommodates both by:
1. Using a status enum for categorical predictions
2. Providing optional strength field for quantitative theories

## Usage

Each theory implements this interface in its own terms. Then comparison
theorems can prove when different theories make the same predictions.

```
Theories/NeoGricean/ImplicatureInstance.lean
  instance : ImplicatureTheory NeoGriceanTheory where ...

Theories/RSA/ImplicatureInstance.lean
  instance : ImplicatureTheory RSATheory where ...

Comparisons/Implicature.lean
  theorem theories_diverge_on_de : ...
```

## References

- Geurts, B. (2010). Quantity Implicatures. Cambridge University Press.
- Goodman & Frank (2016). Pragmatic Language Interpretation as Probabilistic Inference.
- Geurts & Pouscoulous (2009). Embedded implicatures?!
-/

import Linglib.Core.Basic

namespace Interfaces

-- ============================================================================
-- Part 1: Implicature Status
-- ============================================================================

/-- The possible implicature outcomes for a scalar position -/
inductive ImplicatureStatus where
  /-- Implicature is derived (Bel_S(¬ψ) or P > threshold) -/
  | triggered
  /-- Implicature is available but not required -/
  | possible
  /-- Implicature is blocked (DE context, no competence) -/
  | blocked
  /-- No scalar item / irrelevant position -/
  | absent
  deriving Repr, DecidableEq

-- ============================================================================
-- Part 2: The Core Interface
-- ============================================================================

/-- A theory that makes predictions about scalar implicatures.

    This is the **theory-neutral interface** that all frameworks implement.
    The interface says nothing about mechanism (belief states, probabilities, etc.),
    only about observable predictions.

    Type parameter `T` is a marker type for the theory (e.g., `NeoGriceanTheory`). -/
class ImplicatureTheory (T : Type) where
  /-- The theory's internal representation of an utterance in context -/
  Structure : Type

  /-- Parse words into the theory's representation.
      Returns `none` if the theory can't parse this input. -/
  parse : List Word → Option Structure

  /-- Predict the implicature status for a scalar position.

      Position indexes into the word list:
      - "some students sleep" → position 0 = some (scalar item)

      Returns the theory's prediction about whether an implicature arises. -/
  implicatureStatus : Structure → Nat → ImplicatureStatus

  /-- Optional: strength/probability (0-100 scale).

      NeoGricean: baseline rate (e.g., 35% for contextualism)
      RSA: L1 probability converted to percentage

      Returns `none` if the theory doesn't provide quantitative predictions. -/
  implicatureStrength : Structure → Nat → Option Nat

  /-- Does the theory predict implicature blocked in downward-entailing contexts? -/
  predictsDEBlocking : Bool

  /-- Does the theory predict a task effect (asking about SI raises rate)? -/
  predictsTaskEffect : Bool

  /-- Predicted baseline implicature rate (%) in neutral contexts -/
  predictedBaselineRate : Nat

-- ============================================================================
-- Part 3: Derived Operations
-- ============================================================================

variable {T : Type} [ImplicatureTheory T]

/-- Check if implicature is derived at position pos -/
def derivesImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .triggered => true
  | _ => false

/-- Check if implicature is blocked at position pos -/
def blocksImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .blocked => true
  | _ => false

/-- Check if implicature is possible (but not required) at position pos -/
def possibleImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .possible => true
  | _ => false

/-- Check if any implicature arises (triggered or possible) at position pos -/
def anyImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .triggered => true
  | .possible => true
  | _ => false

-- ============================================================================
-- Part 4: Theory Comparison
-- ============================================================================

variable {T1 T2 : Type} [ImplicatureTheory T1] [ImplicatureTheory T2]

/-- Two theories agree on a sentence at a position if they make the same status prediction -/
def theoriesAgreeOnStatus (ws : List Word) (pos : Nat) : Bool :=
  match ImplicatureTheory.parse (T := T1) ws,
        ImplicatureTheory.parse (T := T2) ws with
  | some s1, some s2 =>
    ImplicatureTheory.implicatureStatus s1 pos ==
    ImplicatureTheory.implicatureStatus s2 pos
  | none, none => true   -- Both can't parse → vacuous agreement
  | _, _ => false        -- One parses, other doesn't → disagreement

/-- Two theories agree on whether an implicature is derived -/
def theoriesAgreeOnDerivation (ws : List Word) (pos : Nat) : Bool :=
  match ImplicatureTheory.parse (T := T1) ws,
        ImplicatureTheory.parse (T := T2) ws with
  | some s1, some s2 =>
    derivesImplicature s1 pos == derivesImplicature s2 pos
  | none, none => true
  | _, _ => false

/-- Two theories agree on DE blocking prediction -/
def theoriesAgreeOnDEPrediction : Bool :=
  ImplicatureTheory.predictsDEBlocking (T := T1) ==
  ImplicatureTheory.predictsDEBlocking (T := T2)

/-- Two theories agree on task effect prediction -/
def theoriesAgreeOnTaskEffect : Bool :=
  ImplicatureTheory.predictsTaskEffect (T := T1) ==
  ImplicatureTheory.predictsTaskEffect (T := T2)

-- ============================================================================
-- Part 5: Empirical Comparison
-- ============================================================================

/-- Compare a theory's predicted rate to empirical data -/
def rateMatchesData (predictedRate observedRate : Nat) (tolerance : Nat := 5) : Bool :=
  let diff := if predictedRate > observedRate
              then predictedRate - observedRate
              else observedRate - predictedRate
  diff <= tolerance

/-- Which theory's baseline is closer to observed data? -/
def closerToData (observed : Nat) : Bool :=
  let diff1 := if ImplicatureTheory.predictedBaselineRate (T := T1) > observed
               then ImplicatureTheory.predictedBaselineRate (T := T1) - observed
               else observed - ImplicatureTheory.predictedBaselineRate (T := T1)
  let diff2 := if ImplicatureTheory.predictedBaselineRate (T := T2) > observed
               then ImplicatureTheory.predictedBaselineRate (T := T2) - observed
               else observed - ImplicatureTheory.predictedBaselineRate (T := T2)
  diff1 < diff2

-- ============================================================================
-- Part 6: Documentation
-- ============================================================================

/-
## How to Implement This Interface

Each theory provides an instance by defining:

1. `Structure`: The theory's internal representation
   - NeoGricean: StandardRecipeResult + polarity + scalar position
   - RSA: RSAScalarResult

2. `parse`: How to build the structure from words
   - Can be partial (return `none` for unparseable inputs)

3. `implicatureStatus`: The theory's prediction for each position
   - This is where the theory's mechanism gets applied

4. `implicatureStrength`: Optional quantitative prediction
   - NeoGricean: baseline rate from params
   - RSA: L1 probability

5. `predictsDEBlocking`: Does the theory model DE blocking?
   - NeoGricean: Yes (context polarity affects alternatives)
   - RSA: No (current model doesn't include DE)

6. `predictsTaskEffect`: Does asking about SI raise rates?
   - Contextualism (Geurts): Yes
   - Defaultism (Levinson): No
   - RSA: No

7. `predictedBaselineRate`: What rate does theory predict?
   - Geurts: ~35%
   - Levinson: ~90%
   - RSA: ~50%

## Example: NeoGricean

```
structure NeoGriceanTheory

instance : ImplicatureTheory NeoGriceanTheory where
  Structure := NeoGriceanStructure
  parse := parseToNeoGricean
  implicatureStatus := λ s pos =>
    if s.scalarPosition != some pos then .absent
    else if s.polarity == .downward then .blocked
    else if s.result.strongImplicature then .triggered
    else if s.result.weakImplicature then .possible
    else .absent
  implicatureStrength := ...
  predictsDEBlocking := true
  predictsTaskEffect := true
  predictedBaselineRate := 35
```

## What This Enables

1. **Automatic comparison**: Once theories implement the interface,
   we can test if they agree on any input.

2. **Divergence detection**: If Theory A predicts triggered and
   Theory B predicts blocked, we've found a divergence point.

3. **Empirical adjudication**: When theories diverge, empirical data
   (Geurts & Pouscoulous 2009) can decide which prediction is correct.

4. **Coverage tracking**: Which theories handle which phenomena?
-/

-- ============================================================================
-- Part 6: Systematic Coverage Tracking
-- ============================================================================

/-- Coverage status for a phenomenon.

    Distinguishes between different reasons for missing coverage:
    - `complete`: Theory models this and predictions are verified
    - `incomplete`: Theory could model this but formalization is missing
    - `outOfScope`: Theory doesn't claim to handle this phenomenon
    - `wrong`: Theory makes prediction that conflicts with data -/
inductive CoverageStatus where
  | complete      -- Modeled and verified
  | incomplete    -- Could be modeled, formalization missing
  | outOfScope    -- Theory doesn't address this phenomenon
  | wrong         -- Prediction conflicts with data
  deriving Repr, DecidableEq, BEq

/-- Pragmatic phenomena that theories might cover -/
inductive PragmaticPhenomenon where
  | scalarImplicature      -- Basic SI (some → not all)
  | deBlocking             -- SI blocked in DE contexts
  | taskEffect             -- Asking about SI raises rates
  | referenceGames         -- Ad-hoc implicatures in reference games
  | knowledgeCancellation  -- SI varies with speaker knowledge
  | exhaustivity           -- "Who came? John" → only John
  | freeChoice             -- "You may have cake or ice cream" → both permitted
  deriving Repr, DecidableEq, BEq

/-- Coverage report for a single phenomenon -/
structure PhenomenonCoverage where
  phenomenon : PragmaticPhenomenon
  status : CoverageStatus
  notes : String
  deriving Repr

/-- Full coverage report for a theory -/
structure TheoryCoverage where
  theoryName : String
  phenomena : List PhenomenonCoverage
  deriving Repr

/-- Get status for a phenomenon (helper) -/
def TheoryCoverage.statusFor (tc : TheoryCoverage) (p : PragmaticPhenomenon) : Option CoverageStatus :=
  tc.phenomena.find? (·.phenomenon == p) |>.map (·.status)

/-- Count phenomena by status -/
def TheoryCoverage.countByStatus (tc : TheoryCoverage) (s : CoverageStatus) : Nat :=
  tc.phenomena.filter (·.status == s) |>.length

/-- List incomplete phenomena -/
def TheoryCoverage.incompletePhenomena (tc : TheoryCoverage) : List PragmaticPhenomenon :=
  tc.phenomena.filter (·.status == .incomplete) |>.map (·.phenomenon)

/-- List out-of-scope phenomena -/
def TheoryCoverage.outOfScopePhenomena (tc : TheoryCoverage) : List PragmaticPhenomenon :=
  tc.phenomena.filter (·.status == .outOfScope) |>.map (·.phenomenon)

-- ============================================================================
-- Part 6b: Legacy Coverage Summary (for backwards compatibility)
-- ============================================================================

/-- Summary of what a theory covers vs what's incomplete -/
structure CoverageSummary where
  /-- Does it derive basic SIs? -/
  derivesBasicSI : Bool
  /-- Does it model DE blocking? -/
  modelsDEBlocking : Bool
  /-- Does it model task effects? -/
  modelsTaskEffect : Bool
  /-- Is baseline rate specified? -/
  hasBaselineRate : Bool
  /-- Notes about incompleteness -/
  incompleteNotes : List String
  deriving Repr

/-- Generate coverage summary for a theory -/
def coverageSummary (T : Type) [ImplicatureTheory T] : CoverageSummary :=
  { derivesBasicSI := ImplicatureTheory.predictedBaselineRate (T := T) > 0
  , modelsDEBlocking := ImplicatureTheory.predictsDEBlocking (T := T)
  , modelsTaskEffect := ImplicatureTheory.predictsTaskEffect (T := T)
  , hasBaselineRate := true  -- All theories must specify this
  , incompleteNotes :=
      (if ImplicatureTheory.predictsDEBlocking (T := T) then []
       else ["DE blocking not modeled"]) ++
      (if ImplicatureTheory.predictsTaskEffect (T := T) then []
       else ["Task effect not modeled"])
  }

-- ============================================================================
-- Part 7: Linking to Empirical Data
-- ============================================================================

/-
## Connecting to Empirical Data

These structures and functions link ImplicatureTheory predictions to
the empirical data types in Phenomena/EmpiricalData.lean and
Phenomena/ScalarImplicatures/Data.lean.
-/

/-- A DE blocking test case derived from empirical data -/
structure DEBlockingTestCase where
  /-- Description of the UE example -/
  ueDescription : String
  /-- Description of the DE example -/
  deDescription : String
  /-- The scalar term -/
  scalarTerm : String
  /-- Expected: implicature arises in UE -/
  expectedUE : Bool
  /-- Expected: implicature blocked in DE -/
  expectedDE : Bool
  deriving Repr

/-- A task effect test case from Geurts & Pouscoulous 2009 -/
structure TaskEffectTestCase where
  /-- Inference task rate (percentage) -/
  inferenceRate : Nat
  /-- Verification task rate (percentage) -/
  verificationRate : Nat
  /-- Is the difference significant? -/
  significant : Bool
  deriving Repr

/-- Result of testing a theory against DE blocking data -/
structure DEBlockingResult where
  /-- Does the theory predict DE blocking? -/
  theoryPredictsDEBlocking : Bool
  /-- Does the data show DE blocking? -/
  datashowsDEBlocking : Bool
  /-- Do they match? -/
  isMatch : Bool
  deriving Repr

/-- Test a theory against a DE blocking test case -/
def testDEBlocking {T : Type} [ImplicatureTheory T] (tc : DEBlockingTestCase) : DEBlockingResult :=
  let theoryPredicts := ImplicatureTheory.predictsDEBlocking (T := T)
  let dataShows := tc.expectedUE && !tc.expectedDE
  { theoryPredictsDEBlocking := theoryPredicts
  , datashowsDEBlocking := dataShows
  , isMatch := theoryPredicts == dataShows
  }

/-- Result of testing a theory against task effect data -/
structure TaskEffectResult where
  /-- Does the theory predict task effect? -/
  theoryPredictsTaskEffect : Bool
  /-- Does the data show task effect? -/
  dataShowsTaskEffect : Bool
  /-- Theory's predicted baseline rate -/
  predictedRate : Nat
  /-- Observed rate (verification task) -/
  observedRate : Nat
  /-- Difference between predicted and observed -/
  rateDifference : Nat
  /-- Does theory match data? -/
  isMatch : Bool
  deriving Repr

/-- Test a theory against task effect data -/
def testTaskEffect {T : Type} [ImplicatureTheory T] (tc : TaskEffectTestCase) (tolerance : Nat := 10) : TaskEffectResult :=
  let theoryPredicts := ImplicatureTheory.predictsTaskEffect (T := T)
  let dataShows := tc.significant && tc.inferenceRate > tc.verificationRate
  let predicted := ImplicatureTheory.predictedBaselineRate (T := T)
  let observed := tc.verificationRate
  let diff := if predicted > observed then predicted - observed else observed - predicted
  { theoryPredictsTaskEffect := theoryPredicts
  , dataShowsTaskEffect := dataShows
  , predictedRate := predicted
  , observedRate := observed
  , rateDifference := diff
  , isMatch := (theoryPredicts == dataShows) && (diff <= tolerance)
  }

-- ============================================================================
-- Part 7: Captures Typeclasses
-- ============================================================================

/-- A theory captures DE blocking data if its prediction isMatch the pattern -/
class CapturesDEBlockingPattern (T : Type) [ImplicatureTheory T] where
  /-- The test case from empirical data -/
  testCase : DEBlockingTestCase
  /-- Proof that theory isMatch data -/
  theoryMatchesData : (testDEBlocking (T := T) testCase).isMatch = true

/-- A theory captures task effect data if its predictions match the observations -/
class CapturesTaskEffectData (T : Type) [ImplicatureTheory T] where
  /-- The task effect data -/
  taskEffectData : TaskEffectTestCase
  /-- Tolerance for rate matching -/
  tolerance : Nat := 10
  /-- Proof that theory isMatch task effect pattern -/
  taskEffectMatches : (testTaskEffect (T := T) taskEffectData tolerance).theoryPredictsTaskEffect ==
                      (testTaskEffect (T := T) taskEffectData tolerance).dataShowsTaskEffect
  /-- Proof that predicted rate is close to observed -/
  rateWithinTolerance : (testTaskEffect (T := T) taskEffectData tolerance).rateDifference <= tolerance

-- ============================================================================
-- Part 8: Comparison with Rate Data
-- ============================================================================

/-- Compare a theory's baseline rate to observed data -/
def compareToObservedRate {T : Type} [ImplicatureTheory T] (observedRate : Nat) : Nat × Nat × Bool :=
  let predicted := ImplicatureTheory.predictedBaselineRate (T := T)
  let diff := if predicted > observedRate then predicted - observedRate else observedRate - predicted
  (predicted, diff, diff <= 10)

/-- Which of two theories is closer to observed rate? -/
def closerToObservedRate {T1 T2 : Type} [ImplicatureTheory T1] [ImplicatureTheory T2]
    (observedRate : Nat) : Bool × Bool :=
  let (_, diff1, _) := compareToObservedRate (T := T1) observedRate
  let (_, diff2, _) := compareToObservedRate (T := T2) observedRate
  (diff1 < diff2, diff1 <= diff2)

end Interfaces
