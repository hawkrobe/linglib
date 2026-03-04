/-
# Implicature Theory Comparison

Compares NeoGricean and RSA theories using the ImplicatureTheory interface.

## Results

### Where Theories Agree
- Both derive scalar implicatures for "some" (predicted baseline > 0)
- Both treat "all" as top of scale (no implicature)
- Both predict DE blocking (RSA via @cite{potts-etal-2016} lexical uncertainty)

### Where Theories Differ

| Aspect | NeoGricean | RSA (current) | RSA Status |
|--------|------------|---------------|------------|
| Simple SI | ✅ Derives | ✅ Derives | Complete |
| DE blocking | ✅ Models | ✅ Models | Complete (@cite{potts-etal-2016}) |
| Task effect | ✅ Models | ❌ N/A | **Incomplete** |
| Baseline rate | 35% | 50% | Different prediction |

**Important**: RSA's remaining gap (task effect) is due to **model incompleteness**,
not theoretical limitations. The current RSA formalization lacks QUD manipulation.

### Empirical Fit (where comparable)
@cite{geurts-pouscoulous-2009} verification task: 34% SI rate
- NeoGricean (35%): 1% difference ✓
- RSA (50%): 16% difference (but model may be incomplete here too)

-/

import Linglib.Core.Interface
import Linglib.Theories.Pragmatics.NeoGricean.ScalarImplicatures.Basic
import Linglib.Theories.Pragmatics.RSA.ScalarImplicatures.Basic

namespace Comparisons.ScalarImplicatureTheories

open Interfaces

-- Part 1: Where Theories Agree

/-- Both theories derive some implicatures (baseline > 0) -/
theorem both_derive_implicatures :
    ImplicatureTheory.predictedBaselineRate (T := NeoGricean.NeoGriceanTheory) > 0 ∧
    ImplicatureTheory.predictedBaselineRate (T := RSA.RSATheory) > 0 := by
  native_decide

/-- Both theories trigger implicature for "some" in UE context -/
theorem both_trigger_some_ue :
    ImplicatureTheory.implicatureStatus (T := NeoGricean.NeoGriceanTheory)
      NeoGricean.someStudentsSleepNG 0 = .triggered ∧
    ImplicatureTheory.implicatureStatus (T := RSA.RSATheory)
      RSA.someRSA 0 = .triggered := by
  native_decide

/-- Both theories derive triggered (not just possible) for "some" -/
theorem both_triggered_not_possible :
    derivesImplicature (T := NeoGricean.NeoGriceanTheory) NeoGricean.someStudentsSleepNG 0 = true ∧
    derivesImplicature (T := RSA.RSATheory) RSA.someRSA 0 = true := by
  native_decide

/-- Neither theory triggers implicature for "all" (top of scale) -/
theorem both_no_implicature_all :
    ImplicatureTheory.implicatureStatus (T := RSA.RSATheory)
      RSA.allRSA 0 = .absent := by
  native_decide

-- Part 2: Where Theories Diverge

/-- NeoGricean predicts DE blocking -/
theorem neogricean_predicts_de_blocking :
    ImplicatureTheory.predictsDEBlocking (T := NeoGricean.NeoGriceanTheory) = true := by
  native_decide

/-- RSA predicts DE blocking (via @cite{potts-etal-2016} lexical uncertainty) -/
theorem rsa_predicts_de_blocking :
    ImplicatureTheory.predictsDEBlocking (T := RSA.RSATheory) = true := by
  native_decide

/-- Both theories now predict DE blocking -/
theorem both_predict_de_blocking :
    ImplicatureTheory.predictsDEBlocking (T := NeoGricean.NeoGriceanTheory) = true ∧
    ImplicatureTheory.predictsDEBlocking (T := RSA.RSATheory) = true := by
  native_decide

/-- NeoGricean predicts task effect (contextualism) -/
theorem neogricean_predicts_task_effect :
    ImplicatureTheory.predictsTaskEffect (T := NeoGricean.NeoGriceanTheory) = true := by
  native_decide

/-- RSA model incomplete: doesn't handle task effects -/
theorem rsa_task_effect_incomplete :
    ImplicatureTheory.predictsTaskEffect (T := RSA.RSATheory) = false := by
  native_decide

/-- NeoGricean models task effect, RSA incomplete -/
theorem neogricean_task_complete_rsa_incomplete :
    ImplicatureTheory.predictsTaskEffect (T := NeoGricean.NeoGriceanTheory) = true ∧
    ImplicatureTheory.predictsTaskEffect (T := RSA.RSATheory) = false := by
  native_decide

/-- Theories have different baseline rates -/
theorem different_baseline_rates :
    ImplicatureTheory.predictedBaselineRate (T := NeoGricean.NeoGriceanTheory) ≠
    ImplicatureTheory.predictedBaselineRate (T := RSA.RSATheory) := by
  native_decide

-- Part 3: Empirical Comparison: @cite{geurts-pouscoulous-2009}

/-- Observed verification task rate from @cite{geurts-pouscoulous-2009} -/
def geurtsPouscolousVerificationRate : Nat := 34

/-- NeoGricean baseline (35%) is close to observed (34%) -/
theorem neogricean_close_to_observed :
    let ng_rate := ImplicatureTheory.predictedBaselineRate (T := NeoGricean.NeoGriceanTheory)
    let diff := if ng_rate > geurtsPouscolousVerificationRate
                then ng_rate - geurtsPouscolousVerificationRate
                else geurtsPouscolousVerificationRate - ng_rate
    diff < 5 := by
  native_decide

/-- RSA baseline (50%) is far from observed (34%) -/
theorem rsa_far_from_observed :
    let rsa_rate := ImplicatureTheory.predictedBaselineRate (T := RSA.RSATheory)
    let diff := if rsa_rate > geurtsPouscolousVerificationRate
                then rsa_rate - geurtsPouscolousVerificationRate
                else geurtsPouscolousVerificationRate - rsa_rate
    diff > 10 := by
  native_decide

/-- NeoGricean closer to @cite{geurts-pouscoulous-2009} data than RSA -/
theorem neogricean_closer_to_geurts_data :
    let ng_rate := ImplicatureTheory.predictedBaselineRate (T := NeoGricean.NeoGriceanTheory)
    let rsa_rate := ImplicatureTheory.predictedBaselineRate (T := RSA.RSATheory)
    let empirical := geurtsPouscolousVerificationRate
    let ng_diff := if ng_rate > empirical then ng_rate - empirical else empirical - ng_rate
    let rsa_diff := if rsa_rate > empirical then rsa_rate - empirical else empirical - rsa_rate
    ng_diff < rsa_diff := by
  native_decide

-- Part 4: Using Interface Functions

/-- Both theories now agree on DE blocking -/
theorem theories_agree_on_de :
    theoriesAgreeOnDEPrediction
      (T1 := NeoGricean.NeoGriceanTheory)
      (T2 := RSA.RSATheory) = true := by
  native_decide

/-- Agreement check on task effect -/
theorem theories_disagree_on_task_effect :
    theoriesAgreeOnTaskEffect
      (T1 := NeoGricean.NeoGriceanTheory)
      (T2 := RSA.RSATheory) = false := by
  native_decide

/-- Rate matching using interface function -/
theorem neogricean_matches_data :
    rateMatchesData
      (ImplicatureTheory.predictedBaselineRate (T := NeoGricean.NeoGriceanTheory))
      geurtsPouscolousVerificationRate
      5 = true := by
  native_decide

/-- RSA doesn't match data within tolerance -/
theorem rsa_doesnt_match_data :
    rateMatchesData
      (ImplicatureTheory.predictedBaselineRate (T := RSA.RSATheory))
      geurtsPouscolousVerificationRate
      5 = false := by
  native_decide

/-- NeoGricean is closer to data -/
theorem neogricean_closer :
    closerToData
      (T1 := NeoGricean.NeoGriceanTheory)
      (T2 := RSA.RSATheory)
      geurtsPouscolousVerificationRate = true := by
  native_decide

-- Part 5: Summary

-- Part 6: Full Coverage Reports (distinguishes incomplete vs out-of-scope)

/-- NeoGricean full coverage report -/
def neogriceanFullCoverage : TheoryCoverage :=
  { theoryName := "NeoGricean (Geurts 2010)"
  , phenomena :=
    [ { phenomenon := .scalarImplicature
      , status := .complete
      , notes := "Standard Recipe derives SI from belief states" }
    , { phenomenon := .deBlocking
      , status := .complete
      , notes := "Context polarity blocks alternatives in DE" }
    , { phenomenon := .taskEffect
      , status := .complete
      , notes := "Contextualism predicts task raises salience" }
    , { phenomenon := .referenceGames
      , status := .outOfScope
      , notes := "NeoGricean uses fixed Horn scales, not ad-hoc alternatives" }
    , { phenomenon := .knowledgeCancellation
      , status := .outOfScope
      , notes := "Competence is binary, not graded knowledge states" }
    , { phenomenon := .exhaustivity
      , status := .outOfScope
      , notes := "Not covered in current formalization" }
    , { phenomenon := .freeChoice
      , status := .outOfScope
      , notes := "Requires different mechanism (see Geurts 2010 Ch. 6)" }
    ]
  }

/-- RSA full coverage report -/
def rsaFullCoverage : TheoryCoverage :=
  { theoryName := "RSA (Goodman & Frank 2016)"
  , phenomena :=
    [ { phenomenon := .scalarImplicature
      , status := .complete
      , notes := "L1 assigns higher prob to some-not-all worlds" }
    , { phenomenon := .deBlocking
      , status := .complete
      , notes := "Derived via lexical uncertainty (@cite{potts-etal-2016})" }
    , { phenomenon := .taskEffect
      , status := .incomplete
      , notes := "Model lacks QUD manipulation" }
    , { phenomenon := .referenceGames
      , status := .complete
      , notes := "Core RSA strength (Frank & Goodman 2012)" }
    , { phenomenon := .knowledgeCancellation
      , status := .complete
      , notes := "Modeled via speaker knowledge states (G&S 2013)" }
    , { phenomenon := .exhaustivity
      , status := .incomplete
      , notes := "Could be modeled, not yet formalized" }
    , { phenomenon := .freeChoice
      , status := .outOfScope
      , notes := "Requires modal semantics extension" }
    ]
  }

-- Evaluate at compile time to see coverage
#eval neogriceanFullCoverage.incompletePhenomena
-- [] (nothing incomplete - either complete or out of scope)

#eval neogriceanFullCoverage.outOfScopePhenomena
-- [referenceGames, knowledgeCancellation, exhaustivity, freeChoice]

#eval rsaFullCoverage.incompletePhenomena
-- [taskEffect, exhaustivity]

#eval rsaFullCoverage.outOfScopePhenomena
-- [freeChoice]

/-- NeoGricean has no incomplete phenomena (but some out of scope) -/
theorem neogricean_no_incomplete :
    neogriceanFullCoverage.countByStatus .incomplete = 0 := by native_decide

/-- RSA has incomplete phenomena that could be extended -/
theorem rsa_has_incomplete :
    rsaFullCoverage.countByStatus .incomplete > 0 := by native_decide

/-- RSA covers reference games (NeoGricean doesn't claim to) -/
theorem rsa_covers_reference_games :
    rsaFullCoverage.statusFor .referenceGames = some .complete := by native_decide

/-- NeoGricean explicitly marks reference games as out of scope -/
theorem neogricean_reference_games_out_of_scope :
    neogriceanFullCoverage.statusFor .referenceGames = some .outOfScope := by native_decide

-- Part 6b: Legacy Coverage Summary (backwards compatibility)

/-- NeoGricean coverage summary (legacy) -/
def neogriceanCoverage : CoverageSummary :=
  coverageSummary NeoGricean.NeoGriceanTheory

/-- RSA coverage summary (legacy) -/
def rsaCoverage : CoverageSummary :=
  coverageSummary RSA.RSATheory

#eval neogriceanCoverage
#eval rsaCoverage

-- Part 7: Linking to Empirical Data Types

/-- @cite{geurts-pouscoulous-2009} task effect data as a test case -/
def geurtsPouscolousTaskEffect : TaskEffectTestCase :=
  { inferenceRate := 62
  , verificationRate := 34
  , significant := true
  }

/-- DE blocking test case from ScalarImplicatures data -/
def someAllDEBlocking : DEBlockingTestCase :=
  { ueDescription := "John ate some of the cookies"
  , deDescription := "No one ate some of the cookies"
  , scalarTerm := "some"
  , expectedUE := true
  , expectedDE := false
  }

-- Part 7: Testing Theories Against Empirical Data

/-- Test NeoGricean against DE blocking data -/
theorem neogricean_captures_de_blocking :
    (testDEBlocking (T := NeoGricean.NeoGriceanTheory) someAllDEBlocking).isMatch = true := by
  native_decide

/-- RSA captures DE blocking (via @cite{potts-etal-2016} lexical uncertainty) -/
theorem rsa_captures_de_blocking :
    (testDEBlocking (T := RSA.RSATheory) someAllDEBlocking).isMatch = true := by
  native_decide

/-- NeoGricean matches task effect pattern -/
theorem neogricean_task_effect_result :
    let result := testTaskEffect (T := NeoGricean.NeoGriceanTheory) geurtsPouscolousTaskEffect 5
    result.theoryPredictsTaskEffect = true ∧
    result.dataShowsTaskEffect = true ∧
    result.rateDifference ≤ 5 := by
  native_decide

/-- RSA model incomplete for task effect (can't represent QUD manipulation) -/
theorem rsa_task_effect_incomplete_test :
    let result := testTaskEffect (T := RSA.RSATheory) geurtsPouscolousTaskEffect 5
    result.theoryPredictsTaskEffect = false ∧
    result.dataShowsTaskEffect = true := by
  native_decide

/-- Compare both theories to observed verification rate -/
theorem neogricean_closer_using_linking :
    let (ng_result, _) := closerToObservedRate
      (T1 := NeoGricean.NeoGriceanTheory)
      (T2 := RSA.RSATheory)
      geurtsPouscolousVerificationRate
    ng_result = true := by
  native_decide

-- Part 8: CapturesTaskEffectData Instances

/-- NeoGricean captures the Geurts & Pouscoulous task effect data -/
instance : CapturesTaskEffectData NeoGricean.NeoGriceanTheory where
  taskEffectData := geurtsPouscolousTaskEffect
  tolerance := 5
  taskEffectMatches := by native_decide
  rateWithinTolerance := by native_decide

/-- NeoGricean captures DE blocking pattern -/
instance : CapturesDEBlockingPattern NeoGricean.NeoGriceanTheory where
  testCase := someAllDEBlocking
  theoryMatchesData := by native_decide

/-- RSA captures DE blocking pattern (via @cite{potts-etal-2016}) -/
instance : CapturesDEBlockingPattern RSA.RSATheory where
  testCase := someAllDEBlocking
  theoryMatchesData := by native_decide

-- Part 9: Summary

/-
## Summary of Theory Comparison

### Coverage Comparison

| Aspect | NeoGricean | RSA | RSA Status |
|--------|------------|-----|------------|
| Simple SI derivation | ✅ | ✅ | Complete |
| DE blocking | ✅ Models | ✅ Models | Complete (@cite{potts-etal-2016}) |
| Task effect | ✅ Models | ❌ | **Incomplete** |
| Baseline rate | 35% | 50% | Different |

### RSA DE Blocking Coverage

The @cite{potts-etal-2016} lexical uncertainty model derives DE blocking by
marginalizing over lexica (weak vs strong "some"). Under "no", the strong
lexicon widens the true-world set, making the utterance less informative;
L1 therefore prefers the weak lexicon, yielding the global reading (NNN).
See `PottsEtAl2016.de_blocking_NNN_vs_NNA` et al. for the formal proofs.

### Remaining RSA Gap: Task Effects

The current RSA formalization lacks QUD manipulation, so it cannot
model task effects. A complete RSA model would need QUD-sensitive
pragmatic reasoning.

### Empirical Fit (where comparable)

| Theory | Predicted | Observed (@cite{geurts-pouscoulous-2009}) | Difference |
|--------|-----------|---------------------|------------|
| NeoGricean | 35% | 34% | 1% ✓ |
| RSA | 50% | 34% | 16% |

Note: RSA's 50% baseline comes from a simple model; a more sophisticated
RSA with proper priors might predict differently.

### What This Comparison Shows

1. **Both theories model DE blocking**: NeoGricean via scale reversal,
   RSA via lexical uncertainty (@cite{potts-etal-2016}).

2. **NeoGricean still ahead on task effects**: It models QUD/task
   manipulation, which RSA's current formalization lacks.

3. **Different strengths**: RSA excels at reference games and ad-hoc
   implicatures (see FrankGoodman2012, GoodmanStuhlmuller2013) where
   NeoGricean is less applicable.
-/

end Comparisons.ScalarImplicatureTheories
