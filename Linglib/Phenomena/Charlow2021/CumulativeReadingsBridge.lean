import Linglib.Phenomena.Charlow2021.Data
import Linglib.Theories.DynamicSemantics.Systems.DynamicGQ.UpdateTheoretic
import Linglib.Theories.DynamicSemantics.Effects.Nondeterminism.PointwiseUpdate

/-!
# Charlow 2021: Cumulative Readings Bridge

Connects the empirical data (Scenario A/B) to the dynamic GQ theory.
Verifies that:
1. The pointwise system overgenerates (predicts TRUE for Scenario B)
2. The update-theoretic system is correct (predicts FALSE for Scenario B)
3. The cumulative reading is strictly stronger than pseudo-cumulative

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
-/

namespace Phenomena.Charlow2021.CumulativeReadings

open Phenomena.Charlow2021.Data

/-- The pointwise system overgenerates: it predicts Scenario B is TRUE
    under the pseudo-cumulative reading.
    This re-exports the observation as a bridge theorem. -/
theorem pointwise_overgenerates :
    pseudoCumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = true :=
  scenarioB_pseudo_true

/-- The update-theoretic system is correct: Scenario B is FALSE under
    the cumulative reading. -/
theorem update_correct :
    cumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = false :=
  scenarioB_cumulative_false

/-- Both readings agree on Scenario A (both true). -/
theorem both_agree_scenarioA :
    cumulativeReading scenarioA_saw allBoys3 allMovies5 3 5 = true ∧
    pseudoCumulativeReading scenarioA_saw allBoys3 allMovies5 3 5 = true :=
  ⟨scenarioA_cumulative_true, scenarioA_pseudo_true⟩

/-- The cumulative reading is strictly stronger than pseudo-cumulative:
    if cumulative is true then pseudo-cumulative is true, but not vice versa.
    Witnessed by Scenario B. -/
theorem cumulative_strictly_stronger :
    (cumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = false) ∧
    (pseudoCumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = true) :=
  ⟨scenarioB_cumulative_false, scenarioB_pseudo_true⟩

end Phenomena.Charlow2021.CumulativeReadings
