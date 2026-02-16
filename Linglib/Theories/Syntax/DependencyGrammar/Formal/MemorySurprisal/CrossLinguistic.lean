import Linglib.Theories.Syntax.DependencyGrammar.Formal.MemorySurprisal.Basic
import Linglib.Phenomena.WordOrder.HahnDegenFutrell2021
import Linglib.Phenomena.DependencyLength.FutrellEtAl2020
import Linglib.Theories.Syntax.DependencyGrammar.Formal.HarmonicOrder

/-!
# Study 2: Crosslinguistic Word-Order Efficiency (54 Languages)

Hahn et al. (2021) Study 2: for 54 languages from Universal Dependencies,
real word orders achieve more efficient memory-surprisal trade-offs than
grammar-preserving random baselines (50/54 = 93%). The 4 exceptions
(Latvian, North Sami, Polish, Slovak) all have high word-order freedom.

## Data Source

AUC values computed from <https://github.com/m-hahn/memory-surprisal>
(`results/tradeoff/listener-curve-auc.tsv`). G values from SI Figure 2.

## Bridges

- → `Phenomena/WordOrder/HahnDegenFutrell2021`: raw 54-language efficiency data
- → `Phenomena/DependencyLength/FutrellEtAl2020`: shared languages across datasets
- → `Formal/HarmonicOrder`: DLM harmonic order prediction consistent with efficiency

## References

- Hahn, M., Degen, J. & Futrell, R. (2021). Study 2 (§5).
- Futrell, R., Levy, R. & Gibson, E. (2020). Dependency locality. Language 96(2).
-/

namespace DepGrammar.MemorySurprisal.CrossLinguistic

open Phenomena.WordOrder.HahnDegenFutrell2021
open Phenomena.DependencyLength.FutrellEtAl2020

-- ============================================================================
-- Core Result
-- ============================================================================

/-- 50 out of 54 languages (93%) have more efficient word orders than baselines. -/
theorem efficient_tradeoff_hypothesis_holds :
    efficientLanguages.length = 50 ∧ allLanguages.length = 54 :=
  ⟨by native_decide, by native_decide⟩

/-- The 4 exception languages all have high branching direction entropy (> 700).

High branching direction entropy means the language has very free word order.
With many acceptable orderings, the optimization pressure is weak:
random baselines are already close to the real language. -/
theorem exceptions_have_high_entropy :
    exceptionLanguages.all (·.branchDirEntropy1000 > 700) = true := by native_decide

/-- Exception languages have higher mean entropy than efficient languages. -/
theorem exceptions_higher_entropy :
    meanEntropy exceptionLanguages > meanEntropy efficientLanguages := by native_decide

-- ============================================================================
-- Bridge to FutrellEtAl2020 (DLM crosslinguistic data)
-- ============================================================================

/-! ### Shared Languages

Languages appearing in both Futrell et al. (2020) DLM dataset and
Hahn et al. (2021) efficiency dataset. These form the empirical
bridge between structural dependency length and information-theoretic
efficiency. -/

/-- ISO codes appearing in Futrell et al. (2020)'s 32-language dataset. -/
def futrellIsoCodes : List String :=
  Phenomena.DependencyLength.FutrellEtAl2020.languages.map (·.isoCode)

/-- ISO codes appearing in Hahn et al. (2021)'s 54-language dataset. -/
def hahnIsoCodes : List String :=
  allLanguages.map (·.isoCode)

/-- Languages in both datasets (by ISO code). -/
def sharedIsoCodes : List String :=
  futrellIsoCodes.filter (hahnIsoCodes.contains ·)

/-- At least 20 languages appear in both datasets. -/
theorem many_shared_languages :
    sharedIsoCodes.length ≥ 20 := by native_decide

/-- All but one shared language (Polish) are efficient in Hahn et al.

Polish is both in Futrell et al.'s DLM dataset and among the 4 exceptions
in Hahn et al. — its free word order means baselines are already close to
the real language in memory-surprisal efficiency, even though it shows
the expected DLM pattern structurally. -/
theorem shared_languages_mostly_efficient :
    (sharedIsoCodes.filter (λ iso =>
      (allLanguages.filter (·.isoCode == iso)).all (·.moreEfficient)
    )).length ≥ sharedIsoCodes.length - 1 := by native_decide

/-- Polish is the only shared language that is an exception. -/
theorem polish_only_shared_exception :
    (sharedIsoCodes.filter (λ iso =>
      (allLanguages.filter (·.isoCode == iso)).any (! ·.moreEfficient)
    )) = ["pl"] := by native_decide

-- ============================================================================
-- Bridge to HarmonicOrder (DLM explains head-direction generalization)
-- ============================================================================

/-! ### Harmonic Consistency ↔ Efficiency

The DLM explanation for the head-direction generalization (Gibson 2025,
formalized in HarmonicOrder.lean) predicts that languages with consistent
head direction have shorter dependencies. Hahn et al. (2021) show that
languages with shorter dependencies also have more efficient trade-offs.

This forms a chain: harmonic consistency → short deps → efficient trade-off. -/

/-- The DLM harmonic order prediction holds (from HarmonicOrder.lean). -/
theorem harmonic_dlm_holds :
    DepGrammar.HarmonicOrder.dlmPredictsHarmonicCheaper = true := by native_decide

/-- Strongly head-final languages (low branching entropy) are all efficient.

Languages with low branching direction entropy have rigid word order,
consistent with strong head-direction consistency. All are efficient. -/
theorem rigid_order_languages_efficient :
    (allLanguages.filter (·.branchDirEntropy1000 < 400)).all (·.moreEfficient) = true := by
  native_decide

-- ============================================================================
-- Word-Order Freedom and Optimization
-- ============================================================================

/-- All 4 exceptions have entropy ≥ 720 (in the top quartile).

This is the key qualitative finding: word-order freedom weakens
optimization pressure. -/
theorem exceptions_all_high_entropy :
    exceptionLanguages.all (·.branchDirEntropy1000 ≥ 720) = true := by native_decide

/-- But not all high-entropy languages are exceptions: Russian, Croatian, etc.
have high entropy but are still efficient. Word-order freedom is necessary
but not sufficient for being an exception. -/
theorem high_entropy_not_sufficient :
    (allLanguages.filter (·.branchDirEntropy1000 ≥ 720)).any (·.moreEfficient) = true := by
  native_decide

end DepGrammar.MemorySurprisal.CrossLinguistic
