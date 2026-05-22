import Linglib.Theories.Syntax.DependencyGrammar.Formal.NonProjective
import Linglib.Phenomena.WordOrder.NonProjectivity

/-!
# Treebank Non-Projectivity Constraints
@cite{kuhlmann-nivre-2006} @cite{kuhlmann-2013}

Connects the structural theory of non-projectivity to empirical treebank data on the prevalence of
well-nestedness, gap degree, and fan-out constraints.

## Key Results

- Well-nestedness covers ≥99% of both PDT and DDT (@cite{kuhlmann-nivre-2006} Table 1)
- Gap degree ≤ 1 covers ≥99% of both treebanks
- Planarity is insufficient (covers far less than well-nestedness)
- Fan-out ≤ 2 (block-degree ≤ 2) loses very few trees across all languages
-/

namespace KuhlmannNivre2006

open Phenomena.WordOrder.NonProjectivity

-- ============================================================================
-- Empirical Data Verification
-- (Data in Phenomena/WordOrder/NonProjectivity.lean)
-- ============================================================================

/-- Well-nestedness covers ≥99% of both treebanks (@cite{kuhlmann-nivre-2006} Table 1). -/
theorem wellNested_near_universal :
    pdt.wellNested ≥ 9900 ∧ ddt.wellNested ≥ 9900 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Gap degree ≤ 1 covers ≥99% of both treebanks. -/
theorem gapDeg_leq1_sufficient :
    pdt.gapDeg0 + pdt.gapDeg1 ≥ 9900 ∧
    ddt.gapDeg0 + ddt.gapDeg1 ≥ 9900 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Planarity covers far less than well-nestedness. -/
theorem planarity_insufficient :
    pdt.planar < pdt.wellNested ∧
    ddt.planar < ddt.wellNested := by
  exact ⟨by native_decide, by native_decide⟩

/-- Fan-out ≤ 2 (block-degree ≤ 2) loses very few trees across all languages
    (@cite{kuhlmann-2013} Tables 3-4). -/
theorem fanout2_good_coverage :
    arabic.treesLostFanout2 ≤ 1 ∧
    czech.treesLostFanout2 * 100 / czech.totalTrees < 1 ∧
    danish.treesLostFanout2 * 100 / danish.totalTrees < 1 ∧
    slovene.treesLostFanout2 * 100 / slovene.totalTrees < 1 ∧
    turkish.treesLostFanout2 * 100 / turkish.totalTrees < 1 := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide⟩

end KuhlmannNivre2006
