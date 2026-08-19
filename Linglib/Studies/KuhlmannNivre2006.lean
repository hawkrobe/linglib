import Linglib.Syntax.DependencyGrammar.Projectivity
import Linglib.Morphology.Word.Basic

/-!
# Kuhlmann & Nivre 2006: Mildly Non-Projective Dependency Structures
[kuhlmann-nivre-2006]

Figure 2a's planar-but-not-projective structure, and the treebank coverage
data of Table 1: prevalence of gap degree, well-nestedness, and planarity in
the Prague and Danish dependency treebanks.

## Main declarations

- `KuhlmannNivre2006.planarNotProjective`: Figure 2a, adapted to a single
  root, separating planarity from projectivity
- `KuhlmannNivre2006.TreebankCoverage`: coverage row (percentages scaled x100)
- `KuhlmannNivre2006.pdt`, `KuhlmannNivre2006.ddt`: Table 1 rows
- `KuhlmannNivre2006.wellNested_near_universal`: well-nestedness covers ≥99%
  of both treebanks
- `KuhlmannNivre2006.gapDeg_leq1_sufficient`: gap degree ≤ 1 covers ≥99% of
  both treebanks
- `KuhlmannNivre2006.planarity_insufficient`: planarity covers less than
  well-nestedness
-/

namespace KuhlmannNivre2006

open DependencyGrammar
open Morphology (Word)

/-! ### Figure 2a: planar but not projective -/

/-- Planar but not projective: no crossing links, yet the positions
    dominated by 0 are `{0, 3}`, which is not an interval.

    Figure 2a's own witness is a forest, with the skipped position a second
    root; this adapts it to a single root. The root sits at position 2,
    inside the gap, and it has to: the paper observes that in a planar tree
    every gap contains the root, so a planar tree rooted at a sentence
    boundary is projective. -/
def planarNotProjective : Graph 4 :=
  .ofArcs
    [Word.mk' "w0" .X, Word.mk' "w1" .X, Word.mk' "w2" .X, Word.mk' "w3" .X]
    2
    [(2, 0, .dep), (2, 1, .dep), (0, 3, .dep)]

example : planarNotProjective.IsTree := by decide

/-- Planarity is strictly weaker than projectivity. -/
example : planarNotProjective.IsPlanar ∧ ¬ planarNotProjective.IsProjective := by
  decide

/-- Planarity is exactly having no crossings, so the count is zero even
    though the structure is not projective. -/
example : planarNotProjective.crossings = 0 := by decide

/-- The root lies strictly inside the gap of position 0. -/
example : (0 : Fin 4) < planarNotProjective.root ∧
    planarNotProjective.root < 3 := by decide

/-! ### Table 1: treebank coverage -/

/-- Treebank coverage data from [kuhlmann-nivre-2006], Table 1.
    Percentages scaled x100 for Nat arithmetic. -/
structure TreebankCoverage where
  name : String
  totalTrees : Nat
  /-- Percentage x100 of trees at gap degree 0 (projective) -/
  gapDeg0 : Nat
  /-- Percentage x100 of trees at gap degree 1 -/
  gapDeg1 : Nat
  /-- Percentage x100 of trees at gap degree 2 -/
  gapDeg2 : Nat
  /-- Percentage x100 of well-nested trees -/
  wellNested : Nat
  /-- Percentage x100 of planar trees -/
  planar : Nat
  deriving Repr

/-- Prague Dependency Treebank row of [kuhlmann-nivre-2006] Table 1. -/
def pdt : TreebankCoverage :=
  { name := "Prague Dependency Treebank"
    totalTrees := 73088
    gapDeg0 := 7685   -- 76.85%
    gapDeg1 := 2272   -- 22.72%
    gapDeg2 := 42      -- 0.42%
    wellNested := 9989 -- 99.89%
    planar := 8216     -- 82.16%
  }

/-- Danish Dependency Treebank row of [kuhlmann-nivre-2006] Table 1. -/
def ddt : TreebankCoverage :=
  { name := "Danish Dependency Treebank"
    totalTrees := 4393
    gapDeg0 := 8495   -- 84.95%
    gapDeg1 := 1489   -- 14.89%
    gapDeg2 := 16      -- 0.16%
    wellNested := 9989 -- 99.89%
    planar := 8641     -- 86.41%
  }

/-- Well-nestedness covers ≥99% of both treebanks ([kuhlmann-nivre-2006] Table 1). -/
theorem wellNested_near_universal :
    pdt.wellNested ≥ 9900 ∧ ddt.wellNested ≥ 9900 := by decide

/-- Gap degree ≤ 1 covers ≥99% of both treebanks. -/
theorem gapDeg_leq1_sufficient :
    pdt.gapDeg0 + pdt.gapDeg1 ≥ 9900 ∧
    ddt.gapDeg0 + ddt.gapDeg1 ≥ 9900 := by decide

/-- Planarity covers far less than well-nestedness. -/
theorem planarity_insufficient :
    pdt.planar < pdt.wellNested ∧
    ddt.planar < ddt.wellNested := by decide

end KuhlmannNivre2006
