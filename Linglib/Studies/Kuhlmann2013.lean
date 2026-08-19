import Linglib.Syntax.DependencyGrammar.Projectivity
import Linglib.Morphology.Word.Basic

/-!
# Kuhlmann 2013: Mildly Non-Projective Dependency Grammar
[kuhlmann-2013]

Figure 1's Dutch/German minimal pair — cross-serial dependencies against
nested infinitives, the same dependencies in opposite verb-cluster orders —
and the LCFRS coverage data of Tables 3-4: rule and tree loss under fan-out
and well-nestedness bounds for five languages from the CoNLL 2006 shared
task.

## Main declarations

- `Kuhlmann2013.dutchCrossSerial`, `Kuhlmann2013.germanNested`: Figure 1's
  minimal pair, separated by gap degree
- `Kuhlmann2013.LCFRSCoverage`: rule/tree loss row under fan-out bounds
- `Kuhlmann2013.arabic`, `Kuhlmann2013.czech`, `Kuhlmann2013.danish`,
  `Kuhlmann2013.slovene`, `Kuhlmann2013.turkish`: Tables 3-4 rows
- `Kuhlmann2013.fanout2_good_coverage`: fan-out ≤ 2 loses under 1% of trees
  in every language
-/

namespace Kuhlmann2013

open DependencyGrammar
open Morphology (Word)

/-! ### Figure 1: cross-serial against nested

The same dependencies in opposite verb-cluster orders. The Dutch order is
non-projective and the German one is not, so the pair separates the two
regimes while holding the dependency structure fixed. -/

/-- Dutch cross-serial: "dat Jan Piet Marie zag helpen lezen". -/
def dutchCrossSerial : Graph 7 :=
  .ofArcs
    [Word.mk' "dat" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "zag" .VERB, Word.mk' "helpen" .VERB,
     Word.mk' "lezen" .VERB]
    0
    [(0, 4, .dep), (4, 1, .nsubj), (4, 5, .xcomp),
     (5, 2, .nsubj), (5, 6, .xcomp), (6, 3, .nsubj)]

/-- German nested: "dass Jan Piet Marie lesen helfen sah". -/
def germanNested : Graph 7 :=
  .ofArcs
    [Word.mk' "dass" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "lesen" .VERB, Word.mk' "helfen" .VERB,
     Word.mk' "sah" .VERB]
    0
    [(0, 6, .dep), (6, 1, .nsubj), (6, 5, .xcomp),
     (5, 2, .nsubj), (5, 4, .xcomp), (4, 3, .nsubj)]

example : dutchCrossSerial.IsTree := by decide
example : germanNested.IsTree := by decide

/-- The cross-serial order is non-projective and the nested order is not. -/
example : ¬ dutchCrossSerial.IsProjective ∧ germanNested.IsProjective := by decide

/-- One gap in the Dutch order, none in the German one: block-degree 2
    against block-degree 1, the fan-out of the extracted LCFRS rule. -/
example : dutchCrossSerial.gapDegree = 1 ∧ germanNested.gapDegree = 0 := by decide

/-- Cross-serial dependencies stay well-nested; they are not planar. -/
example : dutchCrossSerial.IsWellNested ∧ ¬ dutchCrossSerial.IsPlanar := by decide

/-- The Dutch fixture as a bundled `Tree`: the dominance-order API applies
    with no side conditions. -/
def dutchTree : Tree 7 := .mk' dutchCrossSerial

example : (⊥ : DominanceOrder dutchTree.toGraph) = 0 := by decide
example : Order.pred (5 : DominanceOrder dutchTree.toGraph) = 4 := by decide

/-! ### Tables 3-4: LCFRS coverage -/

/-- [kuhlmann-2013] Table 3: rule/tree loss under fan-out bounds.
    Five languages from the CoNLL 2006 shared task. -/
structure LCFRSCoverage where
  name : String
  totalRules : Nat
  totalTrees : Nat
  /-- Rules lost at fan-out = 1 (projective only) -/
  rulesLostFanout1 : Nat
  /-- Trees lost at fan-out = 1 -/
  treesLostFanout1 : Nat
  /-- Rules lost at fan-out ≤ 2 -/
  rulesLostFanout2 : Nat
  /-- Trees lost at fan-out ≤ 2 -/
  treesLostFanout2 : Nat
  /-- Rules lost when also requiring well-nestedness (with fan-out ≤ 2) -/
  rulesLostWN : Nat
  /-- Trees lost when also requiring well-nestedness -/
  treesLostWN : Nat
  deriving Repr

/-- Arabic row of [kuhlmann-2013] Tables 3-4. -/
def arabic : LCFRSCoverage :=
  { name := "Arabic", totalRules := 5839, totalTrees := 1460
    rulesLostFanout1 := 411, treesLostFanout1 := 163
    rulesLostFanout2 := 1, treesLostFanout2 := 1
    rulesLostWN := 2, treesLostWN := 2 }

/-- Czech row of [kuhlmann-2013] Tables 3-4. -/
def czech : LCFRSCoverage :=
  { name := "Czech", totalRules := 1322111, totalTrees := 72703
    rulesLostFanout1 := 22283, treesLostFanout1 := 16831
    rulesLostFanout2 := 328, treesLostFanout2 := 312
    rulesLostWN := 407, treesLostWN := 382 }

/-- Danish row of [kuhlmann-2013] Tables 3-4. -/
def danish : LCFRSCoverage :=
  { name := "Danish", totalRules := 99576, totalTrees := 5190
    rulesLostFanout1 := 1229, treesLostFanout1 := 811
    rulesLostFanout2 := 11, treesLostFanout2 := 9
    rulesLostWN := 17, treesLostWN := 15 }

/-- Slovene row of [kuhlmann-2013] Tables 3-4. -/
def slovene : LCFRSCoverage :=
  { name := "Slovene", totalRules := 30284, totalTrees := 1534
    rulesLostFanout1 := 530, treesLostFanout1 := 340
    rulesLostFanout2 := 14, treesLostFanout2 := 11
    rulesLostWN := 17, treesLostWN := 13 }

/-- Turkish row of [kuhlmann-2013] Tables 3-4. -/
def turkish : LCFRSCoverage :=
  { name := "Turkish", totalRules := 62507, totalTrees := 4997
    rulesLostFanout1 := 924, treesLostFanout1 := 580
    rulesLostFanout2 := 54, treesLostFanout2 := 33
    rulesLostWN := 68, treesLostWN := 43 }

/-- Fan-out ≤ 2 (block-degree ≤ 2) loses very few trees across all languages
    ([kuhlmann-2013] Tables 3-4). -/
theorem fanout2_good_coverage :
    arabic.treesLostFanout2 ≤ 1 ∧
    czech.treesLostFanout2 * 100 / czech.totalTrees < 1 ∧
    danish.treesLostFanout2 * 100 / danish.totalTrees < 1 ∧
    slovene.treesLostFanout2 * 100 / slovene.totalTrees < 1 ∧
    turkish.treesLostFanout2 * 100 / turkish.totalTrees < 1 := by decide

end Kuhlmann2013
