/-!
# Kuhlmann 2013: Mildly Non-Projective Dependency Grammar
[kuhlmann-2013]

LCFRS coverage data from [kuhlmann-2013] Tables 3-4 (Computational Linguistics
39(2)): rule and tree loss under fan-out and well-nestedness bounds for five
languages from the CoNLL 2006 shared task.

## Main declarations

- `Kuhlmann2013.LCFRSCoverage`: rule/tree loss row under fan-out bounds
- `Kuhlmann2013.arabic`, `Kuhlmann2013.czech`, `Kuhlmann2013.danish`,
  `Kuhlmann2013.slovene`, `Kuhlmann2013.turkish`: Tables 3-4 rows
- `Kuhlmann2013.fanout2_good_coverage`: fan-out ≤ 2 loses under 1% of trees in
  every language
-/

namespace Kuhlmann2013

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
