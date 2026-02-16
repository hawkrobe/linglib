/-!
# Treebank Non-Projectivity Data

Empirical data on non-projective structures in dependency treebanks.

## Sources

- Kuhlmann & Nivre (2006). Mildly Non-Projective Dependency Structures.
  COLING/ACL 2006, Table 1.
- Kuhlmann (2013). Mildly Non-Projective Dependency Grammar.
  Computational Linguistics 39(2), Tables 3-4.
-/

namespace DepGrammar.Phenomena

-- ============================================================================
-- §1: Treebank Coverage (Kuhlmann & Nivre 2006, Table 1)
-- ============================================================================

/-- Treebank coverage data from Kuhlmann & Nivre (2006), Table 1.
    Percentages scaled x100 for Nat arithmetic. -/
structure TreebankCoverage where
  name : String
  totalTrees : Nat
  /-- Percentage x100 of trees at each gap degree -/
  gapDeg0 : Nat   -- projective (x100)
  gapDeg1 : Nat
  gapDeg2 : Nat
  /-- Percentage x100 of well-nested trees -/
  wellNested : Nat
  /-- Percentage x100 of planar trees -/
  planar : Nat
  deriving Repr

def pdt : TreebankCoverage :=
  { name := "Prague Dependency Treebank"
    totalTrees := 73088
    gapDeg0 := 7685   -- 76.85%
    gapDeg1 := 2272   -- 22.72%
    gapDeg2 := 42      -- 0.42%
    wellNested := 9989 -- 99.89%
    planar := 8216     -- 82.16%
  }

def ddt : TreebankCoverage :=
  { name := "Danish Dependency Treebank"
    totalTrees := 4393
    gapDeg0 := 8495   -- 84.95%
    gapDeg1 := 1489   -- 14.89%
    gapDeg2 := 16      -- 0.16%
    wellNested := 9989 -- 99.89%
    planar := 8641     -- 86.41%
  }

-- ============================================================================
-- §2: LCFRS Coverage (Kuhlmann 2013, Tables 3-4)
-- ============================================================================

/-- Kuhlmann (2013) Table 3: rule/tree loss under fan-out bounds.
    Five languages from the CoNLL 2006 shared task. -/
structure LCFRSCoverage where
  name : String
  totalRules : Nat
  totalTrees : Nat
  /-- Rules lost at fan-out = 1 (projective only) -/
  rulesLostFanout1 : Nat
  /-- Trees lost at fan-out = 1 -/
  treesLostFanout1 : Nat
  /-- Rules lost at fan-out <= 2 -/
  rulesLostFanout2 : Nat
  /-- Trees lost at fan-out <= 2 -/
  treesLostFanout2 : Nat
  /-- Rules lost when also requiring well-nestedness (with fan-out <= 2) -/
  rulesLostWN : Nat
  /-- Trees lost when also requiring well-nestedness -/
  treesLostWN : Nat
  deriving Repr

def arabic : LCFRSCoverage :=
  { name := "Arabic", totalRules := 5839, totalTrees := 1460
    rulesLostFanout1 := 411, treesLostFanout1 := 163
    rulesLostFanout2 := 1, treesLostFanout2 := 1
    rulesLostWN := 2, treesLostWN := 2 }

def czech : LCFRSCoverage :=
  { name := "Czech", totalRules := 1322111, totalTrees := 72703
    rulesLostFanout1 := 22283, treesLostFanout1 := 16831
    rulesLostFanout2 := 328, treesLostFanout2 := 312
    rulesLostWN := 407, treesLostWN := 382 }

def danish : LCFRSCoverage :=
  { name := "Danish", totalRules := 99576, totalTrees := 5190
    rulesLostFanout1 := 1229, treesLostFanout1 := 811
    rulesLostFanout2 := 11, treesLostFanout2 := 9
    rulesLostWN := 17, treesLostWN := 15 }

def slovene : LCFRSCoverage :=
  { name := "Slovene", totalRules := 30284, totalTrees := 1534
    rulesLostFanout1 := 530, treesLostFanout1 := 340
    rulesLostFanout2 := 14, treesLostFanout2 := 11
    rulesLostWN := 17, treesLostWN := 13 }

def turkish : LCFRSCoverage :=
  { name := "Turkish", totalRules := 62507, totalTrees := 4997
    rulesLostFanout1 := 924, treesLostFanout1 := 580
    rulesLostFanout2 := 54, treesLostFanout2 := 33
    rulesLostWN := 68, treesLostWN := 43 }

end DepGrammar.Phenomena
