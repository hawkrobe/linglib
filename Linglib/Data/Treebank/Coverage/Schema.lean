import Mathlib.Data.Rat.Defs

/-!
# Treebank coverage of non-projectivity constraints: schema

Typed schema for the per-treebank statistics a paper reports on how many of a treebank's
dependency trees, or of the grammar rules extracted from them, satisfy a constraint on
non-projectivity: projectivity, a bound on the gap degree, well-nestedness, planarity, or a
conjunction of these. Generated rows live in `Data/Treebank/Coverage/<Paper>.lean`, emitted
from the canonical `<Paper>.json` by `scripts/gen_treebank_coverage.py`.

This is data: it imports nothing from `Linglib/` and states no theorems. A row records the
covered quantity at the precision the paper prints, either as a count or as a percentage in
hundredths, so that consumers compute over it by `decide`; `Row.coverage` is the common
rational reading. The language code is a Glottolog code, an annotation for cross-study joins
rather than a printed value.

## References

* [kuhlmann-2013]
* [kuhlmann-nivre-2006]
-/

namespace Data.Treebank.Coverage

/-- A constraint on non-projectivity whose coverage a paper measures. -/
inductive Constraint where
  /-- Projectivity: gap degree 0, block-degree 1, fan-out 1. -/
  | projective
  /-- Gap degree exactly `k`. -/
  | gapDegreeEq (k : ℕ)
  /-- Gap degree at most `k`, block-degree and fan-out at most `k + 1`. -/
  | gapDegreeLe (k : ℕ)
  /-- Well-nestedness. -/
  | wellNested
  /-- Planarity. -/
  | planar
  /-- Gap degree at most `k` together with well-nestedness. -/
  | gapDegreeLeWellNested (k : ℕ)
  deriving DecidableEq, Repr

/-- What the coverage counts. -/
inductive Item where
  /-- Dependency trees of the treebank. -/
  | trees
  /-- Grammar rules extracted from the treebank, counted as tokens. -/
  | rules
  deriving DecidableEq, Repr

/-- How the paper prints the covered quantity. -/
inductive Scale where
  /-- A count of covered items. -/
  | count
  /-- A percentage of the total, in hundredths of a percent. -/
  | percentHundredths
  deriving DecidableEq, Repr

/-- One treebank's coverage under one constraint. -/
structure Row where
  /-- The treebank or language name as the paper prints it. -/
  treebank : String
  /-- The Glottolog code of the treebank's language. -/
  language : String
  /-- What is counted. -/
  item : Item
  /-- The number of items in the treebank. -/
  total : ℕ
  /-- The constraint. -/
  constraint : Constraint
  /-- The scale of `value`. -/
  scale : Scale
  /-- The covered quantity at the paper's scale. -/
  value : ℕ
  deriving DecidableEq, Repr

/-- The covered proportion of the treebank. -/
def Row.coverage (r : Row) : ℚ :=
  match r.scale with
  | .count => r.value / r.total
  | .percentHundredths => r.value / 10000

end Data.Treebank.Coverage
