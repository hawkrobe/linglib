import Mathlib.Data.Rat.Defs

/-!
# Paradigms: forms over ordered cells
[ackerman-malouf-2013] [bobaljik-2012]

The morphologist's primary observable: a **paradigm** assigns a surface
form to each of `n` linearly ordered cells. One type serves both
research lines that consume it — realization-pattern typology (*ABA and
contiguity, `Morphology/Paradigm/Contiguity.lean`) and paradigm-cell
information theory (implicative structure and complexity,
`Morphology/Paradigm/Complexity.lean`). [ackerman-malouf-2013]'s
inflection classes are paradigms with frequency weights
(`ParadigmSystem`); [bobaljik-2012]-style realization patterns are
paradigms over graded cells.

## Main declarations

* `Paradigm n F` — assignment of a form to each of the `n` cells
* `ParadigmSystem n Form` — paradigms with frequency weights, organized
  by inflection class
* `cellDistribution`, `jointCellDistribution` — empirical form
  distributions at cells
* `eComplexity` — count of inflection classes (Ackerman-Malouf
  E-complexity)
-/

namespace Morphology

/-- A **paradigm** over `n` linearly ordered cells: the form occupying
each cell. The single carrier for realization patterns
([bobaljik-2012]'s AAA/ABB/ABC shapes; see
`Morphology/Paradigm/Contiguity.lean`) and for inflection-class rows
([ackerman-malouf-2013]; a weighted system of paradigms is a
`ParadigmSystem`). -/
abbrev Paradigm (n : ℕ) (F : Type*) := Fin n → F

/-- A paradigm system: paradigms (inflection classes) paired with
frequency weights. -/
structure ParadigmSystem (numCells : ℕ) (Form : Type*) where
  entries : List (Paradigm numCells Form × ℚ)

/-- Group a tagged list by key, summing associated ℚ values. -/
def groupBySum {α : Type*} [DecidableEq α] (tagged : List (α × ℚ)) : List (α × ℚ) :=
  tagged.foldl (λ acc (key, f) =>
    match acc.find? (λ (k, _) => k = key) with
    | some _ => acc.map (λ (k, p) => if k = key then (k, p + f) else (k, p))
    | none => acc ++ [(key, f)]
  ) []

/-- Empirical distribution of forms at cell `c`: pairs each surface form with
    the total frequency of inflection classes realizing it at `c`. -/
def ParadigmSystem.cellDistribution {n : ℕ} {Form : Type*} [DecidableEq Form]
    (ps : ParadigmSystem n Form) (c : Fin n) :
    List (Form × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => (ic c, f))

/-- Joint empirical distribution of forms at cell pair `(ci, cj)`. -/
def ParadigmSystem.jointCellDistribution {n : ℕ} {Form : Type*} [DecidableEq Form]
    (ps : ParadigmSystem n Form) (ci cj : Fin n) :
    List ((Form × Form) × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => ((ic ci, ic cj), f))

/-- E-complexity ([ackerman-malouf-2013]): the number of inflection
    classes in the paradigm system. -/
def ParadigmSystem.eComplexity {n : ℕ} {Form : Type*}
    (ps : ParadigmSystem n Form) : Nat :=
  ps.entries.length

end Morphology
