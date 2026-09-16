import Mathlib.Data.Rat.Defs
import Linglib.Core.Data.Setoid.Basic

/-!
# Paradigms: forms over ordered cells

The morphologist's primary observable: a **paradigm** assigns a surface
form to each of `n` linearly ordered cells; its **syncretism** is the
kernel setoid of that assignment (`syncretism`). One type serves both
research lines that consume it — realization-pattern typology (*ABA and
contiguity, `Morphology/Paradigm/Contiguity.lean`) and paradigm-cell
information theory (implicative structure and complexity,
`Morphology/Paradigm/Complexity.lean`). [ackerman-malouf-2013]'s
inflection classes are paradigms with frequency weights
(`ParadigmSystem`); [bobaljik-2012]-style realization patterns are
paradigms over graded cells.

## Main declarations

* `Paradigm n F` — assignment of a form to each of the `n` cells
* `syncretism` — the kernel setoid of a form assignment, `Setoid.ker`
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

/-- The **syncretism** relation of a form assignment `p`: two cells are
syncretic iff `p` assigns them the same form. Exactly the kernel setoid
`Setoid.ker p`; its equivalence classes are the syncretism patterns, and
two assignments have the same pattern iff their syncretisms agree. -/
abbrev syncretism {Cell F : Type*} (p : Cell → F) : Setoid Cell := Setoid.ker p

/-- Two form assignments have the same syncretism pattern iff they identify
the same pairs of cells. -/
theorem syncretism_eq_iff {Cell F G : Type*} {p : Cell → F} {q : Cell → G} :
    syncretism p = syncretism q ↔ ∀ a b, p a = p b ↔ q a = q b := by
  simp only [syncretism, Setoid.ext_iff, Setoid.ker_def]

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
