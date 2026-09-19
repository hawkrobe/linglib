import Mathlib.Data.Finset.Image
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
* `formsAt` — the form assignment of an inventory: the forms its items offer for each cell
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

/-! ### The paradigm of an inventory -/

section FormsAt

variable {ι Cell F : Type*} [DecidableEq Cell] [DecidableEq F]
  {cells : ι → Finset Cell} {form : ι → F} {I J : Finset ι} {c : Cell} {f : F}

/-- The forms an inventory `I` offers for the cell `c`, where the item `i` has the form `form i`
and realizes the cells `cells i`. A cell no item realizes gets `∅` and an overabundant cell
several forms, and `syncretism (formsAt cells form I)` relates the cells the inventory does not
distinguish. -/
def formsAt (cells : ι → Finset Cell) (form : ι → F) (I : Finset ι) (c : Cell) : Finset F :=
  (I.filter (c ∈ cells ·)).image form

theorem mem_formsAt : f ∈ formsAt cells form I c ↔ ∃ i ∈ I, c ∈ cells i ∧ form i = f := by
  simp [formsAt, and_assoc]

@[gcongr]
theorem formsAt_mono (h : I ⊆ J) (c : Cell) :
    formsAt cells form I c ⊆ formsAt cells form J c :=
  Finset.image_subset_image (Finset.filter_subset_filter _ h)

theorem formsAt_union [DecidableEq ι] (I J : Finset ι) (c : Cell) :
    formsAt cells form (I ∪ J) c = formsAt cells form I c ∪ formsAt cells form J c := by
  simp [formsAt, Finset.filter_union, Finset.image_union]

end FormsAt

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
