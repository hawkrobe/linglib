module

public import Mathlib.Data.Finset.Image
public import Linglib.Core.Data.Setoid.Basic

/-!
# Paradigms: forms over ordered cells

The morphologist's primary observable: a **paradigm** assigns a surface
form to each of `n` linearly ordered cells; its **syncretism** is the
kernel setoid of that assignment, `Setoid.ker p`, whose classes are the cells
sharing a form, decidable over finitely many cells by the instances of
`Core/Data/Setoid/Basic.lean`. One type serves both
research lines that consume it — realization-pattern typology (*ABA and
contiguity, `Morphology/Paradigm/Contiguity.lean`) and paradigm-cell
information theory (implicative structure and complexity,
`Morphology/Paradigm/Complexity.lean`). A **paradigm system** is a finite
family of paradigms indexed by its inflection classes, an inflection-class
table read as a matrix whose rows are the classes
([ackerman-malouf-2013]; [bobaljik-2012]-style realization patterns are
single paradigms over graded cells). Class probabilities — uniform in
[ackerman-malouf-2013]'s computations, type frequencies in its general
definitions — are a `MeasureTheory.Measure` on the classes, a parameter of
the entropy statements in `Complexity.lean`, never a field of the data.

## Main declarations

* `Paradigm n F` — assignment of a form to each of the `n` cells
* `formsAt` — the form assignment of an inventory: the forms its items offer for each cell
* `ParadigmSystem D n Form` — a family of paradigms indexed by the inflection classes `D`
-/

@[expose] public section

namespace Morphology

/-- A **paradigm** over `n` linearly ordered cells assigns the form occupying
each cell. The single carrier for realization patterns
([bobaljik-2012]'s AAA/ABB/ABC shapes; see
`Morphology/Paradigm/Contiguity.lean`) and for inflection-class rows
([ackerman-malouf-2013]; a family of them is a `ParadigmSystem`). -/
abbrev Paradigm (n : ℕ) (F : Type*) := Fin n → F

/-! ### The paradigm of an inventory -/

section FormsAt

variable {ι Cell F : Type*} [DecidableEq Cell] [DecidableEq F]
  {cells : ι → Finset Cell} {form : ι → F} {I J : Finset ι} {c : Cell} {f : F}

/-- The forms an inventory `I` offers for the cell `c`, where the item `i` has the form `form i`
and realizes the cells `cells i`. A cell no item realizes gets `∅` and an overabundant cell
several forms, and `Setoid.ker (formsAt cells form I)` relates the cells the inventory does not
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

/-- A **paradigm system** is a family of paradigms indexed by its inflection classes `D`, an
inflection-class table read as a matrix whose rows are the classes, such as
[ackerman-malouf-2013]'s Table 1. The number of classes (the enumerative class count of that
paper's Table 3) is `Fintype.card D`. -/
abbrev ParadigmSystem (D : Type*) (n : ℕ) (Form : Type*) := D → Paradigm n Form

end Morphology
