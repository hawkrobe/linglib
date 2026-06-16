import Linglib.Core.Logic.Aristotelian.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Aristotelian diagrams

Per [deklerck-vignero-demey-2024] (Definition 1). An Aristotelian diagram is a
*fragment* of a Boolean algebra: a finite indexed family `φ : ι → α`. The
Aristotelian relations between its members are **derived** from `φ` and the
algebra (`Diagram.opposition` / `Diagram.implication`, or the `IsContradictory …`
predicates of `Basic.lean`), never stored — the diagram *is* the pair `(φ, α)`.

The background logic enters as the choice of `α` (its Lindenbaum–Tarski algebra),
so logic-sensitivity ([demey-frijters-2023]) is the failure of relation-
preservation under a non-iso Boolean homomorphism — the dual of the
`opposition_apply_orderIso` invariance under isomorphisms.

## TODO

Hexagon (`ι = Fin 6`) and cube (`ι = Fin 8`) specializations; the opposition/
implication informativity preorders and the morphism category
([deklerck-vignero-demey-2024]).
-/

namespace Aristotelian

variable {ι : Type*} [Fintype ι] {α : Type*} [BooleanAlgebra α]

/-- An Aristotelian diagram ([deklerck-vignero-demey-2024], Definition 1): a finite fragment
`φ : ι → α` of a Boolean algebra. The relations are derived (`Diagram.opposition` /
`Diagram.implication`); the indexing `ι → α` stands in for the paper's `F ⊆ α`. -/
structure Diagram (ι : Type*) [Fintype ι] (α : Type*) [BooleanAlgebra α] where
  /-- The corner-to-formula assignment (the fragment). -/
  φ : ι → α

/-- The opposition relation between corners `i` and `j` (derived from `φ`). -/
def Diagram.opposition [DecidableEq α] (D : Diagram ι α) (i j : ι) : OppositionRel :=
  Aristotelian.opposition (D.φ i) (D.φ j)

/-- The implication relation between corners `i` and `j` (derived from `φ`). -/
def Diagram.implication [DecidableLE α] (D : Diagram ι α) (i j : ι) : ImplicationRel :=
  Aristotelian.implication (D.φ i) (D.φ j)

end Aristotelian
