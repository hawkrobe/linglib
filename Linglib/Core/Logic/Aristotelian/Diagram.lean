import Linglib.Core.Logic.Aristotelian.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Aristotelian diagrams

Per @cite{demey-smessaert-2024} (Definition 1). An Aristotelian diagram is a
fragment in a Boolean algebra: a finite indexed family `φ : ι → α` together with
the matrix of Aristotelian relations between its members. The classical square
(`Square.lean`) is the case `ι = Fin 4`.

## TODO

Hexagon (`ι = Fin 6`) and cube (`ι = Fin 8`) specializations.
-/

namespace Aristotelian

variable {α : Type*} [BooleanAlgebra α]

/-- An Aristotelian diagram (@cite{demey-smessaert-2024}, Definition 1): a finite
indexed family `φ : ι → α` with a relation matrix, where `relation_correct`
asserts the labels match the actual Aristotelian relations. `relation` is
convenience data, determined by `φ`. -/
structure Diagram (ι : Type*) [Fintype ι] (α : Type*) [BooleanAlgebra α] where
  /-- The corner-to-formula assignment. -/
  φ : ι → α
  /-- The labeled relation between any two corners. -/
  relation : ι → ι → AristotelianRel
  /-- The labels match the actual relations (`unconnected` is the residual). -/
  relation_correct : ∀ i j,
    (relation i j = AristotelianRel.contradictory → IsContradictory (φ i) (φ j)) ∧
    (relation i j = AristotelianRel.contrary → IsContrary (φ i) (φ j)) ∧
    (relation i j = AristotelianRel.subcontrary → IsSubcontrary (φ i) (φ j)) ∧
    (relation i j = AristotelianRel.subaltern → IsSubaltern (φ i) (φ j))

end Aristotelian
