import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Frame conditions on accessibility — generic over point type

Pure relational predicates over a `Finset`-valued accessibility relation
`R : W → Finset W` and a base team `s : Finset W`. Theory-neutral: nothing
in this file knows about formulas, support, or evaluation.

Used by BSML (Aloni 2022 Definition 5), QBSML (Aloni & van Ormondt 2023
Definition 4.10), and any future state-based logic that needs to
distinguish epistemic-from-deontic accessibility via these conditions.

In QBSML, the team is over indices `W × Assignment`; the frame conditions
apply to the *projection* `s↓ := {w | ∃g, (w, g) ∈ s}`. So a QBSML
`isStateBased` becomes `Core.Logic.StateAlgebra.isStateBased R (s.image Prod.fst)`
— the same definition, called via a state projection.
-/

namespace Core.Logic.StateAlgebra

variable {W : Type*}

/-- `R` is **state-based** on team `s` iff every world in `s` is `R`-accessible
    exactly to `s`. Strictly stronger than indisputability.

    Aloni 2022 Definition 5 (state-based ↔ epistemic modals). -/
def isStateBased (R : W → Finset W) (s : Finset W) : Prop :=
  ∀ w ∈ s, R w = s

/-- `R` is **indisputable** on team `s` iff all worlds in `s` see the same
    set of accessible worlds. Equivalently: `R` is constant on `s`.

    Aloni 2022 Definition 5 (indisputable ↔ deontic-with-knowledgeable-speaker). -/
def isIndisputable (R : W → Finset W) (s : Finset W) : Prop :=
  ∀ w₁ ∈ s, ∀ w₂ ∈ s, R w₁ = R w₂

/-- State-based implies indisputable. (Aloni 2022 §4.1 remark; trivial
    from definitions.) -/
theorem isStateBased_imp_isIndisputable (R : W → Finset W) (s : Finset W)
    (h : isStateBased R s) : isIndisputable R s := by
  intro w₁ hw₁ w₂ hw₂; rw [h w₁ hw₁, h w₂ hw₂]

instance (R : W → Finset W) (s : Finset W)
    [DecidableEq W] [Fintype W] : Decidable (isStateBased R s) := by
  unfold isStateBased; infer_instance

instance (R : W → Finset W) (s : Finset W)
    [DecidableEq W] [Fintype W] : Decidable (isIndisputable R s) := by
  unfold isIndisputable; infer_instance

end Core.Logic.StateAlgebra
