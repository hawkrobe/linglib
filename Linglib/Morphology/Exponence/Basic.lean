import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

/-!
# Rules of exponence

This file defines the `Exponence` typeclass, pairing an exponent
`exponent : R → F` with an applicability condition `Applies : R → Ctx → Prop`
([matthews-1991]), and the specificity preorder it induces.

## Main definitions

* `Exponence`: the exponent-plus-applicability interface.
* `Exponence.toPreorder`: the specificity preorder ([kiparsky-1973]'s
  Elsewhere Condition); not an instance — each engine installs it on its
  own carrier.
-/

namespace Morphology

/-- Terms of `R` are rules of exponence with an exponent in `F` and an
applicability condition on `Ctx`. -/
class Exponence (R : Type*) (Ctx F : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → F
  /-- The condition on contexts under which a rule applies. -/
  Applies : R → Ctx → Prop

namespace Exponence

variable {Ctx F : Type*} {R : Type*} [Exponence R Ctx F]

/-- The contexts in which a rule applies. -/
def applySet (r : R) : Set Ctx := {c | Applies (F := F) r c}

@[simp] theorem mem_applySet {r : R} {c : Ctx} :
    c ∈ applySet (F := F) r ↔ Applies (F := F) r c :=
  Iff.rfl

/-- `r ≤ s` when `r` applies in a subset of the contexts `s` applies in. -/
@[reducible] def toPreorder : Preorder R := Preorder.lift (applySet (F := F))

end Exponence
end Morphology
