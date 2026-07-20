import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

/-!
# Rules of exponence

This file defines the `Exponence.Rule` typeclass, pairing an exponent
`exponent : R → E` with an applicability condition `Applies : R → Ctx → Prop`
([matthews-1991]), and the specificity preorder it induces.

## Main definitions

* `Exponence.Rule`: the exponent-plus-applicability interface.
* `Exponence.toPreorder`: the specificity preorder ([kiparsky-1973]'s
  Elsewhere Condition); not an instance — each engine installs it on its
  own carrier.
-/

namespace Morphology.Exponence

/-- `Rule R Ctx E` says that `R` is a type of rules of exponence: each rule
carries an exponent in `E` and applies in a class of contexts in `Ctx`. -/
class Rule (R : Type*) (Ctx E : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → E
  /-- The condition on contexts under which a rule applies. -/
  Applies : R → Ctx → Prop

export Rule (exponent Applies)

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E]

/-- The contexts in which a rule applies. -/
def applySet (r : R) : Set Ctx := {c | Applies r c}

@[simp] theorem mem_applySet {r : R} {c : Ctx} :
    c ∈ applySet r ↔ Applies r c :=
  Iff.rfl

/-- `r ≤ s` when `r` applies in a subset of the contexts `s` applies in. -/
@[reducible] def toPreorder : Preorder R := Preorder.lift (applySet (Ctx := Ctx) (E := E))

end Morphology.Exponence
