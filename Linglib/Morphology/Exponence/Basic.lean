import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

/-!
# Rules of exponence

A rule of exponence pairs an exponent with the class of contexts in which
it may be inserted; exponence is [matthews-1991]'s term for the mapping
from morphosyntactic content to form. The `Exponence` typeclass provides a
unified interface to this shape: an exponent projection `exponent : R → F`
and an applicability condition `Applies : R → Ctx → Prop`.

Specificity is applicability-set inclusion: `r ≤ s` when `r` applies in a
subset of the contexts `s` applies in. This is [kiparsky-1973]'s Elsewhere
Condition as an order, in [stump-2022]'s single-clause formulation of
Pāṇini's principle; [stump-2001]'s two-clause rule narrowness collapses to
it when contexts pair expressions with their full property sets. Distinct
rules may share an applicability condition while carrying different
exponents, so the induced order is a preorder and not a partial order. It
is provided as `Exponence.toPreorder` and is not an instance, for
flexibility in choosing orders: each engine installs it, or a
definitionally equal order, on its own carrier.

The class is selection-side only: the phonological substance of exponents
([trommer-zimmermann-2015]) is opaque in `F`. Selection over this order is
`Morphology/Exponence/Select.lean`.

A typical engine is declared as:
```
instance : Exponence (MyRule Ctx F) Ctx F :=
  ⟨MyRule.exponent, fun r c => r.condition c⟩

instance : Preorder (MyRule Ctx F) := Exponence.toPreorder
```
after which the selection theorems of `Select.lean` apply to `MyRule`.

## Main declarations

* `Exponence` — the exponent-plus-applicability interface.
* `Exponence.applySet`, `Exponence.toPreorder` — a rule's applicability set
  and the specificity preorder it induces.
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
