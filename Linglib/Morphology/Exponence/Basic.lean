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
— additive, transformational, templatic ([trommer-zimmermann-2015]) — is
opaque in `F` and lives in `Phonology/`. Selection over the specificity
order (existence, coherence, and the prediction relation) is
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

/-- `Exponence R Ctx F` states that terms of `R` are rules of exponence:
each carries an exponent in `F` and applies in a class of contexts in
`Ctx`. This is `SetLike` without injectivity: the projection to
applicability sets (`applySet`) need not be injective, since distinct
rules may share a condition while carrying different exponents. The
primitive is the predicate `Applies`, which is what engines define and
what decidability instances attach to. -/
class Exponence (R : Type*) (Ctx F : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → F
  /-- The condition on contexts under which a rule applies. -/
  Applies : R → Ctx → Prop

namespace Exponence

variable {Ctx F : Type*} {R : Type*} [Exponence R Ctx F]

/-- The applicability set of a rule: the contexts in which it applies. -/
def applySet (r : R) : Set Ctx := {c | Applies (F := F) r c}

@[simp] theorem mem_applySet {r : R} {c : Ctx} :
    c ∈ applySet (F := F) r ↔ Applies (F := F) r c :=
  Iff.rfl

/-- The specificity preorder: `r ≤ s` when `r` applies in a subset of the
contexts `s` applies in. Rules with the same applicability but different
exponents are equivalent, not equal, so this is only a preorder. This is
not an instance, for flexibility in choosing orders: each engine installs
it, or a definitionally equal order, on its own carrier. -/
@[reducible] def toPreorder : Preorder R := Preorder.lift (applySet (F := F))

end Exponence
end Morphology
