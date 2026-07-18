import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

/-!
# Rules of exponence
[kiparsky-1973] [halle-marantz-1993] [stump-2001] [stump-2022]

**Exponence** ([matthews-1991]'s term for the mapping from morphosyntactic
content to form) is the class every framework engine's carrier implements:
an exponent projection and an applicability set, ordered by set inclusion
([kiparsky-1973]'s Elsewhere Condition), so the most specific applicable
rule has the smallest applicability domain. The class is selection-side
only: the phonological substance of exponents (additive vs
transformational vs templatic, [trommer-zimmermann-2015]) is opaque in
`F` and lives in `Phonology/`. The order is [stump-2022]'s
single-clause formulation of Pāṇini's principle — domain-subset precedence
— to which [stump-2001]'s two-clause rule narrowness collapses when
contexts pair expressions with their full property sets. Selection over
this order — existence, coherence, and the framework-neutral prediction
relation — lives in `Morphology/Exponence/Select.lean`.

Framework engines (the containment hierarchy, DM vocabulary items,
nanosyntax spellout) implement `Exponence` on their own intensional
carriers (thresholds, feature bundles, stored trees) and install
`Exponence.toPreorder` as the carrier's order, so the selection theorems
apply to the native type with no wrapper.

## Main declarations

* `Exponence` — the exponent-plus-applicability class;
  `Exponence.toPreorder` lifts applicability-set inclusion to a preorder
-/

namespace Morphology

/-- Carriers whose values expone: an exponent projection and an
applicability condition, à la `SetLike` minus injectivity — conceptually
a coercion to applicability sets (`applySet`), though the primitive is
the predicate, which is what engines define and what decidability
instances attach to. Distinct rules may share an applicability condition
while carrying different exponents, so there is no `coe_injective` and
the induced order is only a preorder (`toPreorder`), never a partial
order. Framework engines instantiate this on their intensional carriers
and derive Elsewhere selection over the native type. -/
class Exponence (R : Type*) (Ctx F : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → F
  /-- The condition on contexts under which a rule applies. -/
  Applies : R → Ctx → Prop

namespace Exponence

variable {Ctx F : Type*} {R : Type*} [Exponence R Ctx F]

/-- A rule's applicability set: the contexts its condition holds in. -/
def applySet (r : R) : Set Ctx := {c | Applies (F := F) r c}

@[simp] theorem mem_applySet {r : R} {c : Ctx} :
    c ∈ applySet (F := F) r ↔ Applies (F := F) r c :=
  Iff.rfl

/-- The preorder a carrier opts into: applicability-set inclusion (`r ≤ s`
when `r` applies in a subset of the contexts `s` applies in, i.e. `r` is
at least as specific as `s`). Only a preorder — rules with the same
applicability but different exponents are equivalent, not equal. Not a
global instance — each engine installs it (or a defeq order) on its own
carrier. -/
@[reducible] def toPreorder : Preorder R := Preorder.lift (applySet (F := F))

end Exponence
end Morphology
