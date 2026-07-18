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

`Exponence.Rule Ctx F` is the free carrier. Framework engines (the
containment hierarchy, DM vocabulary items, nanosyntax spellout) implement
`Exponence` on their own intensional carriers (thresholds, feature
bundles, stored trees) and install `Exponence.toPreorder` as the
carrier's order, so the selection theorems apply to the native type
with no wrapper.

## Main declarations

* `Exponence` — the exponent-plus-applicability class;
  `Exponence.toPreorder` lifts applicability-set inclusion to a preorder
* `Exponence.Rule` — the free carrier: an exponent with its applicability
  condition
-/

namespace Morphology

/-- Carriers whose values expone: an exponent projection and an
applicability set, à la `SetLike` minus injectivity. Distinct rules may
share an applicability set while carrying different exponents, so there
is no `coe_injective` and the induced order is only a preorder
(`toPreorder`), never a partial order. Framework engines instantiate
this on their intensional carriers and derive Elsewhere selection over
the native type. -/
class Exponence (R : Type*) (Ctx F : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → F
  /-- The set of contexts a rule applies in. -/
  applySet : R → Set Ctx

namespace Exponence

variable {Ctx F : Type*}

/-- A **rule of exponence**: an exponent paired with the condition on
contexts under which the rule applies. Framework engines specialize
`Ctx` and recover applicability from intensional specifications
(thresholds, feature bundles, stored trees). -/
structure Rule (Ctx : Type*) (F : Type*) where
  /-- The exponent the rule inserts. -/
  exponent : F
  /-- The contexts in which the rule applies. -/
  Applies : Ctx → Prop

namespace Rule

/-- The set of contexts a rule applies in. -/
def applySet (r : Rule Ctx F) : Set Ctx := {c | r.Applies c}

@[simp] theorem mem_applySet {r : Rule Ctx F} {c : Ctx} :
    c ∈ r.applySet ↔ r.Applies c :=
  Iff.rfl

/-- Rules are preordered by applicability-set inclusion: `r ≤ s` when
`r` applies in a subset of the contexts `s` applies in, i.e. `r` is at
least as specific as `s`. Only a preorder — rules with the same
applicability but different exponents are equivalent, not equal. -/
instance : Preorder (Rule Ctx F) := .lift applySet

theorem le_def {r s : Rule Ctx F} : r ≤ s ↔ r.applySet ⊆ s.applySet :=
  Iff.rfl

/-- Derived Pāṇinian specificity, unfolded: `r ≤ s` iff `s` applies
wherever `r` does. -/
theorem le_iff {r s : Rule Ctx F} :
    r ≤ s ↔ ∀ ⦃c⦄, r.Applies c → s.Applies c :=
  Iff.rfl

end Rule

variable {R : Type*} [Exponence R Ctx F]

/-- A rule applies at a context when the context is in its
applicability set. -/
def Applies (r : R) (c : Ctx) : Prop := c ∈ applySet (F := F) r

/-- The preorder a carrier opts into: applicability-set inclusion. Not a
global instance — each engine installs it (or a defeq order) on its own
carrier. -/
@[reducible] def toPreorder : Preorder R := Preorder.lift (applySet (F := F))

/-- The free carrier exposes its fields as the interface. -/
instance : Exponence (Rule Ctx F) Ctx F := ⟨Rule.exponent, Rule.applySet⟩

end Exponence
end Morphology
