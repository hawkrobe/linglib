import Linglib.Semantics.Presupposition.Defs

/-!
# Quantified presupposition projection

Projection of presuppositions from the scope of quantifiers — the
empirically contested corner of projection theory: [chemla-2009-quantified]
supports universal projection, [mayr-sauerland-2015] argue for existential
semantic projection pragmatically strengthened, and [spector-sudo-2017]
delimit when each reading surfaces.

## Main declarations

* `forallPartial` — universal quantification, universal projection.
* `existsPartialUniv` / `existsPartialExist` — existential quantification
  with universal vs existential projection; consumers committing to a
  projection theory pick one explicitly.
* `negExistsPartial` — negated existential, universal projection.
-/

namespace Semantics.Presupposition

namespace PartialProp

variable {W : Type*}

/-- Universal presupposition projection: presuppositions project
    universally from the scope of a universal quantifier.

    For ∀x ∈ S, φ(x) where φ(x) is a PartialProp:
    - asserts: ∀x ∈ S, assertion(φ(x))
    - presupposes: ∀x ∈ S, presup(φ(x))

    [chemla-2009-quantified], [fox-2013]: presuppositions triggered in
    the scope of a universal quantifier tend to project universally.
    ([mayr-sauerland-2015] dissent: semantic projection is existential,
    pragmatically strengthened — cf. [spector-sudo-2017].) -/
def forallPartial {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∀ x, S x → (φ x).assertion w

/-- Existential presupposition projection — universal presup, existential
    assert.

    For ∃x ∈ S, φ(x): presuppositions project *universally*, but the
    assertion is existential. This is the projection choice supported
    experimentally by [chemla-2009-quantified]; whether it is the right
    default is empirically contested — see [spector-sudo-2017] for
    conditions under which a non-universal (existential) reading is
    preferred. Consumers committing to a projection theory should pick
    `existsPartialUniv` or `existsPartialExist` explicitly. -/
def existsPartialUniv {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).assertion w

/-- Existential presupposition projection — existential presup, existential
    assert. The non-universal alternative to `existsPartialUniv`; see
    [spector-sudo-2017] for the empirical debate. -/
def existsPartialExist {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∃ x, S x ∧ (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).assertion w

/-- Negated existential with universal presupposition projection.

    For ¬∃x ∈ S, φ(x): equivalent to ∀x ∈ S, ¬φ(x).
    Presuppositions project universally. -/
def negExistsPartial {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ¬∃ x, S x ∧ (φ x).assertion w

/-- `forallPartial` holds iff every member satisfies both presupposition and assertion. -/
theorem forallPartial_holds {α : Type*} (S : α → Prop) (φ : α → PartialProp W) (w : W) :
    (forallPartial S φ).holds w ↔
      (∀ x, S x → (φ x).presup w) ∧ (∀ x, S x → (φ x).assertion w) :=
  Iff.rfl

end PartialProp

end Semantics.Presupposition
