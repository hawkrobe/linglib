module

public import Linglib.Semantics.Presupposition.Defs

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
* `existsPartialStrong` — the strong Kleene existential ([kleene-1952], [fox-2013]): true when
  some instance is true, false when every instance is false, so that its presupposition is a
  disjunction; `existsPartialStrong_presup_iff` reduces it to a presupposition every instance
  shares, over a nonempty domain.
-/

@[expose] public section

namespace Presupposition

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

/-- The strong Kleene existential ([kleene-1952], [fox-2013]): true when some instance is true,
false when every instance is false, and undefined otherwise. -/
def existsPartialStrong {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup w := (∃ x, S x ∧ (φ x).holds w) ∨ ∀ x, S x → (φ x).presup w ∧ ¬ (φ x).assertion w
  assertion w := ∃ x, S x ∧ (φ x).holds w

section existsPartialStrong

variable {α : Type*} {S : α → Prop} {φ : α → PartialProp W} {w : W}

/-- The strong existential holds when some instance does. -/
theorem existsPartialStrong_holds_iff :
    (existsPartialStrong S φ).holds w ↔ ∃ x, S x ∧ (φ x).holds w :=
  ⟨And.right, fun h ↦ ⟨.inl h, h⟩⟩

/-- A strong existential over an empty domain is defined, and false. -/
theorem existsPartialStrong_presup_of_not_exists (h : ¬ ∃ x, S x) :
    (existsPartialStrong S φ).presup w :=
  .inr fun x hx ↦ absurd ⟨x, hx⟩ h

/-- A strong existential over defined instances is defined. -/
theorem existsPartialStrong_presup_of_forall (h : ∀ x, S x → (φ x).presup w) :
    (existsPartialStrong S φ).presup w := by
  by_cases hx : ∃ x, S x ∧ (φ x).assertion w
  · obtain ⟨x, hx, ha⟩ := hx
    exact .inl ⟨x, hx, h x hx, ha⟩
  · exact .inr fun x hxS ↦ ⟨h x hxS, fun ha ↦ hx ⟨x, hxS, ha⟩⟩

/-- A defined strong existential over a nonempty domain has a defined instance. -/
theorem exists_presup_of_existsPartialStrong (hS : ∃ x, S x)
    (h : (existsPartialStrong S φ).presup w) : ∃ x, S x ∧ (φ x).presup w := by
  rcases h with ⟨x, hx, hp, _⟩ | h
  · exact ⟨x, hx, hp⟩
  · obtain ⟨x, hx⟩ := hS
    exact ⟨x, hx, (h x hx).1⟩

/-- Over a nonempty domain whose instances share a presupposition, the strong existential
presupposes it. -/
theorem existsPartialStrong_presup_iff {π : W → Prop} (hS : ∃ x, S x)
    (h : ∀ x, S x → (φ x).presup = π) : (existsPartialStrong S φ).presup w ↔ π w := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ existsPartialStrong_presup_of_forall fun x hx ↦ h x hx ▸ hp⟩
  obtain ⟨x, hx, hpx⟩ := exists_presup_of_existsPartialStrong hS hp
  exact h x hx ▸ hpx

end existsPartialStrong

/-- `forallPartial` holds iff every member satisfies both presupposition and assertion. -/
theorem forallPartial_holds {α : Type*} (S : α → Prop) (φ : α → PartialProp W) (w : W) :
    (forallPartial S φ).holds w ↔
      (∀ x, S x → (φ x).presup w) ∧ (∀ x, S x → (φ x).assertion w) :=
  Iff.rfl

end PartialProp

end Presupposition
