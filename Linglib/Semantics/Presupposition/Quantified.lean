module

public import Linglib.Semantics.Presupposition.Defs

/-!
# Quantified presupposition projection

A presupposition triggered in the scope of a quantifier may project universally, as Chemla's
experiments support, or existentially, as Mayr and Sauerland argue for a semantic projection
that pragmatics then strengthens; Spector and Sudo delimit when each reading surfaces. Each
quantifier here fixes its projection, so a consumer commits to a theory by its choice of
operator. The strong Kleene existential of Kleene and Fox is instead defined exactly where some
instance is true or every instance is false.

## Main declarations

* `forallPartial`: universal quantification with universal projection.
* `existsPartialUniv`, `existsPartialExist`: existential quantification with universal and with
  existential projection.
* `negExistsPartial`: the negated existential with universal projection.
* `existsUniquePartial`: *exactly one* with universal projection, which Del Pinal, Bassi and
  Sauerland assume for non-monotonic quantifiers.
* `existsPartialStrong`, `existsPartialStrong_presup_iff`: the strong Kleene existential, whose
  presupposition over a nonempty domain reduces to one every instance shares.

## References

* [chemla-2009-quantified]
* [mayr-sauerland-2015]
* [spector-sudo-2017]
* [kleene-1952]
* [fox-2013]
* [delpinal-bassi-sauerland-2024]
-/

@[expose] public section

namespace Presupposition

namespace PartialProp

variable {W : Type*}

/-- `forallPartial S φ` asserts that every `x` with `S x` satisfies the assertion of `φ x` and
presupposes that every such `x` satisfies its presupposition. -/
def forallPartial {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∀ x, S x → (φ x).assertion w

/-- `existsPartialUniv S φ` asserts that some `x` with `S x` satisfies the assertion of `φ x` and
presupposes that every such `x` satisfies its presupposition. -/
def existsPartialUniv {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).assertion w

/-- `existsPartialExist S φ` asserts that some `x` with `S x` satisfies the assertion of `φ x` and
presupposes that some such `x` satisfies its presupposition. -/
def existsPartialExist {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∃ x, S x ∧ (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).assertion w

/-- `negExistsPartial S φ` asserts that no `x` with `S x` satisfies the assertion of `φ x` and
presupposes that every such `x` satisfies its presupposition. -/
def negExistsPartial {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ¬∃ x, S x ∧ (φ x).assertion w

/-- `existsUniquePartial S φ` asserts that exactly one `x` with `S x` satisfies the assertion of
`φ x` and presupposes that every such `x` satisfies its presupposition. -/
def existsUniquePartial {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∃! x, S x ∧ (φ x).assertion w

/-- The strong Kleene existential is true when some instance is true, false when every instance
is false, and undefined otherwise. -/
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
