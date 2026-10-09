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

The quantifiers descend along `eval` to trivalent quantifiers over the domain's subtype,
continuing the connective bridges of `Presupposition.Basic`: universal projection is the Weak
Kleene family (`eval_forallPartial`, `eval_existsPartialUniv`, `eval_negExistsPartial`),
existential projection is Haug's family (`eval_existsPartialExist`), and the strong Kleene
existential is the Strong Kleene family (`eval_existsPartialStrong`). Only
`existsUniquePartial`, whose counting assertion is no lattice quantifier, carries no bridge.

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

/-- `existsPartialExist S φ` asserts that some `x` with `S x` satisfies `φ x` outright and
presupposes that some such `x` is defined. The witness must satisfy presupposition and
assertion together — reading bare assertion values at undefined witnesses would make the
quantifier sensitive to content that `eval` forgets — so the operator descends to Haug's
existential (`eval_existsPartialExist`). -/
def existsPartialExist {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∃ x, S x ∧ (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).holds w

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

/-! ### Evaluation bridges

Each quantifier evaluates to a trivalent quantifier over the domain's subtype — the
quantified counterparts of the connective bridges in `Presupposition.Basic`.
`existsUniquePartial` shares the Weak Kleene projection of `forallPartial`, but its counting
assertion is no lattice quantifier, so it carries no bridge. -/

section Bridges

variable {α : Type*} (S : α → Prop) (φ : α → PartialProp W) (w : W)

/-- Universal projection is the Weak Kleene universal quantifier. -/
theorem eval_forallPartial :
    (forallPartial S φ).eval w =
      Trivalent.forallWeak fun x : {x // S x} => (φ x.1).eval w := by
  refine Trivalent.eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [forallPartial, Subtype.forall, Subtype.exists, not_forall, Classical.not_imp,
      forall_and]

/-- The existential with universal projection is the Weak Kleene existential. -/
theorem eval_existsPartialUniv :
    (existsPartialUniv S φ).eval w =
      Trivalent.existsWeak fun x : {x // S x} => (φ x.1).eval w := by
  refine Trivalent.eq_of_indet_iff_of_true_iff ?_ ?_
  · simp [existsPartialUniv, Subtype.exists, not_forall, Classical.not_imp]
  · simp only [eval_eq_true_iff, Trivalent.existsWeak_eq_true_iff, ne_eq, eval_eq_indet_iff,
      not_not, Subtype.forall, Subtype.exists, exists_prop, existsPartialUniv]
    exact and_congr_right fun hp => exists_congr fun x =>
      and_congr_right fun hx => (and_iff_right (hp x hx)).symm

/-- The negated existential with universal projection is the negated Weak Kleene
existential. -/
theorem eval_negExistsPartial :
    (negExistsPartial S φ).eval w =
      Trivalent.neg (Trivalent.existsWeak fun x : {x // S x} => (φ x.1).eval w) := by
  refine Trivalent.eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [negExistsPartial, Subtype.forall, Subtype.exists, not_forall, Classical.not_imp,
      not_exists, not_and, forall_and]

/-- Existential projection is Haug's existential quantifier. -/
theorem eval_existsPartialExist :
    (existsPartialExist S φ).eval w =
      Trivalent.existsHaug fun x : {x // S x} => (φ x.1).eval w := by
  refine Trivalent.eq_of_indet_iff_of_true_iff ?_ ?_
  · simp [existsPartialExist, Subtype.forall, not_exists, not_and]
  · simp only [eval_eq_true_iff, Trivalent.existsHaug_eq_true_iff, Subtype.exists,
      exists_prop, existsPartialExist, holds]
    exact ⟨fun ⟨_, h⟩ => h, fun ⟨x, hx, hp, ha⟩ => ⟨⟨x, hx, hp⟩, x, hx, hp, ha⟩⟩

/-- The strong existential is the Strong Kleene existential quantifier. -/
theorem eval_existsPartialStrong :
    (existsPartialStrong S φ).eval w =
      Trivalent.existsStrong fun x : {x // S x} => (φ x.1).eval w := by
  refine Trivalent.eq_of_indet_iff_of_true_iff ?_ ?_
  · rw [eval_eq_indet_iff, Trivalent.existsStrong_eq_indet_iff]
    constructor
    · intro hnp
      have h1 : ¬ ∃ x, S x ∧ (φ x).holds w := fun h => hnp (.inl h)
      have h2 : ¬ ∀ x, S x → (φ x).presup w ∧ ¬(φ x).assertion w := fun h => hnp (.inr h)
      refine ⟨fun ⟨x, hx⟩ ht => h1 ⟨x, hx, (eval_eq_true_iff _ _).1 ht⟩, ?_⟩
      by_contra hc
      push Not at hc
      refine h2 fun x hx => ?_
      have hp : (φ x).presup w := not_not.1 ((eval_eq_indet_iff _ _).2.mt (hc ⟨x, hx⟩))
      exact ⟨hp, fun ha => h1 ⟨x, hx, hp, ha⟩⟩
    · rintro ⟨hnt, ⟨x, hx⟩, hind⟩ (⟨y, hy, hh⟩ | hall)
      · exact hnt ⟨y, hy⟩ ((eval_eq_true_iff _ _).2 hh)
      · exact (eval_eq_indet_iff _ _).1 hind (hall x hx).1
  · simp only [eval_eq_true_iff, Trivalent.existsStrong_eq_true_iff, Subtype.exists,
      exists_prop, existsPartialStrong, holds]
    exact ⟨fun ⟨_, h⟩ => h, fun ⟨x, hx, hh⟩ => ⟨.inl ⟨x, hx, hh⟩, x, hx, hh⟩⟩

end Bridges

end PartialProp

end Presupposition
