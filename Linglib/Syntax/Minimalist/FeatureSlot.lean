import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic

/-!
# Feature-checking slots
[chomsky-2000] [marcolli-chomsky-berwick-2025]

A *feature-checking slot* records the state of one feature dimension on a
lexical item. Unlike a plain determinate slot (`Core/Order/Flat.lean`'s `Flat`,
which is two-state — bottom or a value), a feature dimension under Agree is in
one of **three** states:

- `absent` — the item lacks the dimension (the order bottom `⊥`);
- `unvalued` — a **probe**: the dimension is present but valueless
  ([chomsky-2000]'s unvalued/uninterpretable feature, which searches for a goal);
- `valued v` — the dimension is present with value `v`.

`FeatureSlot` is **polymorphic** in the value type `α`, so it is reusable across
feature spaces (φ-features, case, categorial features, …) and carries no
commitment to any particular inventory.

## Why this is decoupled from the Merge carrier

Per [marcolli-chomsky-berwick-2025] (book p. 13), the valued/unvalued
feature-checking apparatus is the **Stabler-Minimalism** layer: label-matching
makes Merge partially defined, forcing "an algebraically more complex Hopf
algebra and … a family of right-ideal coideals … which keep track of the feature
checking problem." MCB's own free-Merge core (the SMT) keeps `SO₀` features
*atomic* — Merge is free, with no feature checking. So feature-checking slots are
an Agree-layer structure, kept general here and **decoupled from the
`SyntacticObject` carrier** rather than baked into it.

## Subsumption order

`absent (⊥) < unvalued < valued v`, with distinct `valued` values forming an
antichain: a probe is more specified than an absent dimension and less specified
than a value, and two values are incomparable. This is the per-slot order that
the bundle subsumption order (`Features.BundleLike.Subsumes`) is built from.
-/

namespace Features

/-- A feature-checking slot for value type `α`: `absent` / `unvalued` (probe) /
`valued v`. See the module docstring. -/
inductive FeatureSlot (α : Type*) where
  | absent
  | unvalued
  | valued (v : α)
  deriving Repr, DecidableEq

namespace FeatureSlot

variable {α : Type*}

instance : Bot (FeatureSlot α) := ⟨absent⟩

@[simp] theorem bot_eq_absent : (⊥ : FeatureSlot α) = absent := rfl

/-- The slot specifies a (present) feature: it is not `absent`. -/
def isSpecified : FeatureSlot α → Bool
  | absent => false
  | _ => true

/-- The slot is a probe (present but unvalued). -/
def isUnvalued : FeatureSlot α → Bool
  | unvalued => true
  | _ => false

/-- The slot carries a value. -/
def isValued : FeatureSlot α → Bool
  | valued _ => true
  | _ => false

/-- The value, when the slot is `valued`. -/
def value? : FeatureSlot α → Option α
  | valued v => some v
  | _ => none

/-- Subsumption: `absent ≤ unvalued ≤ valued v`, with distinct values
incomparable. The reflexive-transitive order on the three checking states. -/
protected inductive LE : FeatureSlot α → FeatureSlot α → Prop
  | absent_le (s) : FeatureSlot.LE absent s
  | unvalued_le_unvalued : FeatureSlot.LE unvalued unvalued
  | unvalued_le_valued (v) : FeatureSlot.LE unvalued (valued v)
  | valued_le_valued (v) : FeatureSlot.LE (valued v) (valued v)

instance : LE (FeatureSlot α) := ⟨FeatureSlot.LE⟩

theorem le_def {a b : FeatureSlot α} : a ≤ b ↔ FeatureSlot.LE a b := Iff.rfl

protected theorem le_refl (a : FeatureSlot α) : a ≤ a := by
  cases a with
  | absent => exact .absent_le _
  | unvalued => exact .unvalued_le_unvalued
  | valued v => exact .valued_le_valued v

protected theorem le_trans {a b c : FeatureSlot α} (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := by
  cases hab with
  | absent_le => exact .absent_le _
  | unvalued_le_unvalued => exact hbc
  | unvalued_le_valued v => cases hbc with | valued_le_valued => exact .unvalued_le_valued v
  | valued_le_valued v => exact hbc

protected theorem le_antisymm {a b : FeatureSlot α} (hab : a ≤ b) (hba : b ≤ a) :
    a = b := by
  cases hab <;> cases hba <;> rfl

instance : PartialOrder (FeatureSlot α) where
  le_refl := FeatureSlot.le_refl
  le_trans _ _ _ := FeatureSlot.le_trans
  le_antisymm _ _ := FeatureSlot.le_antisymm

instance : OrderBot (FeatureSlot α) where
  bot_le a := .absent_le a

instance [DecidableEq α] (a b : FeatureSlot α) : Decidable (a ≤ b) :=
  match a, b with
  | absent, _ => isTrue (.absent_le _)
  | unvalued, unvalued => isTrue .unvalued_le_unvalued
  | unvalued, valued v => isTrue (.unvalued_le_valued v)
  | unvalued, absent => isFalse (by rintro ⟨⟩)
  | valued v, valued w =>
    if h : v = w then isTrue (h ▸ .valued_le_valued v)
    else isFalse (by rintro ⟨⟩; exact h rfl)
  | valued _, absent => isFalse (by rintro ⟨⟩)
  | valued _, unvalued => isFalse (by rintro ⟨⟩)

@[simp] theorem isSpecified_iff_ne_bot {s : FeatureSlot α} :
    s.isSpecified = true ↔ s ≠ ⊥ := by
  cases s <;> simp [isSpecified]

end FeatureSlot

end Features
