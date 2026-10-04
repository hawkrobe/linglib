module

public import Linglib.Core.Order.Flat
public import Mathlib.Order.WithBot

/-!
# Feature-checking slots

A feature-checking slot records the state of one feature dimension on a lexical item. Under
Agree a dimension is in one of three states: `absent`, when the item lacks it; `unvalued`, a
probe, present but valueless (Chomsky's unvalued feature, which searches for a goal); and
`valued v`. A determinate slot of `Core/Order/Flat.lean` has two states, bottom or a value, so a
checking slot is a flat slot with a new bottom below it: `WithBot (Flat α)`, as `EReal` is
`WithBot (WithTop ℝ)`. Its subsumption order is therefore `absent < unvalued < valued v` with
distinct values incomparable, the per-slot order the bundle subsumption order is built from.

Following Marcolli, Chomsky and Berwick, the free-Merge core keeps the features of a syntactic
object atomic, and the valued/unvalued apparatus belongs to the Agree layer, so slots are kept
general here, polymorphic in the value type, and decoupled from the `SyntacticObject` carrier.

## Main definitions

* `Minimalist.FeatureSlot` — `WithBot (Flat α)`, with the patterns `absent`, `unvalued`,
  `valued` and the eliminator `FeatureSlot.rec'`
* `Minimalist.FeatureSlot.valueWith` — valuation of an unvalued slot

## References

* [chomsky-2000]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

/-- A feature-checking slot for value type `α` is `absent`, `unvalued` (a probe), or `valued v`:
a flat slot with a new bottom below it. -/
abbrev FeatureSlot (α : Type*) := WithBot (Flat α)

namespace FeatureSlot

variable {α : Type*}

/-- An item lacking the dimension has the `absent` slot. -/
@[match_pattern] abbrev absent : FeatureSlot α := none

/-- A probe has the `unvalued` slot, present but valueless. -/
@[match_pattern] abbrev unvalued : FeatureSlot α := WithBot.some ⊥

/-- The `valued v` slot carries the value `v`. -/
@[match_pattern] abbrev valued (v : α) : FeatureSlot α := WithBot.some (Flat.some v)

/-- A slot is absent, unvalued, or valued. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec' {motive : FeatureSlot α → Sort*} (absent : motive .absent) (unvalued : motive .unvalued)
    (valued : ∀ v, motive (.valued v)) : ∀ s, motive s
  | .absent => absent
  | .unvalued => unvalued
  | .valued v => valued v

@[simp] theorem bot_eq_absent : (⊥ : FeatureSlot α) = absent := rfl

@[simp] theorem unvalued_ne_absent : (unvalued : FeatureSlot α) ≠ absent := nofun

@[simp] theorem valued_ne_absent (v : α) : valued v ≠ absent := nofun

@[simp] theorem valued_ne_unvalued (v : α) : valued v ≠ unvalued := nofun

@[simp] theorem valued_inj {v w : α} : valued v = valued w ↔ v = w :=
  ⟨fun h ↦ Flat.coe_injective (WithBot.coe_injective h), fun h ↦ h ▸ rfl⟩

/-- The slot specifies a present feature, that is, it is not `absent`. -/
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

/-- The value of a slot, when it is valued. -/
def value? : FeatureSlot α → Option α
  | valued v => some v
  | _ => none

/-- Valuing a slot with `v` fills it when it is unvalued and leaves an absent or valued slot as it
is. -/
def valueWith (v : α) : FeatureSlot α → FeatureSlot α
  | unvalued => valued v
  | s => s

@[simp] theorem valueWith_absent (v : α) : valueWith v absent = absent := rfl
@[simp] theorem valueWith_unvalued (v : α) : valueWith v unvalued = valued v := rfl
@[simp] theorem valueWith_valued (v w : α) : valueWith v (valued w) = valued w := rfl

theorem valueWith_of_ne_unvalued (v : α) {s : FeatureSlot α} (h : s ≠ unvalued) :
    valueWith v s = s := by
  cases s with
  | absent => rfl
  | unvalued => exact absurd rfl h
  | valued w => rfl

/-- Valuation is inflationary in the subsumption order. -/
theorem le_valueWith (v : α) (s : FeatureSlot α) : s ≤ valueWith v s := by
  cases s with
  | absent => exact bot_le
  | unvalued => exact WithBot.coe_le_coe.2 bot_le
  | valued w => exact le_rfl

@[simp] theorem isSpecified_iff_ne_bot {s : FeatureSlot α} :
    s.isSpecified = true ↔ s ≠ ⊥ := by
  cases s with
  | absent => simp [isSpecified]
  | unvalued => exact ⟨fun _ ↦ nofun, fun _ ↦ rfl⟩
  | valued v => exact ⟨fun _ ↦ nofun, fun _ ↦ rfl⟩

end FeatureSlot

end Minimalist
