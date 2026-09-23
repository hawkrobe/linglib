/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Linglib.Logic.Natural.Basic

/-!
# Marked types for the monotonicity calculus

This file defines the type system of the [icard-moss-tune-2017]
monotonicity calculus: simple types over a set of base types, with
each arrow marked as monotone (`+`), antitone (`−`), or unmarked
(`·`).

## Main declarations

* The three markings are the context polarities `upward` (`+`), `downward` (`−`) and
  `nonMonotonic` (`·`), a commutative monoid under valence composition (`+` the identity, `·`
  absorbing); here they also get the information order, a join-semilattice with `·` on top.
* `Ty`: marked simple types, with the subtyping order — contravariant
  in domains, covariant in codomains and markings — decidable over a
  `DecidableEq` base.
* `Ty.sup?`: the partial join of compatible types.
* `Ty.unmark`: erasure of the markings along the codomain spine.

## References

* [icard-moss-tune-2017] — Definitions 3.1–3.3.
-/

@[expose] public section

namespace NaturalLogic

/-! ### Markings -/

/-! A monotonicity marking ([icard-moss-tune-2017] Definition 3.1) is a `ContextPolarity`:
`upward` (`+`, monotone), `downward` (`−`, antitone) or `nonMonotonic` (`·`, no information),
composing as valences do. -/

namespace ContextPolarity

/-- The information order: `+ ⊑ ·` and `− ⊑ ·`. -/
def le : ContextPolarity → ContextPolarity → Prop
  | _, .nonMonotonic => True
  | .upward, .upward => True
  | .downward, .downward => True
  | _, _ => False

instance : DecidableRel le := fun a b => by
  cases a <;> cases b <;> first | exact isTrue trivial | exact isFalse not_false

instance : LE ContextPolarity := ⟨le⟩

instance decidableLE (a b : ContextPolarity) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (le a b))

instance : SemilatticeSup ContextPolarity where
  le := le
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [le]
  le_antisymm a b := by cases a <;> cases b <;> simp [le]
  sup a b := if a = b then a else .nonMonotonic
  le_sup_left a b := by cases a <;> cases b <;> simp [le]
  le_sup_right a b := by cases a <;> cases b <;> simp [le]
  sup_le a b c := by cases a <;> cases b <;> cases c <;> simp [le]

instance : OrderTop ContextPolarity where
  top := .nonMonotonic
  le_top a := by cases a <;> trivial

end ContextPolarity

/-! ### Marked types -/

/-- Simple types over base types `B`, with marked arrows
    ([icard-moss-tune-2017] Definition 3.1): `arr σ m τ` is the type of
    `m`-behaved functions from `σ` to `τ`. -/
inductive Ty (B : Type*) where
  | base : B → Ty B
  | arr : Ty B → ContextPolarity → Ty B → Ty B
  deriving DecidableEq

namespace Ty

variable {B : Type*}

/-- The subtyping order ([icard-moss-tune-2017] Definition 3.2):
    contravariant in domains, covariant in codomains and markings, so
    that every `+`- or `−`-typed function can also be considered
    `·`-typed. -/
protected inductive LE : Ty B → Ty B → Prop
  | base (b : B) : Ty.LE (.base b) (.base b)
  | arr {σ σ' τ τ' : Ty B} {m m' : ContextPolarity} :
      Ty.LE σ' σ → Ty.LE τ τ' → m ≤ m' →
      Ty.LE (.arr σ m τ) (.arr σ' m' τ')

instance : LE (Ty B) := ⟨Ty.LE⟩

protected theorem LE.refl : ∀ σ : Ty B, Ty.LE σ σ
  | .base b => .base b
  | .arr σ _ τ => .arr (Ty.LE.refl σ) (Ty.LE.refl τ) le_rfl

protected theorem LE.trans :
    ∀ {σ τ μ : Ty B}, Ty.LE σ τ → Ty.LE τ μ →
      Ty.LE σ μ
  | _, _, _, .base b, .base _ => .base b
  | _, _, _, .arr h₁ h₂ hm, .arr h₁' h₂' hm' =>
      .arr (h₁'.trans h₁) (h₂.trans h₂') (hm.trans hm')

protected theorem LE.antisymm :
    ∀ {σ τ : Ty B}, Ty.LE σ τ → Ty.LE τ σ → σ = τ
  | _, _, .base _, .base _ => rfl
  | _, _, .arr h₁ h₂ hm, .arr h₁' h₂' hm' => by
      rw [(h₁.antisymm h₁' : _ = _), h₂.antisymm h₂', hm.antisymm hm']

instance : PartialOrder (Ty B) where
  le_refl := Ty.LE.refl
  le_trans _ _ _ := Ty.LE.trans
  le_antisymm _ _ := Ty.LE.antisymm

@[simp] theorem base_le_base {b b' : B} : (Ty.base b : Ty B) ≤ .base b' ↔ b = b' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .base b⟩

@[simp] theorem not_base_le_arr {b : B} {σ τ : Ty B} {m : ContextPolarity} :
    ¬ (Ty.base b : Ty B) ≤ .arr σ m τ := fun h => by cases h

@[simp] theorem not_arr_le_base {b : B} {σ τ : Ty B} {m : ContextPolarity} :
    ¬ (Ty.arr σ m τ : Ty B) ≤ .base b := fun h => by cases h

@[simp] theorem arr_le_arr {σ σ' τ τ' : Ty B} {m m' : ContextPolarity} :
    (Ty.arr σ m τ : Ty B) ≤ .arr σ' m' τ' ↔ σ' ≤ σ ∧ τ ≤ τ' ∧ m ≤ m' :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›, ‹_›⟩, fun ⟨h₁, h₂, hm⟩ => .arr h₁ h₂ hm⟩

set_option warn.classDefReducibility false in
instance decidableLE [DecidableEq B] :
    ∀ σ τ : Ty B, Decidable (σ ≤ τ)
  | .base b, .base b' =>
      if h : b = b' then .isTrue (h ▸ .base b)
      else .isFalse fun hle => by cases hle; exact h rfl
  | .base _, .arr .. => .isFalse fun hle => by cases hle
  | .arr .., .base _ => .isFalse fun hle => by cases hle
  | .arr σ m τ, .arr σ' m' τ' =>
      match decidableLE σ' σ, decidableLE τ τ', ContextPolarity.decidableLE m m' with
      | .isTrue h₁, .isTrue h₂, .isTrue hm => .isTrue (.arr h₁ h₂ hm)
      | .isFalse h₁, _, _ => .isFalse fun hle => by cases hle; exact h₁ ‹_›
      | _, .isFalse h₂, _ => .isFalse fun hle => by cases hle; exact h₂ ‹_›
      | _, _, .isFalse hm => .isFalse fun hle => by cases hle; exact hm ‹_›
  termination_by σ τ => sizeOf σ + sizeOf τ

/-! ### Compatibility join and marking erasure -/

/-- The partial join of compatible types ([icard-moss-tune-2017]
    Definition 3.3): defined when the two types share their unmarked
    skeleton and their domains exactly, joining the markings along the
    codomain spine. -/
def sup? [DecidableEq B] : Ty B → Ty B → Option (Ty B)
  | .base b, .base b' => if b = b' then some (.base b) else none
  | .arr σ m τ, .arr σ' m' τ' =>
      if σ = σ' then (sup? τ τ').map (.arr σ (m ⊔ m')) else none
  | _, _ => none

@[simp] theorem sup?_self [DecidableEq B] :
    ∀ σ : Ty B, sup? σ σ = some σ
  | .base b => by simp [sup?]
  | .arr σ m τ => by simp [sup?, sup?_self τ]

/-- Both compatible types lie below their join. -/
theorem le_of_mem_sup?_left [DecidableEq B] :
    ∀ {σ τ μ : Ty B}, sup? σ τ = some μ → σ ≤ μ
  | .base b, .base b', _, h => by
      rw [sup?] at h
      split at h
      · cases h; exact .base b
      · exact absurd h (by simp)
  | .arr σ m τ, .arr σ' m' τ', _, h => by
      rw [sup?] at h
      split at h
      · rcases Option.map_eq_some_iff.mp h with ⟨κ, hκ, rfl⟩
        exact .arr (Ty.LE.refl σ) (le_of_mem_sup?_left hκ) le_sup_left
      · exact absurd h (by simp)

/-- Erase the markings along the codomain spine ([icard-moss-tune-2017]
    Definition 3.3, their `σ̂`). -/
def unmark : Ty B → Ty B
  | .base b => .base b
  | .arr σ _ τ => .arr σ .nonMonotonic (unmark τ)

/-- Every type embeds into its marking erasure. -/
theorem le_unmark : ∀ σ : Ty B, σ ≤ unmark σ
  | .base b => .base b
  | .arr σ _ τ => .arr (Ty.LE.refl σ) (le_unmark τ) le_top

end Ty

end NaturalLogic
