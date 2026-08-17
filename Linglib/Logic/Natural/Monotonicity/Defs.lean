/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice

/-!
# Marked types for the monotonicity calculus

This file defines the type system of the [icard-moss-tune-2017]
monotonicity calculus: simple types over a set of base types, with
each arrow marked as monotone (`+`), antitone (`−`), or unmarked
(`·`).

## Main declarations

* `Marking`: the three markings — a commutative monoid under valence
  composition (`+` the identity, `·` absorbing), and a
  join-semilattice with `·` on top.
* `Ty`: marked simple types, with the subtyping order — contravariant
  in domains, covariant in codomains and markings — decidable over a
  `DecidableEq` base.
* `Ty.sup?`: the partial join of compatible types.
* `Ty.unmark`: erasure of the markings along the codomain spine.

## References

* [icard-moss-tune-2017] — Definitions 3.1–3.3.
-/

namespace NaturalLogic

/-! ### Markings -/

/-- A monotonicity marking: `pos` (`+`, monotone), `neg` (`−`, antitone),
    or `unmarked` (`·`, no information) ([icard-moss-tune-2017]
    Definition 3.1). -/
inductive Marking where
  | pos
  | neg
  | unmarked
  deriving DecidableEq, Repr

namespace Marking

/-- Valence composition: signs multiply, `·` absorbs. -/
def comp : Marking → Marking → Marking
  | .pos, m => m
  | m, .pos => m
  | .neg, .neg => .pos
  | _, _ => .unmarked

instance : Mul Marking := ⟨comp⟩
instance : One Marking := ⟨.pos⟩

instance : CommMonoid Marking where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

/-- The information order: `+ ⊑ ·` and `− ⊑ ·`. -/
def le : Marking → Marking → Prop
  | _, .unmarked => True
  | .pos, .pos => True
  | .neg, .neg => True
  | _, _ => False

instance : DecidableRel le := fun a b => by
  cases a <;> cases b <;> first | exact isTrue trivial | exact isFalse not_false

instance : LE Marking := ⟨le⟩

instance decidableLE (a b : Marking) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (le a b))

instance : SemilatticeSup Marking where
  le := le
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [le]
  le_antisymm a b := by cases a <;> cases b <;> simp [le]
  sup a b := if a = b then a else .unmarked
  le_sup_left a b := by cases a <;> cases b <;> simp [le]
  le_sup_right a b := by cases a <;> cases b <;> simp [le]
  sup_le a b c := by cases a <;> cases b <;> cases c <;> simp [le]

instance : OrderTop Marking where
  top := .unmarked
  le_top a := by cases a <;> trivial

end Marking

/-! ### Marked types -/

/-- Simple types over base types `B`, with marked arrows
    ([icard-moss-tune-2017] Definition 3.1): `arr σ m τ` is the type of
    `m`-behaved functions from `σ` to `τ`. -/
inductive Ty (B : Type*) where
  | base : B → Ty B
  | arr : Ty B → Marking → Ty B → Ty B
  deriving DecidableEq

namespace Ty

variable {B : Type*}

/-- The subtyping order ([icard-moss-tune-2017] Definition 3.2):
    contravariant in domains, covariant in codomains and markings, so
    that every `+`- or `−`-typed function can also be considered
    `·`-typed. -/
protected inductive LE : Ty B → Ty B → Prop
  | base (b : B) : Ty.LE (.base b) (.base b)
  | arr {σ σ' τ τ' : Ty B} {m m' : Marking} :
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

@[simp] theorem not_base_le_arr {b : B} {σ τ : Ty B} {m : Marking} :
    ¬ (Ty.base b : Ty B) ≤ .arr σ m τ := fun h => by cases h

@[simp] theorem not_arr_le_base {b : B} {σ τ : Ty B} {m : Marking} :
    ¬ (Ty.arr σ m τ : Ty B) ≤ .base b := fun h => by cases h

@[simp] theorem arr_le_arr {σ σ' τ τ' : Ty B} {m m' : Marking} :
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
      match decidableLE σ' σ, decidableLE τ τ', Marking.decidableLE m m' with
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
  | .arr σ _ τ => .arr σ .unmarked (unmark τ)

/-- Every type embeds into its marking erasure. -/
theorem le_unmark : ∀ σ : Ty B, σ ≤ unmark σ
  | .base b => .base b
  | .arr σ _ τ => .arr (Ty.LE.refl σ) (le_unmark τ) le_top

end Ty

end NaturalLogic
