import Mathlib.Data.Part

/-!
# Left-biased choice of partial values

`Part.or` is the `Part` analogue of `Option.or`: `p.or q` is defined
wherever either argument is, with the left taking precedence.
Noncomputable, since it decides `p.Dom`; `Flat.or` is its computable
twin on `Option`-carried partial values. An `[UPSTREAM]` candidate for
`Mathlib/Data/Part.lean`.
-/

namespace Part

variable {α : Type*} {p q r : Part α} {a : α}

open Classical in
/-- The left-biased choice of two partial values: defined wherever
either is, with the left taking precedence. -/
protected noncomputable def or (p q : Part α) : Part α :=
  if p.Dom then p else q

@[simp] theorem or_dom : (p.or q).Dom ↔ p.Dom ∨ q.Dom := by
  by_cases h : p.Dom <;> simp [Part.or, h]

theorem mem_or_iff : a ∈ p.or q ↔ a ∈ p ∨ ¬p.Dom ∧ a ∈ q := by
  by_cases h : p.Dom
  · simp [Part.or, h]
  · simp [Part.or, eq_none_iff'.mpr h]

@[simp] theorem none_or (q : Part α) : Part.none.or q = q :=
  if_neg not_none_dom

@[simp] theorem or_none (p : Part α) : p.or none = p := by
  by_cases h : p.Dom
  · simp [Part.or, h]
  · simp [Part.or, eq_none_iff'.mpr h]

@[simp] theorem some_or (a : α) (q : Part α) : (Part.some a).or q = Part.some a :=
  if_pos trivial

@[simp] theorem bot_or (q : Part α) : (⊥ : Part α).or q = q :=
  none_or q

@[simp] theorem or_bot (p : Part α) : p.or ⊥ = p :=
  or_none p

@[simp] theorem or_self (p : Part α) : p.or p = p :=
  ite_self p

theorem or_assoc (p q r : Part α) : (p.or q).or r = p.or (q.or r) := by
  by_cases hp : p.Dom <;> by_cases hq : q.Dom <;> simp [Part.or, hp, hq]

theorem le_or_left : p ≤ p.or q := fun _ ha => mem_or_iff.mpr (.inl ha)

theorem or_le (hp : p ≤ r) (hq : q ≤ r) : p.or q ≤ r := fun a ha =>
  (mem_or_iff.mp ha).elim (hp a) fun h => hq a h.2

end Part
