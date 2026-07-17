import Linglib.Core.Order.PartialUnify
import Mathlib.Data.Part

/-!
# Left-biased choice of partial values

`Part.or` is the `Part` analogue of `Option.or`: `p.or q` is defined
wherever either argument is, with the left taking precedence.
Noncomputable, since it decides `p.Dom`; `Flat.or` is its computable
twin on `Option`-carried partial values. Also the order facts of the
flat domain: definedness is monotone (`dom_mono`), descent without
domain growth is equality (`eq_of_le_of_dom`), and two partial values
are bounded above exactly when they agree wherever both are defined
(`compat_iff`), with `p.or q` the witnessing bound. `[UPSTREAM]`
candidates for `Mathlib/Data/Part.lean`.
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

@[simp] theorem none_or : Part.none.or q = q :=
  if_neg not_none_dom

@[simp] theorem or_none : p.or none = p := by
  by_cases h : p.Dom
  · simp [Part.or, h]
  · simp [Part.or, eq_none_iff'.mpr h]

@[simp] theorem some_or : (Part.some a).or q = Part.some a :=
  if_pos trivial

@[simp] theorem bot_or : (⊥ : Part α).or q = q :=
  none_or

@[simp] theorem or_bot : p.or ⊥ = p :=
  or_none

@[simp] theorem or_self : p.or p = p :=
  ite_self p

theorem or_assoc : (p.or q).or r = p.or (q.or r) := by
  by_cases hp : p.Dom <;> by_cases hq : q.Dom <;> simp [Part.or, hp, hq]

theorem le_or_left : p ≤ p.or q := fun _ ha => mem_or_iff.mpr (.inl ha)

theorem or_le (hp : p ≤ r) (hq : q ≤ r) : p.or q ≤ r := fun a ha =>
  (mem_or_iff.mp ha).elim (hp a) fun h => hq a h.2

theorem dom_mono (h : p ≤ q) (hd : p.Dom) : q.Dom :=
  dom_iff_mem.mpr ⟨_, h _ (get_mem hd)⟩

theorem eq_of_le_of_dom (h : p ≤ q) (hd : q.Dom → p.Dom) : p = q :=
  Part.ext fun a => ⟨h a, fun ha =>
    have hp := hd (dom_iff_mem.mpr ⟨a, ha⟩)
    mem_unique (h _ (get_mem hp)) ha ▸ get_mem hp⟩

theorem le_or_right_of_agree (hag : ∀ a b, a ∈ p → b ∈ q → a = b) :
    q ≤ p.or q := fun b hb => mem_or_iff.mpr <| or_iff_not_imp_left.mpr
  fun hp => ⟨fun hd => hp (hag _ b (get_mem hd) hb ▸ get_mem hd), hb⟩

/-- Two partial values are compatible — bounded above in the flat
order — exactly when they agree wherever both are defined. -/
theorem compat_iff : Compat p q ↔ ∀ a b, a ∈ p → b ∈ q → a = b := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hp, hq⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    exact fun a b ha hb => mem_unique (hp a ha) (hq b hb)
  · exact fun hag => ⟨p.or q, PartialUnify.mem_upperBounds_pair.mpr
      ⟨le_or_left, le_or_right_of_agree hag⟩⟩

theorem le_or_right (h : Compat p q) : q ≤ p.or q :=
  le_or_right_of_agree (compat_iff.mp h)

theorem compat_or_left (hp : Compat p r) (hq : Compat q r) : Compat (p.or q) r :=
  compat_iff.mpr fun a b ha hb => (mem_or_iff.mp ha).elim
    (fun h => compat_iff.mp hp a b h hb) fun h => compat_iff.mp hq a b h.2 hb

end Part
