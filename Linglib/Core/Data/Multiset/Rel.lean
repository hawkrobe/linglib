/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Multiset.ZeroCons

/-!
# Lifting a relation to multisets: list-level reading and transitivity

Two facts about `Multiset.Rel` that mathlib's `Mathlib/Data/Multiset/ZeroCons.lean` lacks: on
coerced lists it is `Forall₂ r` followed by a permutation, the `Rel` counterpart of
`Multiset.coe_eq_coe`, and it is transitive whenever `r` is transitive on the members, the
counterpart of `Multiset.rel_refl_of_refl_on` that generalizes `Multiset.Rel.trans`.

## Main statements

* `Multiset.rel_coe_iff`: `Rel r ↑l₁ ↑l₂ ↔ (Forall₂ r ∘r Perm) l₁ l₂`.
* `Multiset.rel_trans_of_trans_on`: transitivity of `Rel r` from transitivity of `r` on the
  members.

[UPSTREAM] candidates for `Mathlib/Data/Multiset/ZeroCons.lean`.
-/

@[expose] public section

namespace Multiset

local infixr:80 " ∘r " => Relation.Comp

variable {α β : Type*}

/-- `Rel r` on coerced lists is componentwise `r` followed by a permutation. -/
theorem rel_coe_iff {r : α → β → Prop} {l₁ : List α} {l₂ : List β} :
    Rel r l₁ l₂ ↔ (List.Forall₂ r ∘r List.Perm) l₁ l₂ := by
  constructor
  · induction l₁ generalizing l₂ with
    | nil => exact fun h ↦ ⟨[], .nil, coe_eq_coe.1 (rel_zero_left.1 h).symm⟩
    | cons a l₁ ih =>
      intro h
      obtain ⟨b, bs, hab, hr, hbs⟩ := rel_cons_left.1 (cons_coe a l₁ ▸ h)
      induction bs using Quotient.inductionOn
      obtain ⟨l, hf, hp⟩ := ih hr
      exact ⟨b :: l, hf.cons hab, (hp.cons b).trans (coe_eq_coe.1 hbs).symm⟩
  · rintro ⟨l, hf, hp⟩
    rw [← coe_eq_coe.2 hp]
    clear hp
    induction hf with
    | nil => exact .zero
    | cons h _ ih => exact .cons h ih

theorem rel_trans_of_trans_on {r : α → α → Prop} {s t u : Multiset α}
    (ht : ∀ x ∈ s, ∀ y ∈ t, ∀ z ∈ u, r x y → r y z → r x z)
    (h₁ : Rel r s t) (h₂ : Rel r t u) : Rel r s u := by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.mp h₁, rel_zero_left.mp h₂, rel_zero_left]
  | cons y t ih =>
    obtain ⟨x, s', hxy, hs, rfl⟩ := rel_cons_right.mp h₁
    obtain ⟨z, u', hyz, hu, rfl⟩ := rel_cons_left.mp h₂
    exact .cons (ht x (mem_cons_self ..) y (mem_cons_self ..) z (mem_cons_self ..) hxy hyz)
      (ih (fun a ha b hb c hc ↦ ht a (mem_cons_of_mem ha) b (mem_cons_of_mem hb) c
        (mem_cons_of_mem hc)) hs hu)

end Multiset
