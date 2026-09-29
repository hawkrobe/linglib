/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Filter

/-!
# Filtering a product of multisets

`Multiset.filter_product`: filtering `s ×ˢ t` by a predicate on each coordinate filters each
factor. The `Multiset` analogue of `Finset.filter_product`. `[UPSTREAM]` candidate.
-/

@[expose] public section

namespace Multiset

variable {α β : Type*} {s : Multiset α} {t : Multiset β}

theorem filter_product (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
    (s ×ˢ t).filter (fun x ↦ p x.1 ∧ q x.2) = s.filter p ×ˢ t.filter q := by
  induction s using Multiset.induction with
  | empty => rfl
  | cons a s ih =>
    by_cases ha : p a <;>
      simp [cons_product, filter_add, ih, filter_map, ha, filter_cons_of_neg, filter_cons_of_pos]

end Multiset
