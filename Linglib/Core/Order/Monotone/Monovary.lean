/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Monotone.Monovary
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Image

/-!
# `MonovaryOn` on `singleton`, `union`, `insert`, and `image`

`[UPSTREAM]` mathlib's `MonovaryOn` API (`Mathlib/Order/Monotone/Monovary.lean`)
has `empty` / `subset` / `comp_right` / `comp_monotone_left`, but lacks the
structural set-building lemmas that `Set.Pairwise` enjoys
(`Set.pairwise_singleton` / `pairwise_union` / `pairwise_insert`). This file fills
the gap, modelled on the `Set.Pairwise` family lemma-for-lemma, plus the `image`
companion of `MonovaryOn.comp_right` (which is the preimage form). Each pairs with
its `AntivaryOn` twin, as every lemma in the mathlib file does.

Upstream home: `section Preorder` of `Mathlib/Order/Monotone/Monovary.lean`,
beside `MonovaryOn.empty` and `MonovaryOn.comp_right`.

## Main results

* `monovaryOn_singleton` / `monovaryOn_union` / `monovaryOn_insert` — the
  `Set.pairwise_*` analogues (and `antivaryOn_*` twins).
* `monovaryOn_image` — `MonovaryOn f g (k '' u) ↔ MonovaryOn (f ∘ k) (g ∘ k) u`,
  the image companion of `MonovaryOn.comp_right` (and `antivaryOn_image` twin).
-/

variable {ι ι' α β : Type*} [Preorder α] [Preorder β] {f : ι → α} {g : ι → β}
  {s t : Set ι}

/-! ### Monovary -/

/-- `MonovaryOn` holds vacuously on a singleton: there is only one index. -/
@[simp] theorem monovaryOn_singleton (a : ι) : MonovaryOn f g {a} := by
  simp [MonovaryOn]

/-- `MonovaryOn` on a union: monovary on each part, plus neither part inverts the
    order against the other. The `Monovary` analogue of `Set.pairwise_union`. -/
theorem monovaryOn_union : MonovaryOn f g (s ∪ t) ↔ MonovaryOn f g s ∧ MonovaryOn f g t ∧
    ∀ a ∈ s, ∀ b ∈ t, (g a < g b → f a ≤ f b) ∧ (g b < g a → f b ≤ f a) := by
  grind [MonovaryOn]

/-- `MonovaryOn` on `insert a s`. The `Monovary` analogue of `Set.pairwise_insert`. -/
theorem monovaryOn_insert {a : ι} :
    MonovaryOn f g (insert a s) ↔
      MonovaryOn f g s ∧ ∀ b ∈ s, (g a < g b → f a ≤ f b) ∧ (g b < g a → f b ≤ f a) := by
  grind [MonovaryOn]

/-- `MonovaryOn` transports across an image: `f, g` monovary on `k '' u` iff
    `f ∘ k, g ∘ k` monovary on `u`. The image companion of `MonovaryOn.comp_right`
    (the preimage form). -/
theorem monovaryOn_image (k : ι' → ι) (u : Set ι') :
    MonovaryOn f g (k '' u) ↔ MonovaryOn (f ∘ k) (g ∘ k) u := by
  grind [MonovaryOn]

/-! ### Antivary -/

/-- `AntivaryOn` holds vacuously on a singleton: there is only one index. -/
@[simp] theorem antivaryOn_singleton (a : ι) : AntivaryOn f g {a} := by
  simp [AntivaryOn]

/-- `AntivaryOn` on a union. The `Antivary` analogue of `Set.pairwise_union`. -/
theorem antivaryOn_union : AntivaryOn f g (s ∪ t) ↔ AntivaryOn f g s ∧ AntivaryOn f g t ∧
    ∀ a ∈ s, ∀ b ∈ t, (g a < g b → f b ≤ f a) ∧ (g b < g a → f a ≤ f b) := by
  grind [AntivaryOn]

/-- `AntivaryOn` on `insert a s`. The `Antivary` analogue of `Set.pairwise_insert`. -/
theorem antivaryOn_insert {a : ι} :
    AntivaryOn f g (insert a s) ↔
      AntivaryOn f g s ∧ ∀ b ∈ s, (g a < g b → f b ≤ f a) ∧ (g b < g a → f a ≤ f b) := by
  grind [AntivaryOn]

/-- `AntivaryOn` transports across an image. The image companion of
    `AntivaryOn.comp_right`. -/
theorem antivaryOn_image (k : ι' → ι) (u : Set ι') :
    AntivaryOn f g (k '' u) ↔ AntivaryOn (f ∘ k) (g ∘ k) u := by
  grind [AntivaryOn]
