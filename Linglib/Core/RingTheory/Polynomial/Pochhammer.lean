/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The rising factorial as a product

`ascPochhammer_eval_eq_prod_range`: `(ascPochhammer R n).eval r = r (r + 1) ⋯ (r + n - 1)`, the
rising-factorial counterpart of mathlib's `descPochhammer_eval_eq_prod_range`.

[UPSTREAM] candidate for `Mathlib.RingTheory.Polynomial.Pochhammer`.
-/

@[expose] public section

theorem ascPochhammer_eval_eq_prod_range {R : Type*} [CommSemiring R] (n : ℕ) (r : R) :
    (ascPochhammer R n).eval r = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]
