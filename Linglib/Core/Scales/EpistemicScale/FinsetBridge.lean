import Linglib.Core.Scales.EpistemicScale.Defs

/-!
# Set ↔ Finset bridge for epistemic scale proofs

Infrastructure for proving `Set (Fin n)` difference equalities by reducing them
to decidable `Finset (Fin n)` operations. This bridges the gap between the
Prop-valued `Set` operations used by `EpistemicSystemFA` and the decidable
`Finset` operations needed for automation.

## Main definitions

* `set_sdiff_fin` — tactic macro that proves `(A : Set (Fin n)) \ B = C` by
  normalizing Set literals to Finset coercions, computing the sdiff in Finset
  land, and closing by `decide`.
* `set_sdiff_eq_of_finset` — bridge lemma: given `A \ B = C` (by `decide` on
  `Finset`), concludes `(↑A : Set _) \ ↑B = ↑C`.
* `set_univ_sdiff_eq_of_finset` — variant for `Set.univ \ ↑B = ↑C`.

## Usage

These replace the manual `ext x; fin_cases x <;> simp [Set.mem_diff, ...]`
pattern used throughout the epistemic scale proofs. Every `sd_*` lemma in
`CancellationHelpers.lean` can be proved by `set_sdiff_fin`.
-/

namespace Core.Scale

/-- Prove `(↑A : Set (Fin n)) \ ↑B = ↑C` from the decidable Finset equality
    `A \ B = C`. The default argument `by decide` makes this zero-effort. -/
theorem set_sdiff_eq_of_finset {n : ℕ}
    (A B C : Finset (Fin n))
    (h : A \ B = C := by decide) :
    (↑A : Set (Fin n)) \ ↑B = ↑C := by
  rw [← Finset.coe_sdiff, h]

/-- Variant of `set_sdiff_eq_of_finset` for `Set.univ` as the left operand. -/
theorem set_univ_sdiff_eq_of_finset {n : ℕ}
    (B C : Finset (Fin n))
    (h : Finset.univ \ B = C := by decide) :
    (Set.univ : Set (Fin n)) \ ↑B = ↑C := by
  rw [← Finset.coe_univ, ← Finset.coe_sdiff, h]

/-- Tactic for proving `(A : Set (Fin n)) \ B = C` where A, B, C are Set
    literals or `Set.univ`. Normalizes to Finset coercions, computes the sdiff
    via kernel reduction, and closes by `rfl` or `decide`. Falls back to
    `ext x; fin_cases x` for edge cases. -/
macro "set_sdiff_fin" : tactic =>
  `(tactic| first
    | (simp only [← Finset.coe_univ, ← Finset.coe_insert, ← Finset.coe_singleton,
        ← Finset.coe_empty, ← Finset.coe_sdiff];
       first | rfl | (congr 1; decide))
    | (ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]))

end Core.Scale
