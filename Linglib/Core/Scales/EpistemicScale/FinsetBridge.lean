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

## Finset-native FA operations (Phase 2)

* `EpistemicSystemFA.geFS` — `sys.ge` lifted to Finset arguments
* `geFS_additive` — additivity with automatic Finset sdiff computation
* `geFS_trans`, `geFS_mono`, `geFS_total`, `geFS_refl` — FA axioms in Finset land

These are designed for use in compact chamber proofs (Phase 4) where all
reasoning happens in Finset land:
- `geFS_mono {0} {0, 2}` — subset by `decide`, no `fin_cases` proof
- `(geFS_additive {1,2} {1,3}).mpr h23` — no `sd_*` lemmas needed

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

-- ── Finset-native FA operations ──────────────────

variable {n : ℕ}

/-- Finset-native comparison: `sys.geFS A B` means `sys.ge ↑A ↑B`. -/
def EpistemicSystemFA.geFS (sys : EpistemicSystemFA (Fin n))
    (A B : Finset (Fin n)) : Prop := sys.ge ↑A ↑B

/-- Additivity in Finset land: `geFS A B ↔ geFS (A \ B) (B \ A)`.
    Set differences are automatically computed on Finsets — no `sd_*` lemmas. -/
theorem EpistemicSystemFA.geFS_additive (sys : EpistemicSystemFA (Fin n))
    (A B : Finset (Fin n)) :
    sys.geFS A B ↔ sys.geFS (A \ B) (B \ A) := by
  show sys.ge ↑A ↑B ↔ sys.ge ↑(A \ B) ↑(B \ A)
  rw [Finset.coe_sdiff, Finset.coe_sdiff]
  exact sys.additive ↑A ↑B

/-- Transitivity in Finset land. -/
theorem EpistemicSystemFA.geFS_trans (sys : EpistemicSystemFA (Fin n))
    {A B C : Finset (Fin n)} :
    sys.geFS A B → sys.geFS B C → sys.geFS A C :=
  sys.trans ↑A ↑B ↑C

/-- Monotonicity in Finset land: `A ⊆ B → geFS B A`.
    The subset check is decidable on Finsets (default: `by decide`). -/
theorem EpistemicSystemFA.geFS_mono (sys : EpistemicSystemFA (Fin n))
    (A B : Finset (Fin n)) (h : A ⊆ B := by decide) :
    sys.geFS B A :=
  sys.mono ↑A ↑B (Finset.coe_subset.mpr h)

/-- Totality in Finset land. -/
theorem EpistemicSystemFA.geFS_total (sys : EpistemicSystemFA (Fin n))
    (A B : Finset (Fin n)) :
    sys.geFS A B ∨ sys.geFS B A :=
  sys.total ↑A ↑B

/-- Reflexivity in Finset land. -/
theorem EpistemicSystemFA.geFS_refl (sys : EpistemicSystemFA (Fin n))
    (A : Finset (Fin n)) :
    sys.geFS A A :=
  sys.refl ↑A

-- ── Derivation combinators for ¬geFS ─────────────

/-- ¬geFS A B from ¬geFS A C and geFS B C (transitivity on the right).
    If A can't beat C, and B ≥ C, then A can't beat B. -/
theorem ngeFS_of_trans_right (sys : EpistemicSystemFA (Fin n))
    {A B C : Finset (Fin n)}
    (hng : ¬sys.geFS A C) (hge : sys.geFS B C) :
    ¬sys.geFS A B :=
  fun h => hng (sys.geFS_trans h hge)

/-- ¬geFS A B from ¬geFS C B and geFS C A (transitivity on the left).
    If C can't beat B, and C ≥ A, then A can't beat B. -/
theorem ngeFS_of_trans_left (sys : EpistemicSystemFA (Fin n))
    {A B C : Finset (Fin n)}
    (hng : ¬sys.geFS C B) (hge : sys.geFS C A) :
    ¬sys.geFS A B :=
  fun h => hng (sys.geFS_trans hge h)

/-- ¬geFS A B from ¬geFS A C where C ⊆ B (monotonicity on the right).
    Subset check is `by decide`. -/
theorem ngeFS_of_mono_right (sys : EpistemicSystemFA (Fin n))
    {A C : Finset (Fin n)} (B : Finset (Fin n))
    (hng : ¬sys.geFS A C) (h : C ⊆ B := by decide) :
    ¬sys.geFS A B :=
  ngeFS_of_trans_right sys hng (sys.geFS_mono C B h)

/-- ¬geFS A B from ¬geFS C B where A ⊆ C (monotonicity on the left).
    Subset check is `by decide`. -/
theorem ngeFS_of_mono_left (sys : EpistemicSystemFA (Fin n))
    {C B : Finset (Fin n)} (A : Finset (Fin n))
    (hng : ¬sys.geFS C B) (h : A ⊆ C := by decide) :
    ¬sys.geFS A B :=
  ngeFS_of_trans_left sys hng (sys.geFS_mono A C h)

/-- ¬geFS A B via positivity: if additivity reduces geFS A B to geFS ∅ {i},
    and hpos says ¬geFS ∅ {i}, contradiction. The sdiff equalities
    `A \ B = ∅` and `B \ A = {i}` are checked by `decide`. -/
theorem ngeFS_via_hpos (sys : EpistemicSystemFA (Fin n))
    {A B : Finset (Fin n)} (i : Fin n)
    (hpos : ¬sys.geFS ∅ {i})
    (hAB : A \ B = ∅ := by decide) (hBA : B \ A = {i} := by decide) :
    ¬sys.geFS A B := fun h => by
  have := (sys.geFS_additive A B).mp h
  rw [hAB, hBA] at this
  exact hpos this

end Core.Scale
