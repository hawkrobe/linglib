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
@[reducible] def EpistemicSystemFA.geFS (sys : EpistemicSystemFA (Fin n))
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

-- ── Set-land derivation combinators for ¬ge ──────

/-- ¬ge A B from ¬ge A C and ge B C (transitivity on the right). -/
theorem nge_of_trans_right_set (sys : EpistemicSystemFA (Fin n))
    {A B C : Set (Fin n)}
    (hng : ¬sys.ge A C) (hge : sys.ge B C) :
    ¬sys.ge A B :=
  fun h => hng (sys.trans _ _ _ h hge)

/-- ¬ge A B from ¬ge C B and ge C A (transitivity on the left). -/
theorem nge_of_trans_left_set (sys : EpistemicSystemFA (Fin n))
    {A B C : Set (Fin n)}
    (hng : ¬sys.ge C B) (hge : sys.ge C A) :
    ¬sys.ge A B :=
  fun h => hng (sys.trans _ _ _ hge h)

/-- ¬ge A B from ¬ge A C where C ⊆ B (monotonicity on the right).
    Subset check closed by `intro x hx; fin_cases x <;> simp_all`. -/
theorem nge_of_mono_right_set (sys : EpistemicSystemFA (Fin n))
    {A C B : Set (Fin n)}
    (hng : ¬sys.ge A C) (h : C ⊆ B) :
    ¬sys.ge A B :=
  nge_of_trans_right_set sys hng (sys.mono C B h)

/-- ¬ge A B from ¬ge C B where A ⊆ C (monotonicity on the left). -/
theorem nge_of_mono_left_set (sys : EpistemicSystemFA (Fin n))
    {C B A : Set (Fin n)}
    (hng : ¬sys.ge C B) (h : A ⊆ C) :
    ¬sys.ge A B :=
  nge_of_trans_left_set sys hng (sys.mono A C h)

/-- ¬ge A B via positivity: if additivity reduces to ge ∅ {i},
    and hpos says ¬ge ∅ {i}, contradiction. -/
theorem nge_via_hpos_set (sys : EpistemicSystemFA (Fin n))
    {A B : Set (Fin n)} (i : Fin n)
    (hpos : ¬sys.ge ∅ {i})
    (hAB : A \ B = ∅) (hBA : B \ A = {i}) :
    ¬sys.ge A B := fun h => by
  have := (sys.additive A B).mp h
  rw [hAB, hBA] at this
  exact hpos this

/-- ¬ge A B via positivity (∀-quantified hpos variant): if A ⊆ B (i.e., A\B = ∅),
    additivity gives ge ∅ (B\A), and ge_empty_contra derives contradiction
    from hpos. Takes the full `∀ i, ¬ge ∅ {i}` to avoid metavar issues in
    tactic search. -/
theorem nge_via_hpos_all (sys : EpistemicSystemFA (Fin n))
    {A B : Set (Fin n)}
    (hpos : ∀ i : Fin n, ¬sys.ge ∅ {i})
    (hAB : A \ B = ∅) (hBA_ne : (B \ A).Nonempty) :
    ¬sys.ge A B := fun h => by
  have h1 := (sys.additive A B).mp h
  rw [hAB] at h1
  obtain ⟨x, hx⟩ := hBA_ne
  exact hpos x (sys.trans _ _ _ h1 (sys.mono _ _ (Set.singleton_subset_iff.mpr hx)))

/-- ¬ge A B when there exists C with ge C A and C ⊆ B: trans gives ge C B,
    additive gives ge (C\B) (B\C) = ge ∅ (B\C), contradicting positivity.
    Combines trans + additive + positivity in one step. -/
theorem nge_of_trans_overlap (sys : EpistemicSystemFA (Fin n))
    (hpos : ∀ i : Fin n, ¬sys.ge ∅ {i})
    {A B C : Set (Fin n)}
    (hge : sys.ge C A) (hCB : C \ B = ∅) (hBCne : (B \ C).Nonempty)
    : ¬sys.ge A B := fun h => by
  have h1 := sys.trans _ _ _ hge h  -- ge C B
  have h2 := (sys.additive C B).mp h1
  rw [hCB] at h2  -- ge ∅ (B\C)
  obtain ⟨x, hx⟩ := hBCne
  exact hpos x (sys.trans _ _ _ h2 (sys.mono _ _ (Set.singleton_subset_iff.mpr hx)))

/-- ¬ge A B from ¬ge C B when ge C A follows from additivity:
    ge (C\A) (A\C) → ge C A (by additive.mpr) → trans with assumed ge A B → ge C B →
    contradiction with ¬ge C B. -/
theorem nge_of_additive_trans_left (sys : EpistemicSystemFA (Fin n))
    {A B C D E : Set (Fin n)}
    (hng : ¬sys.ge C B)
    (hge_de : sys.ge D E)
    (hd : C \ A = D) (he : A \ C = E)
    : ¬sys.ge A B :=
  fun h => hng (sys.trans _ _ _ ((sys.additive C A).mpr (by rw [hd, he]; exact hge_de)) h)

/-- ¬ge A B from ¬ge (A\B) (B\A) via the additive axiom (mp direction).
    If ge A B held, additive.mp would give ge (A\B) (B\A), contradiction. -/
theorem nge_of_additive_mp (sys : EpistemicSystemFA (Fin n))
    {A B D E : Set (Fin n)}
    (hng : ¬sys.ge D E)
    (hd : A \ B = D) (he : B \ A = E)
    : ¬sys.ge A B :=
  fun h => by
    have := (sys.additive A B).mp h
    rw [hd, he] at this
    exact hng this

/-- ¬ge A B via double additive: use additive.mpr to get ge C A from ge (C\A) (A\C),
    then trans with assumed ge A B gives ge C B, then additive.mp on ge C B gives
    ge (C\B) (B\C), which contradicts ¬ge (C\B) (B\C). -/
theorem nge_of_double_additive (sys : EpistemicSystemFA (Fin n))
    {A B C D1 E1 D2 E2 : Set (Fin n)}
    (hge_d1e1 : sys.ge D1 E1)
    (hd1 : C \ A = D1) (he1 : A \ C = E1)
    (hng_d2e2 : ¬sys.ge D2 E2)
    (hd2 : C \ B = D2) (he2 : B \ C = E2)
    : ¬sys.ge A B :=
  fun h => by
    have hca : sys.ge C A := (sys.additive C A).mpr (by rw [hd1, he1]; exact hge_d1e1)
    have hcb := sys.trans _ _ _ hca h
    have hred := (sys.additive C B).mp hcb
    rw [hd2, he2] at hred
    exact hng_d2e2 hred

/-- ge B A via one additive step + one trans step: derive ge B C from
    ge (B\C) (C\B) via additive.mpr, then chain with ge C A in context. -/
theorem ge_of_additive_trans (sys : EpistemicSystemFA (Fin n))
    {B C A D E : Set (Fin n)}
    (hge_de : sys.ge D E)
    (hd : B \ C = D) (he : C \ B = E)
    (hge_ca : sys.ge C A)
    : sys.ge B A :=
  sys.trans _ _ _ ((sys.additive B C).mpr (by rw [hd, he]; exact hge_de)) hge_ca

/-- ge B A via two additive steps through bridge set C:
    ge B C from ge (B\C) (C\B), ge C A from ge (C\A) (A\C). -/
theorem ge_of_double_additive_pos (sys : EpistemicSystemFA (Fin n))
    {B C A D1 E1 D2 E2 : Set (Fin n)}
    (hge_d1e1 : sys.ge D1 E1)
    (hd1 : B \ C = D1) (he1 : C \ B = E1)
    (hge_d2e2 : sys.ge D2 E2)
    (hd2 : C \ A = D2) (he2 : A \ C = E2)
    : sys.ge B A :=
  sys.trans _ _ _
    ((sys.additive B C).mpr (by rw [hd1, he1]; exact hge_d1e1))
    ((sys.additive C A).mpr (by rw [hd2, he2]; exact hge_d2e2))

/-- ¬ge A B via trans to superset: if ge B C and A ⊆ C (A\C = ∅),
    then ge A B → ge A C → ge ∅ (C\A) → contradiction with hpos. -/
theorem nge_of_trans_superset (sys : EpistemicSystemFA (Fin n))
    (hpos : ∀ i : Fin n, ¬sys.ge ∅ {i})
    {A B C : Set (Fin n)}
    (hge : sys.ge B C) (hAC : A \ C = ∅) (hCA_ne : (C \ A).Nonempty)
    : ¬sys.ge A B := fun h => by
  have h1 := sys.trans _ _ _ h hge  -- ge A C
  have h2 := (sys.additive A C).mp h1
  rw [hAC] at h2  -- ge ∅ (C\A)
  obtain ⟨x, hx⟩ := hCA_ne
  exact hpos x (sys.trans _ _ _ h2 (sys.mono _ _ (Set.singleton_subset_iff.mpr hx)))

end Core.Scale
