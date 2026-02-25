import Linglib.Core.Scales.EpistemicScale.Defs

/-!
# Theorem 8a for Fin 4 — Direct case-split approach

The proof uses direct case-splitting with explicit rational witnesses,
paralleling the proven Fin 3 approach in Defs.lean. After handling null
elements (reducing to Fin 3), the all-non-null case proceeds by:

1. WLOG sort singletons: find a permutation σ so that
   ge({0})({1}), ge({1})({2}), ge({2})({3}).
2. Case-split on tie/strict boundaries between consecutive elements.
3. Within each partition type, case-split on free multi-element comparisons.
4. At each leaf, provide an explicit rational witness and verify via `fin4_dispatch`.
-/

namespace Core.Scale

attribute [local instance] Classical.propDecidable

-- ═══════════════════════════════════════════════════════════════
-- § 1. Null case helpers
-- ═══════════════════════════════════════════════════════════════

/-- If element 0 is null, reduce to Fin 3. Need a non-null witness among {1,2,3}. -/
private theorem fin4_null0 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : sys.ge ∅ {(0 : Fin 4)})
    (hn1 : ¬sys.ge ∅ {(1 : Fin 4)}) :
    ∃ m : FinAddMeasure (Fin 4), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  null_elem_reduce sys hn0 ⟨0, hn1⟩ theorem8a_fin3

private theorem fin4_null0' (sys : EpistemicSystemFA (Fin 4))
    (hn0 : sys.ge ∅ {(0 : Fin 4)})
    (hn1 : sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) :
    ∃ m : FinAddMeasure (Fin 4), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  null_elem_reduce sys hn0 ⟨1, hn2⟩ theorem8a_fin3

private theorem fin4_null0'' (sys : EpistemicSystemFA (Fin 4))
    (hn0 : sys.ge ∅ {(0 : Fin 4)})
    (hn1 : sys.ge ∅ {(1 : Fin 4)})
    (hn2 : sys.ge ∅ {(2 : Fin 4)})
    (hn3 : ¬sys.ge ∅ {(3 : Fin 4)}) :
    ∃ m : FinAddMeasure (Fin 4), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  null_elem_reduce sys hn0 ⟨2, hn3⟩ theorem8a_fin3

-- ═══════════════════════════════════════════════════════════════
-- § 2. Measure construction
-- ═══════════════════════════════════════════════════════════════

private noncomputable def measure_fin4 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) : FinAddMeasure (Fin 4) where
  mu := fun A =>
    (if (0 : Fin 4) ∈ A then a else 0) +
    (if (1 : Fin 4) ∈ A then b else 0) +
    (if (2 : Fin 4) ∈ A then c else 0) +
    (if (3 : Fin 4) ∈ A then 1 - a - b - c else 0)
  nonneg := fun A => by
    apply add_nonneg; apply add_nonneg; apply add_nonneg
    · split <;> [exact ha; exact le_refl _]
    · split <;> [exact hb; exact le_refl _]
    · split <;> [exact hc; exact le_refl _]
    · split <;> [linarith; exact le_refl _]
  additive := fun A B hdisj => by
    by_cases h0A : (0 : Fin 4) ∈ A <;> by_cases h0B : (0 : Fin 4) ∈ B <;>
    by_cases h1A : (1 : Fin 4) ∈ A <;> by_cases h1B : (1 : Fin 4) ∈ B <;>
    by_cases h2A : (2 : Fin 4) ∈ A <;> by_cases h2B : (2 : Fin 4) ∈ B <;>
    by_cases h3A : (3 : Fin 4) ∈ A <;> by_cases h3B : (3 : Fin 4) ∈ B <;>
    simp_all [Set.mem_union] <;> linarith
  total := by simp only [Set.mem_univ, ite_true]; linarith

-- ═══════════════════════════════════════════════════════════════
-- § 3. Set enumeration and measure value lemmas
-- ═══════════════════════════════════════════════════════════════

private theorem set_fin4_eq (A : Set (Fin 4)) :
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = {2} ∨ A = {3} ∨
    A = {0,1} ∨ A = {0,2} ∨ A = {0,3} ∨ A = {1,2} ∨ A = {1,3} ∨ A = {2,3} ∨
    A = {0,1,2} ∨ A = {0,1,3} ∨ A = {0,2,3} ∨ A = {1,2,3} ∨ A = Set.univ := by
  by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
  by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A
  -- 0123: univ
  · right; right; right; right; right; right; right; right; right; right
    right; right; right; right; right; ext x; fin_cases x <;> simp_all
  -- 012¬3: {0,1,2}
  · right; right; right; right; right; right; right; right; right; right
    right; left; ext x; fin_cases x <;> simp_all
  -- 01¬23: {0,1,3}
  · right; right; right; right; right; right; right; right; right; right
    right; right; left; ext x; fin_cases x <;> simp_all
  -- 01¬2¬3: {0,1}
  · right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  -- 0¬123: {0,2,3}
  · right; right; right; right; right; right; right; right; right; right
    right; right; right; left; ext x; fin_cases x <;> simp_all
  -- 0¬12¬3: {0,2}
  · right; right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  -- 0¬1¬23: {0,3}
  · right; right; right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  -- 0¬1¬2¬3: {0}
  · right; left; ext x; fin_cases x <;> simp_all
  -- ¬0123: {1,2,3}
  · right; right; right; right; right; right; right; right; right; right
    right; right; right; right; left; ext x; fin_cases x <;> simp_all
  -- ¬012¬3: {1,2}
  · right; right; right; right; right; right; right; right; left
    ext x; fin_cases x <;> simp_all
  -- ¬01¬23: {1,3}
  · right; right; right; right; right; right; right; right; right; left
    ext x; fin_cases x <;> simp_all
  -- ¬01¬2¬3: {1}
  · right; right; left; ext x; fin_cases x <;> simp_all
  -- ¬0¬123: {2,3}
  · right; right; right; right; right; right; right; right; right; right; left
    ext x; fin_cases x <;> simp_all
  -- ¬0¬12¬3: {2}
  · right; right; right; left; ext x; fin_cases x <;> simp_all
  -- ¬0¬1¬23: {3}
  · right; right; right; right; left; ext x; fin_cases x <;> simp_all
  -- ¬0¬1¬2¬3: ∅
  · left; ext x; fin_cases x <;> simp_all

-- Measure value lemmas for Fin 4
private theorem measure_fin4_mu (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) (A : Set (Fin 4)) :
    (measure_fin4 a b c ha hb hc habc).mu A =
    (if (0 : Fin 4) ∈ A then a else 0) +
    (if (1 : Fin 4) ∈ A then b else 0) +
    (if (2 : Fin 4) ∈ A then c else 0) +
    (if (3 : Fin 4) ∈ A then 1 - a - b - c else 0) := rfl

private theorem mf4_empty (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ∅ = 0 := by
  rw [measure_fin4_mu]; simp

private theorem mf4_s0 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(0 : Fin 4)} = a := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∈ ({(0 : Fin 4)} : Set _) := rfl
  have h1 : (1 : Fin 4) ∉ ({(0 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h2 : (2 : Fin 4) ∉ ({(0 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h3 : (3 : Fin 4) ∉ ({(0 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  rw [if_pos h0, if_neg h1, if_neg h2, if_neg h3]; linarith

private theorem mf4_s1 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(1 : Fin 4)} = b := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∉ ({(1 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h1 : (1 : Fin 4) ∈ ({(1 : Fin 4)} : Set _) := rfl
  have h2 : (2 : Fin 4) ∉ ({(1 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h3 : (3 : Fin 4) ∉ ({(1 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  rw [if_neg h0, if_pos h1, if_neg h2, if_neg h3]; linarith

private theorem mf4_s2 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(2 : Fin 4)} = c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∉ ({(2 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h1 : (1 : Fin 4) ∉ ({(2 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h2 : (2 : Fin 4) ∈ ({(2 : Fin 4)} : Set _) := rfl
  have h3 : (3 : Fin 4) ∉ ({(2 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  rw [if_neg h0, if_neg h1, if_pos h2, if_neg h3]; linarith

private theorem mf4_s3 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(3 : Fin 4)} = 1 - a - b - c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∉ ({(3 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h1 : (1 : Fin 4) ∉ ({(3 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h2 : (2 : Fin 4) ∉ ({(3 : Fin 4)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h3 : (3 : Fin 4) ∈ ({(3 : Fin 4)} : Set _) := rfl
  rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3]; linarith

private theorem mf4_p01 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 1} : Set (Fin 4)) = a + b := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∈ ({0, 1} : Set (Fin 4)) := by simp
  have h1 : (1 : Fin 4) ∈ ({0, 1} : Set (Fin 4)) := by simp
  have h2 : (2 : Fin 4) ∉ ({0, 1} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h3 : (3 : Fin 4) ∉ ({0, 1} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  rw [if_pos h0, if_pos h1, if_neg h2, if_neg h3]; linarith

private theorem mf4_p02 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 2} : Set (Fin 4)) = a + c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∈ ({0, 2} : Set (Fin 4)) := by simp
  have h1 : (1 : Fin 4) ∉ ({0, 2} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h2 : (2 : Fin 4) ∈ ({0, 2} : Set (Fin 4)) := by simp
  have h3 : (3 : Fin 4) ∉ ({0, 2} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  rw [if_pos h0, if_neg h1, if_pos h2, if_neg h3]; linarith

private theorem mf4_p03 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 3} : Set (Fin 4)) = 1 - b - c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∈ ({0, 3} : Set (Fin 4)) := by simp
  have h1 : (1 : Fin 4) ∉ ({0, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h2 : (2 : Fin 4) ∉ ({0, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h3 : (3 : Fin 4) ∈ ({0, 3} : Set (Fin 4)) := by simp
  rw [if_pos h0, if_neg h1, if_neg h2, if_pos h3]; linarith

private theorem mf4_p12 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({1, 2} : Set (Fin 4)) = b + c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∉ ({1, 2} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h1 : (1 : Fin 4) ∈ ({1, 2} : Set (Fin 4)) := by simp
  have h2 : (2 : Fin 4) ∈ ({1, 2} : Set (Fin 4)) := by simp
  have h3 : (3 : Fin 4) ∉ ({1, 2} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  rw [if_neg h0, if_pos h1, if_pos h2, if_neg h3]; linarith

private theorem mf4_p13 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({1, 3} : Set (Fin 4)) = 1 - a - c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∉ ({1, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h1 : (1 : Fin 4) ∈ ({1, 3} : Set (Fin 4)) := by simp
  have h2 : (2 : Fin 4) ∉ ({1, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h3 : (3 : Fin 4) ∈ ({1, 3} : Set (Fin 4)) := by simp
  rw [if_neg h0, if_pos h1, if_neg h2, if_pos h3]; linarith

private theorem mf4_p23 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({2, 3} : Set (Fin 4)) = 1 - a - b := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∉ ({2, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h1 : (1 : Fin 4) ∉ ({2, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h2 : (2 : Fin 4) ∈ ({2, 3} : Set (Fin 4)) := by simp
  have h3 : (3 : Fin 4) ∈ ({2, 3} : Set (Fin 4)) := by simp
  rw [if_neg h0, if_neg h1, if_pos h2, if_pos h3]; linarith

private theorem mf4_t012 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 2} : Set (Fin 4)) = a + b + c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∈ ({0, 1, 2} : Set (Fin 4)) := by simp
  have h1 : (1 : Fin 4) ∈ ({0, 1, 2} : Set (Fin 4)) := by simp
  have h2 : (2 : Fin 4) ∈ ({0, 1, 2} : Set (Fin 4)) := by simp
  have h3 : (3 : Fin 4) ∉ ({0, 1, 2} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
      (fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                        (fun h' => absurd (Fin.ext_iff.mp h') (by omega)))
  rw [if_pos h0, if_pos h1, if_pos h2, if_neg h3]; linarith

private theorem mf4_t013 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 3} : Set (Fin 4)) = 1 - c := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∈ ({0, 1, 3} : Set (Fin 4)) := by simp
  have h1 : (1 : Fin 4) ∈ ({0, 1, 3} : Set (Fin 4)) := by simp
  have h2 : (2 : Fin 4) ∉ ({0, 1, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
      (fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                        (fun h' => absurd (Fin.ext_iff.mp h') (by omega)))
  have h3 : (3 : Fin 4) ∈ ({0, 1, 3} : Set (Fin 4)) := by simp
  rw [if_pos h0, if_pos h1, if_neg h2, if_pos h3]; linarith

private theorem mf4_t023 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 2, 3} : Set (Fin 4)) = 1 - b := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∈ ({0, 2, 3} : Set (Fin 4)) := by simp
  have h1 : (1 : Fin 4) ∉ ({0, 2, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
      (fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                        (fun h' => absurd (Fin.ext_iff.mp h') (by omega)))
  have h2 : (2 : Fin 4) ∈ ({0, 2, 3} : Set (Fin 4)) := by simp
  have h3 : (3 : Fin 4) ∈ ({0, 2, 3} : Set (Fin 4)) := by simp
  rw [if_pos h0, if_neg h1, if_pos h2, if_pos h3]; linarith

private theorem mf4_t123 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({1, 2, 3} : Set (Fin 4)) = 1 - a := by
  rw [measure_fin4_mu]
  have h0 : (0 : Fin 4) ∉ ({1, 2, 3} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
      (fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                        (fun h' => absurd (Fin.ext_iff.mp h') (by omega)))
  have h1 : (1 : Fin 4) ∈ ({1, 2, 3} : Set (Fin 4)) := by simp
  have h2 : (2 : Fin 4) ∈ ({1, 2, 3} : Set (Fin 4)) := by simp
  have h3 : (3 : Fin 4) ∈ ({1, 2, 3} : Set (Fin 4)) := by simp
  rw [if_neg h0, if_pos h1, if_pos h2, if_pos h3]; linarith

private theorem mf4_univ (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu (Set.univ : Set (Fin 4)) = 1 := by
  rw [measure_fin4_mu]; simp only [Set.mem_univ, ite_true]; linarith

-- ═══════════════════════════════════════════════════════════════
-- § 4. Dispatch helper
-- ═══════════════════════════════════════════════════════════════

set_option maxHeartbeats 1600000 in
/-- Core dispatch: given measure values and ordering biconditionals for all
    disjoint directed pairs, prove representation for ALL disjoint pairs.
    Parallels `fin3_dispatch` from Defs.lean. -/
private theorem fin4_dispatch (sys : EpistemicSystemFA (Fin 4))
    (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c ≤ 1)
    -- non-null hypotheses
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    -- 16 measure-value lemmas
    (hme : (measure_fin4 a b c ha hb hc habc).mu ∅ = 0)
    (hm0 : (measure_fin4 a b c ha hb hc habc).mu {(0 : Fin 4)} = a)
    (hm1 : (measure_fin4 a b c ha hb hc habc).mu {(1 : Fin 4)} = b)
    (hm2 : (measure_fin4 a b c ha hb hc habc).mu {(2 : Fin 4)} = c)
    (hm3 : (measure_fin4 a b c ha hb hc habc).mu {(3 : Fin 4)} = 1 - a - b - c)
    (hm01 : (measure_fin4 a b c ha hb hc habc).mu ({0, 1} : Set (Fin 4)) = a + b)
    (hm02 : (measure_fin4 a b c ha hb hc habc).mu ({0, 2} : Set (Fin 4)) = a + c)
    (hm03 : (measure_fin4 a b c ha hb hc habc).mu ({0, 3} : Set (Fin 4)) = 1 - b - c)
    (hm12 : (measure_fin4 a b c ha hb hc habc).mu ({1, 2} : Set (Fin 4)) = b + c)
    (hm13 : (measure_fin4 a b c ha hb hc habc).mu ({1, 3} : Set (Fin 4)) = 1 - a - c)
    (hm23 : (measure_fin4 a b c ha hb hc habc).mu ({2, 3} : Set (Fin 4)) = 1 - a - b)
    (hm012 : (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 2} : Set (Fin 4)) = a + b + c)
    (hm013 : (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 3} : Set (Fin 4)) = 1 - c)
    (hm023 : (measure_fin4 a b c ha hb hc habc).mu ({0, 2, 3} : Set (Fin 4)) = 1 - b)
    (hm123 : (measure_fin4 a b c ha hb hc habc).mu ({1, 2, 3} : Set (Fin 4)) = 1 - a)
    (hmu : (measure_fin4 a b c ha hb hc habc).mu (Set.univ : Set (Fin 4)) = 1)
    -- ordering biconditionals: ∅ vs singletons (4)
    (he0 : sys.ge ∅ {(0 : Fin 4)} ↔ a ≤ 0)
    (he1 : sys.ge ∅ {(1 : Fin 4)} ↔ b ≤ 0)
    (he2 : sys.ge ∅ {(2 : Fin 4)} ↔ c ≤ 0)
    (he3 : sys.ge ∅ {(3 : Fin 4)} ↔ 1 - a - b - c ≤ 0)
    -- ∅ vs pairs (6)
    (he01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) ↔ a + b ≤ 0)
    (he02 : sys.ge ∅ ({0, 2} : Set (Fin 4)) ↔ a + c ≤ 0)
    (he03 : sys.ge ∅ ({0, 3} : Set (Fin 4)) ↔ 1 - b - c ≤ 0)
    (he12 : sys.ge ∅ ({1, 2} : Set (Fin 4)) ↔ b + c ≤ 0)
    (he13 : sys.ge ∅ ({1, 3} : Set (Fin 4)) ↔ 1 - a - c ≤ 0)
    (he23 : sys.ge ∅ ({2, 3} : Set (Fin 4)) ↔ 1 - a - b ≤ 0)
    -- ∅ vs triples (4)
    (he012 : sys.ge ∅ ({0, 1, 2} : Set (Fin 4)) ↔ a + b + c ≤ 0)
    (he013 : sys.ge ∅ ({0, 1, 3} : Set (Fin 4)) ↔ 1 - c ≤ 0)
    (he023 : sys.ge ∅ ({0, 2, 3} : Set (Fin 4)) ↔ 1 - b ≤ 0)
    (he123 : sys.ge ∅ ({1, 2, 3} : Set (Fin 4)) ↔ 1 - a ≤ 0)
    -- singleton vs singleton (12)
    (h01 : sys.ge {(0 : Fin 4)} {1} ↔ a ≥ b)
    (h10 : sys.ge {(1 : Fin 4)} {0} ↔ b ≥ a)
    (h02 : sys.ge {(0 : Fin 4)} {2} ↔ a ≥ c)
    (h20 : sys.ge {(2 : Fin 4)} {0} ↔ c ≥ a)
    (h03 : sys.ge {(0 : Fin 4)} {3} ↔ a ≥ 1 - a - b - c)
    (h30 : sys.ge {(3 : Fin 4)} {0} ↔ 1 - a - b - c ≥ a)
    (h12 : sys.ge {(1 : Fin 4)} {2} ↔ b ≥ c)
    (h21 : sys.ge {(2 : Fin 4)} {1} ↔ c ≥ b)
    (h13 : sys.ge {(1 : Fin 4)} {3} ↔ b ≥ 1 - a - b - c)
    (h31 : sys.ge {(3 : Fin 4)} {1} ↔ 1 - a - b - c ≥ b)
    (h23 : sys.ge {(2 : Fin 4)} {3} ↔ c ≥ 1 - a - b - c)
    (h32 : sys.ge {(3 : Fin 4)} {2} ↔ 1 - a - b - c ≥ c)
    -- singleton vs pair (24)
    (h0_12 : sys.ge {(0 : Fin 4)} ({1, 2} : Set _) ↔ a ≥ b + c)
    (h0_13 : sys.ge {(0 : Fin 4)} ({1, 3} : Set _) ↔ a ≥ 1 - a - c)
    (h0_23 : sys.ge {(0 : Fin 4)} ({2, 3} : Set _) ↔ a ≥ 1 - a - b)
    (h1_02 : sys.ge {(1 : Fin 4)} ({0, 2} : Set _) ↔ b ≥ a + c)
    (h1_03 : sys.ge {(1 : Fin 4)} ({0, 3} : Set _) ↔ b ≥ 1 - b - c)
    (h1_23 : sys.ge {(1 : Fin 4)} ({2, 3} : Set _) ↔ b ≥ 1 - a - b)
    (h2_01 : sys.ge {(2 : Fin 4)} ({0, 1} : Set _) ↔ c ≥ a + b)
    (h2_03 : sys.ge {(2 : Fin 4)} ({0, 3} : Set _) ↔ c ≥ 1 - b - c)
    (h2_13 : sys.ge {(2 : Fin 4)} ({1, 3} : Set _) ↔ c ≥ 1 - a - c)
    (h3_01 : sys.ge {(3 : Fin 4)} ({0, 1} : Set _) ↔ 1 - a - b - c ≥ a + b)
    (h3_02 : sys.ge {(3 : Fin 4)} ({0, 2} : Set _) ↔ 1 - a - b - c ≥ a + c)
    (h3_12 : sys.ge {(3 : Fin 4)} ({1, 2} : Set _) ↔ 1 - a - b - c ≥ b + c)
    (h12_0 : sys.ge ({1, 2} : Set (Fin 4)) {0} ↔ b + c ≥ a)
    (h13_0 : sys.ge ({1, 3} : Set (Fin 4)) {0} ↔ 1 - a - c ≥ a)
    (h23_0 : sys.ge ({2, 3} : Set (Fin 4)) {0} ↔ 1 - a - b ≥ a)
    (h02_1 : sys.ge ({0, 2} : Set (Fin 4)) {1} ↔ a + c ≥ b)
    (h03_1 : sys.ge ({0, 3} : Set (Fin 4)) {1} ↔ 1 - b - c ≥ b)
    (h23_1 : sys.ge ({2, 3} : Set (Fin 4)) {1} ↔ 1 - a - b ≥ b)
    (h01_2 : sys.ge ({0, 1} : Set (Fin 4)) {2} ↔ a + b ≥ c)
    (h03_2 : sys.ge ({0, 3} : Set (Fin 4)) {2} ↔ 1 - b - c ≥ c)
    (h13_2 : sys.ge ({1, 3} : Set (Fin 4)) {2} ↔ 1 - a - c ≥ c)
    (h01_3 : sys.ge ({0, 1} : Set (Fin 4)) {3} ↔ a + b ≥ 1 - a - b - c)
    (h02_3 : sys.ge ({0, 2} : Set (Fin 4)) {3} ↔ a + c ≥ 1 - a - b - c)
    (h12_3 : sys.ge ({1, 2} : Set (Fin 4)) {3} ↔ b + c ≥ 1 - a - b - c)
    -- singleton vs triple (8)
    (h0_123 : sys.ge {(0 : Fin 4)} ({1, 2, 3} : Set _) ↔ a ≥ 1 - a)
    (h1_023 : sys.ge {(1 : Fin 4)} ({0, 2, 3} : Set _) ↔ b ≥ 1 - b)
    (h2_013 : sys.ge {(2 : Fin 4)} ({0, 1, 3} : Set _) ↔ c ≥ 1 - c)
    (h3_012 : sys.ge {(3 : Fin 4)} ({0, 1, 2} : Set _) ↔ 1 - a - b - c ≥ a + b + c)
    (h123_0 : sys.ge ({1, 2, 3} : Set (Fin 4)) {0} ↔ 1 - a ≥ a)
    (h023_1 : sys.ge ({0, 2, 3} : Set (Fin 4)) {1} ↔ 1 - b ≥ b)
    (h013_2 : sys.ge ({0, 1, 3} : Set (Fin 4)) {2} ↔ 1 - c ≥ c)
    (h012_3 : sys.ge ({0, 1, 2} : Set (Fin 4)) {3} ↔ a + b + c ≥ 1 - a - b - c)
    -- pair vs pair (6)
    (h01_23 : sys.ge ({0, 1} : Set (Fin 4)) ({2, 3} : Set _) ↔ a + b ≥ 1 - a - b)
    (h23_01 : sys.ge ({2, 3} : Set (Fin 4)) ({0, 1} : Set _) ↔ 1 - a - b ≥ a + b)
    (h02_13 : sys.ge ({0, 2} : Set (Fin 4)) ({1, 3} : Set _) ↔ a + c ≥ 1 - a - c)
    (h13_02 : sys.ge ({1, 3} : Set (Fin 4)) ({0, 2} : Set _) ↔ 1 - a - c ≥ a + c)
    (h03_12 : sys.ge ({0, 3} : Set (Fin 4)) ({1, 2} : Set _) ↔ 1 - b - c ≥ b + c)
    (h12_03 : sys.ge ({1, 2} : Set (Fin 4)) ({0, 3} : Set _) ↔ b + c ≥ 1 - b - c) :
    ∀ C D : Set (Fin 4), (∀ x, x ∈ C → x ∉ D) →
      (sys.ge C D ↔ (measure_fin4 a b c ha hb hc habc).inducedGe C D) := by
  intro C D hdisj
  simp only [FinAddMeasure.inducedGe]
  rcases set_fin4_eq C with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases set_fin4_eq D with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- Phase 1: Close non-disjoint cases via exfalso
  -- For each non-disjoint pair, exhibit a shared element i with membership proofs
  all_goals try (exfalso; first
    | exact hdisj 0
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _)
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _)
    | exact hdisj 1
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _)
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _)
    | exact hdisj 2
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _)
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _)
    | exact hdisj 3
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _)
        (by first | rfl | exact Set.mem_insert _ _ | exact Set.mem_insert_of_mem _ rfl
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
                  | exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
                  | exact Set.mem_univ _))
  -- Phase 2: Rewrite measure values on remaining goals
  all_goals simp only [hme, hm0, hm1, hm2, hm3, hm01, hm02, hm03, hm12, hm13, hm23,
    hm012, hm013, hm023, hm123, hmu]
  -- Phase 3: Close remaining goals
  all_goals first
    | exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
    | exact ⟨fun h => absurd h sys.nonTrivial, fun h => by linarith⟩
    | exact ⟨fun _ => by linarith, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
    | exact he0 | exact he1 | exact he2 | exact he3
    | exact he01 | exact he02 | exact he03 | exact he12 | exact he13 | exact he23
    | exact he012 | exact he013 | exact he023 | exact he123
    | exact h01 | exact h10 | exact h02 | exact h20 | exact h03 | exact h30
    | exact h12 | exact h21 | exact h13 | exact h31 | exact h23 | exact h32
    | exact h0_12 | exact h0_13 | exact h0_23 | exact h1_02 | exact h1_03 | exact h1_23
    | exact h2_01 | exact h2_03 | exact h2_13 | exact h3_01 | exact h3_02 | exact h3_12
    | exact h12_0 | exact h13_0 | exact h23_0 | exact h02_1 | exact h03_1 | exact h23_1
    | exact h01_2 | exact h03_2 | exact h13_2 | exact h01_3 | exact h02_3 | exact h12_3
    | exact h0_123 | exact h1_023 | exact h2_013 | exact h3_012
    | exact h123_0 | exact h023_1 | exact h013_2 | exact h012_3
    | exact h01_23 | exact h23_01 | exact h02_13 | exact h13_02 | exact h03_12 | exact h12_03

-- ═══════════════════════════════════════════════════════════════
-- § 5. Permutation infrastructure for Fin 4
-- ═══════════════════════════════════════════════════════════════

/-- Singleton comparison transport through permutation. -/
private theorem perm_ge_singleton (σ : Fin 4 ≃ Fin 4)
    (sys : EpistemicSystemFA (Fin 4)) (i j : Fin 4) :
    (transportFA σ sys).ge {i} {j} ↔ sys.ge {σ.symm i} {σ.symm j} := by
  show sys.ge (σ.symm '' {i}) (σ.symm '' {j}) ↔ sys.ge {σ.symm i} {σ.symm j}
  simp only [Set.image_singleton]

-- ═══════════════════════════════════════════════════════════════
-- § 6. Main theorem
-- ═══════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════
-- § 6a. Derivation helpers for the case tree
-- ═══════════════════════════════════════════════════════════════

-- Derive ¬ge ∅ {i,j} from ¬ge ∅ {i}
private theorem nge_empty_pair_of_nge_singleton (sys : EpistemicSystemFA (Fin 4))
    {i j : Fin 4} (hni : ¬sys.ge ∅ {i})
    (hij : i ∈ ({i, j} : Set (Fin 4))) :
    ¬sys.ge ∅ ({i, j} : Set (Fin 4)) :=
  fun h => hni (sys.trans _ _ _ h (sys.mono _ _ (Set.singleton_subset_iff.mpr hij)))

-- Derive ge {i,j} {k} from {i} ⊆ {i,j} and ge {i} {k}
private theorem ge_pair_singleton_of_ge (sys : EpistemicSystemFA (Fin 4))
    {i j k : Fin 4} (hi : i ∈ ({i, j} : Set (Fin 4))) (hik : sys.ge {i} {k}) :
    sys.ge ({i, j} : Set (Fin 4)) {k} :=
  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr hi)) hik

-- Derive ¬ge {i} {j,k} from: ge {j} {i} → ge {i} {j,k} → ge {i} {i,k} → ge ∅ {k} → contradiction
-- Pattern: ge {i} {j,k} + ge {j,k} {i,k} (add ↔ ge {j} {i}) → ge {i} {i,k} (add ↔ ge ∅ {k}) → hn_k
private theorem nge_singleton_pair (sys : EpistemicSystemFA (Fin 4))
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hge_ji : sys.ge {j} {i}) (hnk : ¬sys.ge ∅ {k})
    (hdiff1a : ({j, k} : Set (Fin 4)) \ {i, k} = {j})
    (hdiff1b : ({i, k} : Set (Fin 4)) \ {j, k} = {i})
    (hdiff2a : ({i} : Set (Fin 4)) \ {i, k} = ∅)
    (hdiff2b : ({i, k} : Set (Fin 4)) \ {i} = {k}) :
    ¬sys.ge {i} ({j, k} : Set (Fin 4)) := fun h => by
  have hge_jk_ik : sys.ge ({j, k} : Set (Fin 4)) ({i, k} : Set _) := by
    rw [sys.additive ({j, k} : Set (Fin 4)) {i, k}, hdiff1a, hdiff1b]; exact hge_ji
  have h1 := sys.trans _ _ _ h hge_jk_ik
  rw [sys.additive {i} {i, k}, hdiff2a, hdiff2b] at h1
  exact hnk h1

-- ═══════════════════════════════════════════════════════════════
-- § 6b. Leaf proof helper — provides witness and calls dispatch
-- ═══════════════════════════════════════════════════════════════

/-- Provide a measure witness and verify all biconditionals via fin4_dispatch. -/
private noncomputable def fin4_witness (sys : EpistemicSystemFA (Fin 4))
    (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c ≤ 1)
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (biconditionals :
      ∀ C D : Set (Fin 4), (∀ x, x ∈ C → x ∉ D) →
        (sys.ge C D ↔ (measure_fin4 a b c ha hb hc habc).inducedGe C D)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  ⟨measure_fin4 a b c ha hb hc habc,
   reduce_to_disjoint sys _ biconditionals⟩

-- ═══════════════════════════════════════════════════════════════
-- § 6c. All-non-null case tree
-- ═══════════════════════════════════════════════════════════════

-- The canonical case: ge{0}{1}, ge{1}{2}, ge{2}{3} (sorted order)
-- with 8 partition sub-cases determined by tie/strict at each boundary
set_option maxHeartbeats 6400000 in
private theorem fin4_sorted_case (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3}) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  -- Case-split on tie/strict at each boundary
  by_cases h10 : sys.ge {(1 : Fin 4)} {0}
  · by_cases h21 : sys.ge {(2 : Fin 4)} {1}
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · -- Case (4): 0~1~2~3, all tied. a=b=c=d=1/4
        have h20 := sys.trans _ _ _ h21 h10
        have h31 := sys.trans _ _ _ h32 h21
        have h30 := sys.trans _ _ _ h31 h10
        sorry
      · -- Case (3,1): 0~1~2>3
        have h20 := sys.trans _ _ _ h21 h10
        sorry
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · -- Case (2,2): 0~1>2~3
        sorry
      · -- Case (2,1,1): 0~1>2>3
        sorry
  · by_cases h21 : sys.ge {(2 : Fin 4)} {1}
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · -- Case (1,3): 0>1~2~3
        sorry
      · -- Case (1,2,1): 0>1~2>3
        sorry
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · -- Case (1,1,2): 0>1>2~3
        sorry
      · -- Case (1,1,1,1): 0>1>2>3, all strict
        sorry

-- Helper: build a specific Fin 4 permutation from a function specification
private def mkPerm4 (f : Fin 4 → Fin 4) (g : Fin 4 → Fin 4)
    (hfg : ∀ i, g (f i) = i) (hgf : ∀ i, f (g i) = i) : Fin 4 ≃ Fin 4 where
  toFun := f
  invFun := g
  left_inv := hfg
  right_inv := hgf

-- Sorting network: find a permutation σ such that the transported system
-- has ge'{0}{1} ∧ ge'{1}{2} ∧ ge'{2}{3}
-- Then apply perm_repr + fin4_sorted_case
set_option maxHeartbeats 6400000 in
private theorem theorem8a_fin4_allnonnull (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)}) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  -- Non-recursive sorting: case-split on pairwise orderings to find canonical order
  -- then apply the right permutation and call fin4_sorted_case
  rcases sys.total {(0 : Fin 4)} {1} with h01 | h10
  · rcases sys.total {(1 : Fin 4)} {2} with h12 | h21
    · rcases sys.total {(2 : Fin 4)} {3} with h23 | h32
      · -- 0≥1≥2≥3: canonical, identity permutation
        exact fin4_sorted_case sys hn0 hn1 hn2 hn3 h01 h12 h23
      · -- 0≥1≥2, 3≥2: where does 3 fit?
        rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
        · -- 0≥1≥3≥2: swap 2↔3
          exact perm_repr (Equiv.swap 2 3) sys
            (fin4_sorted_case _ (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h01)
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h13)
              (by rw [perm_ge_singleton]; simp; exact h32))
        · -- 3≥1, 0≥1, 3≥2: where does 3 fit relative to 0?
          rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · -- 0≥3≥1≥2: perm (0,3,1,2) → σ.symm = [0,3,1,2], σ = [0,2,3,1]
            sorry
          · -- 3≥0≥1≥2: σ⁻¹ = [3,0,1,2], σ = [1,2,3,0]
            exact perm_repr
              (⟨fun | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0,
                fun | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h30)
                (by rw [perm_ge_singleton]; exact h01)
                (by rw [perm_ge_singleton]; exact h12))
    · rcases sys.total {(2 : Fin 4)} {3} with h23 | h32
      · -- 0≥1, 2≥1, 2≥3: where does 0 vs 2?
        rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
        · -- 0≥2≥1, 2≥3: where does 3 fit?
          rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
          · -- 0≥2≥1≥3: swap 1↔2
            exact perm_repr (Equiv.swap 1 2) sys
              (fin4_sorted_case _ (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h02)
                (by rw [perm_ge_singleton]; simp; exact h21)
                (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h13)
                )
          · -- 0≥2≥3≥1: perm σ.symm = [0,2,3,1]
            sorry
        · -- 2≥0≥1, 2≥3: where does 3 fit?
          rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · -- 2≥0≥1, 0≥3: where does 3 vs 1?
            rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
            · -- 2≥0≥1≥3: swap 0↔2
              sorry
            · -- 2≥0≥3≥1: perm σ.symm = [2,0,3,1]
              sorry
          · -- 2≥0≥1, 3≥0: also 2≥3 (given), so 2≥3≥0≥1
            have h31 : sys.ge {(3 : Fin 4)} {1} := sys.trans _ _ _ h30 h01
            sorry
      · -- 0≥1, 2≥1, 3≥2: trans 3≥2≥1, also 0≥1
        have h31 : sys.ge {(3 : Fin 4)} {1} := sys.trans _ _ _ h32 h21
        rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
        · rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
          · -- 0≥3, 0≥2: need to order 2 and 3
            -- 0≥{2,3}, 3≥2≥1. Where does 0 fit? 0≥3≥2≥1 or 0≥2 and 3≥2...
            -- We have h03 (0≥3) and h32 (3≥2), so 0≥3≥2≥1
            sorry
          · -- h20 (2≥0), h03 (0≥3): 2≥0≥3, 3≥2? No, h32 (3≥2). So 3≥2≥0 and 0≥3?
            -- Trans: 0≥3≥2≥0, circular, so 0~2~3, also 0≥1. Order: 0~2~3≥1
            sorry
        · -- h30 (3≥0), 3≥2≥1, 0≥1
          rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
          · -- 3≥0≥2≥1: perm σ.symm = [3,0,2,1]
            sorry
          · -- 3≥0, 2≥0, 3≥2≥1, 0≥1: 3≥2≥0≥1 (since 2≥0)
            sorry
  · -- ge {1} {0}
    rcases sys.total {(1 : Fin 4)} {2} with h12 | h21
    · -- 1≥0, 1≥2
      rcases sys.total {(2 : Fin 4)} {3} with h23 | h32
      · -- 1≥0, 1≥2≥3: where does 0 fit?
        rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
        · -- 1≥0≥2≥3: swap 0↔1
          exact perm_repr (Equiv.swap 0 1) sys
            (fin4_sorted_case _ (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rw [perm_ge_singleton]; simp; exact h10)
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h02)
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h23))
        · -- 1≥2≥0: where does 0 fit relative to 3?
          rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · -- 1≥2≥0≥3: perm σ.symm = [1,2,0,3]
            sorry
          · -- 1≥2≥3≥0: perm σ.symm = [1,2,3,0]
            sorry
      · -- 1≥0, 1≥2, 3≥2: where does 3 fit?
        rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
        · -- 1≥3≥2, 1≥0: order 0 vs 3?
          rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · -- 1≥0≥3≥2 or 1≥3≥0≥2? We have 1≥0 and 1≥3, 0≥3.
            -- 1≥0≥3≥2: perm swap(0,1) then swap(2,3)
            sorry
          · -- 1≥3≥0, 3≥2: where does 0 vs 2?
            rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
            · -- 1≥3≥0≥2
              sorry
            · -- 1≥3≥2≥0
              sorry
        · -- 3≥1≥0, 3≥2: order 1 vs 2, 0 vs 2
          rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
          · -- 3≥1≥0, 0≥2: 3≥1≥0≥2
            sorry
          · -- 3≥1≥0, 2≥0, 3≥2, 1≥2? We have h12. So 3≥1≥2≥0
            sorry
    · -- 1≥0, 2≥1: trans 2≥1≥0
      have h20 : sys.ge {(2 : Fin 4)} {0} := sys.trans _ _ _ h21 h10
      rcases sys.total {(2 : Fin 4)} {3} with h23 | h32
      · -- 2≥1≥0, 2≥3: where does 3 fit?
        rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
        · -- 2≥1≥0≥3: swap 0↔2
          sorry
        · -- 2≥1, 3≥0, 2≥3: where does 3 vs 1?
          rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
          · -- 2≥1≥3≥0
            sorry
          · -- 2≥3, 3≥1≥0: 2≥3≥1≥0
            sorry
      · -- 2≥1≥0, 3≥2: trans 3≥2≥1≥0, reversed order
        have h30 : sys.ge {(3 : Fin 4)} {0} := sys.trans _ _ _ h32 h20
        have h31 : sys.ge {(3 : Fin 4)} {1} := sys.trans _ _ _ h32 h21
        -- 3≥2≥1≥0: reverse permutation
        sorry

-- ═══════════════════════════════════════════════════════════════
-- § 7. Main theorem
-- ═══════════════════════════════════════════════════════════════

/-- Not all 4 singletons can be null. -/
private theorem not_all_null (sys : EpistemicSystemFA (Fin 4)) :
    ¬(sys.ge ∅ {0} ∧ sys.ge ∅ {1} ∧ sys.ge ∅ {2} ∧ sys.ge ∅ {3}) := by
  intro ⟨h0, h1, h2, h3⟩
  have h01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) := by
    have : sys.ge {1} ({0, 1} : Set (Fin 4)) := by
      rw [sys.additive {1} {0, 1}]
      rw [show ({1} : Set (Fin 4)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1} : Set (Fin 4)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
      exact h0
    exact sys.trans _ _ _ h1 this
  have h012 : sys.ge ∅ ({0, 1, 2} : Set (Fin 4)) := by
    have : sys.ge {2} ({0, 1, 2} : Set (Fin 4)) := by
      rw [sys.additive {2} {0, 1, 2}]
      rw [show ({2} : Set (Fin 4)) \ {0, 1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1, 2} : Set (Fin 4)) \ {2} = {0, 1} from by ext x; fin_cases x <;> simp_all]
      exact h01
    exact sys.trans _ _ _ h2 this
  have huniv : sys.ge ∅ Set.univ := by
    have : sys.ge {3} (Set.univ : Set (Fin 4)) := by
      rw [sys.additive {3} Set.univ]
      rw [show ({3} : Set (Fin 4)) \ Set.univ = ∅ from by ext x; simp]
      rw [show (Set.univ : Set (Fin 4)) \ {3} = {0, 1, 2} from by ext x; fin_cases x <;> simp_all]
      exact h012
    exact sys.trans _ _ _ h3 this
  exact sys.nonTrivial huniv

/-- **Theorem 8a for Fin 4**: every FA system on 4 elements is representable. -/
theorem theorem8a_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  -- Case 1: Some singleton is null → reduce to Fin 3 via null_elem_reduce
  by_cases hn0 : sys.ge ∅ {(0 : Fin 4)}
  · -- 0 is null; need a non-null witness
    by_cases hn1 : sys.ge ∅ {(1 : Fin 4)}
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 4)}
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · exact absurd ⟨hn0, hn1, hn2, hn3⟩ (not_all_null sys)
        · exact fin4_null0'' sys hn0 hn1 hn2 hn3
      · exact fin4_null0' sys hn0 hn1 hn2
    · exact fin4_null0 sys hn0 hn1
  · by_cases hn1 : sys.ge ∅ {(1 : Fin 4)}
    · -- 1 is null, 0 is not. Swap 0↔1, reduce.
      exact perm_repr (Equiv.swap 0 1) sys
        (fin4_null0 (transportFA (Equiv.swap 0 1) sys)
          (by rwa [perm_null_iff])
          (by rwa [perm_null_iff]))
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 4)}
      · -- 2 is null, 0,1 are not. Swap 0↔2, reduce.
        exact perm_repr (Equiv.swap 0 2) sys
          (fin4_null0 (transportFA (Equiv.swap 0 2) sys)
            (by rwa [perm_null_iff])
            (by rwa [perm_null_iff]))
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 3 is null, 0,1,2 are not. Swap 0↔3, reduce.
          exact perm_repr (Equiv.swap 0 3) sys
            (fin4_null0 (transportFA (Equiv.swap 0 3) sys)
              (by rwa [perm_null_iff])
              (by rwa [perm_null_iff]))
        · -- Case 2: All singletons non-null.
          exact theorem8a_fin4_allnonnull sys hn0 hn1 hn2 hn3

end Core.Scale
