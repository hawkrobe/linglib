import Linglib.Core.Scales.EpistemicScale.Cancellation

/-!
# Chamber proofs for Fin 4 cancellation

Auto-generated: 88 chamber proofs for the sorted Fin 4 cancellation theorem.
Each chamber is a fully-determined FA ordering consistent with 0 ≥ 1 ≥ 2 ≥ 3,
proved via `cancellation_from_weights` with rational witness weights.
-/

namespace Core.Scale

attribute [local instance] Classical.propDecidable

private lemma ge_empty_contra (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ (i : Fin 4), ¬sys.ge ∅ {i})
    {B : Set (Fin 4)} (hne : B.Nonempty) (h : sys.ge ∅ B) : False := by
  obtain ⟨x, hx⟩ := hne
  exact hpos x (sys.trans _ _ _ h (sys.mono _ _ (Set.singleton_subset_iff.mpr hx)))

-- Precomputed set-difference equalities for Fin 4
private lemma sd_0_0 : ({(0 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0_01 : ({(0 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0_02 : ({(0 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0_03 : ({(0 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0_012 : ({(0 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0_013 : ({(0 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0_023 : ({(0 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0_0123 : ({(0 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_1 : ({(1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_01 : ({(1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_12 : ({(1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_13 : ({(1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_012 : ({(1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_013 : ({(1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_123 : ({(1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_1_0123 : ({(1 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_2 : ({(2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_02 : ({(2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_12 : ({(2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_23 : ({(2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_012 : ({(2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_023 : ({(2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_123 : ({(2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_2_0123 : ({(2 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_3 : ({(3 : Fin 4)} : Set (Fin 4)) \ {(3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_03 : ({(3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_13 : ({(3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_23 : ({(3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_013 : ({(3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_023 : ({(3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_123 : ({(3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_3_0123 : ({(3 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_0 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_1 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_01 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_02 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_03 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_12 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_13 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_012 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_013 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_023 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_123 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_01_0123 : ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_0 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_2 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_01 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_02 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_03 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_12 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_23 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_012 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_013 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_023 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_123 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_02_0123 : ({(0 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_0 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_3 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_01 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_02 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_03 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_13 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_23 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_012 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_013 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_023 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_123 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_03_0123 : ({(0 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_1 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_2 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_01 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_02 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_12 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_13 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_23 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_012 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_013 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_023 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_123 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_12_0123 : ({(1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_1 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_3 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_01 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_03 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_12 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_13 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_23 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_012 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_013 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_023 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_123 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_13_0123 : ({(1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_2 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_3 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_02 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_03 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_12 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_13 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_23 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_012 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_013 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_023 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_123 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_23_0123 : ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_0 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4)} = {(1 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_1 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4)} = {(0 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_2 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4)} = {(0 : Fin 4), (1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_01 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_02 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_03 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_12 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_13 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_23 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4), (1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_012 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_013 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_023 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_123 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_012_0123 : ({(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_0 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4)} = {(1 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_1 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4)} = {(0 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_3 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(3 : Fin 4)} = {(0 : Fin 4), (1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_01 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_02 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(1 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_03 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_12 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(0 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_13 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_23 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4), (1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_012 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_013 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_023 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_123 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_013_0123 : ({(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_0 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4)} = {(2 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_2 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4)} = {(0 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_3 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(3 : Fin 4)} = {(0 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_01 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(2 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_02 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_03 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_12 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(0 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_13 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_23 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_012 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_013 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_023 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_123 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_023_0123 : ({(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_1 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4)} = {(2 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_2 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4)} = {(1 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_3 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(3 : Fin 4)} = {(1 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_01 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(2 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_02 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(1 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_03 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_12 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_13 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_23 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_012 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_013 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_023 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_123 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_123_0123 : ({(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_0 : (Set.univ : Set (Fin 4)) \ {(0 : Fin 4)} = {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_1 : (Set.univ : Set (Fin 4)) \ {(1 : Fin 4)} = {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_2 : (Set.univ : Set (Fin 4)) \ {(2 : Fin 4)} = {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_3 : (Set.univ : Set (Fin 4)) \ {(3 : Fin 4)} = {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_01 : (Set.univ : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4)} = {(2 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_02 : (Set.univ : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4)} = {(1 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_03 : (Set.univ : Set (Fin 4)) \ {(0 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_12 : (Set.univ : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4)} = {(0 : Fin 4), (3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_13 : (Set.univ : Set (Fin 4)) \ {(1 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4), (2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_23 : (Set.univ : Set (Fin 4)) \ {(2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4), (1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_012 : (Set.univ : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} = {(3 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_013 : (Set.univ : Set (Fin 4)) \ {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} = {(2 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_023 : (Set.univ : Set (Fin 4)) \ {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(1 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_123 : (Set.univ : Set (Fin 4)) \ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} = {(0 : Fin 4)} := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
private lemma sd_0123_0123 : (Set.univ : Set (Fin 4)) \ (Set.univ : Set (Fin 4)) = (∅ : Set (Fin 4)) := by ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]

set_option maxHeartbeats 800000 in
private theorem chamber_0 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/15, (4 : ℚ)/15, (2 : ℚ)/15, (1 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_1 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/11, (3 : ℚ)/11, (1 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_2 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(10 : ℚ)/19, (4 : ℚ)/19, (3 : ℚ)/19, (2 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_3 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/11, (2 : ℚ)/11, (2 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_4 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/15, (3 : ℚ)/15, (2 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_5 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have heqr_3_1 : sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ h32 h21)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h13 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_1_12, sd_12_1] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/7, (1 : ℚ)/7, (1 : ℚ)/7, (1 : ℚ)/7])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_6 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/13, (3 : ℚ)/13, (2 : ℚ)/13, (1 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_7 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf6rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf6r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf6r (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/9, (2 : ℚ)/9, (1 : ℚ)/9, (1 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_8 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf4rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf4r
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(10 : ℚ)/21, (6 : ℚ)/21, (3 : ℚ)/21, (2 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_9 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/17, (5 : ℚ)/17, (2 : ℚ)/17, (2 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_10 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/14, (4 : ℚ)/14, (2 : ℚ)/14, (1 : ℚ)/14])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_11 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/10, (3 : ℚ)/10, (1 : ℚ)/10, (1 : ℚ)/10])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_12 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(10 : ℚ)/23, (7 : ℚ)/23, (4 : ℚ)/23, (2 : ℚ)/23])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_13 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h hf4r)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf4
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_13_12, sd_12_13] at h2
        exact h32 h2
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/13, (4 : ℚ)/13, (2 : ℚ)/13, (1 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_14 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/19, (6 : ℚ)/19, (4 : ℚ)/19, (1 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_15 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/16, (5 : ℚ)/16, (3 : ℚ)/16, (1 : ℚ)/16])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_16 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(10 : ℚ)/25, (8 : ℚ)/25, (4 : ℚ)/25, (3 : ℚ)/25])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_17 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_13_03, sd_03_13] at h2
        exact h10 h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_12_02, sd_02_12] at h2
        exact h10 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/15, (5 : ℚ)/15, (2 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_18 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/19, (6 : ℚ)/19, (3 : ℚ)/19, (2 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_19 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have heqr_12_0 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) hf3r)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) hf3r))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/9, (3 : ℚ)/9, (1 : ℚ)/9, (1 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_20 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/21, (7 : ℚ)/21, (4 : ℚ)/21, (2 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_21 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h01 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h01 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ (sys.mono {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h32t h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_1 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h h10)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/11, (4 : ℚ)/11, (2 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_22 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/18, (6 : ℚ)/18, (3 : ℚ)/18, (2 : ℚ)/18])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_23 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have heqr_13_02 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have heqr_12_03 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)))
  have heqr_02_13 : sys.ge {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_02_12, sd_12_02]; exact h01)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h01 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ (sys.mono {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h23 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_1 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h h10)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(3 : ℚ)/8, (3 : ℚ)/8, (1 : ℚ)/8, (1 : ℚ)/8])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_24 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/15, (5 : ℚ)/15, (3 : ℚ)/15, (1 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_25 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf5rt : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf5r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/12, (4 : ℚ)/12, (2 : ℚ)/12, (1 : ℚ)/12])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_26 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf4rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf4r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/17, (4 : ℚ)/17, (3 : ℚ)/17, (2 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_27 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf4rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf4r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/15, (3 : ℚ)/15, (3 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_28 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/13, (3 : ℚ)/13, (2 : ℚ)/13, (2 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_29 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have heqr_3_1 : sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ h32 h21)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32))) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h13 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_1_12, sd_12_1] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/11, (2 : ℚ)/11, (2 : ℚ)/11, (2 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_30 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf4rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf4r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf4r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(9 : ℚ)/19, (5 : ℚ)/19, (3 : ℚ)/19, (2 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_31 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h)
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/15, (4 : ℚ)/15, (2 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_32 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(9 : ℚ)/18, (4 : ℚ)/18, (3 : ℚ)/18, (2 : ℚ)/18])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_33 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/10, (2 : ℚ)/10, (2 : ℚ)/10, (1 : ℚ)/10])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_34 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/14, (3 : ℚ)/14, (2 : ℚ)/14, (2 : ℚ)/14])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_35 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have heqr_3_1 : sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ h32 h21)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h13 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_1_12, sd_12_1] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(3 : ℚ)/6, (1 : ℚ)/6, (1 : ℚ)/6, (1 : ℚ)/6])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_36 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h32t)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/12, (3 : ℚ)/12, (2 : ℚ)/12, (1 : ℚ)/12])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_37 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_0 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf6
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_12_123, sd_123_12] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_1 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_12_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/8, (2 : ℚ)/8, (1 : ℚ)/8, (1 : ℚ)/8])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_38 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h21t)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/19, (5 : ℚ)/19, (4 : ℚ)/19, (2 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_39 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/17, (4 : ℚ)/17, (4 : ℚ)/17, (2 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_40 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h hf4r)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf4
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_13_12, sd_12_13] at h2
        exact h32 h2
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h21t)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/16, (4 : ℚ)/16, (3 : ℚ)/16, (2 : ℚ)/16])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_41 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h hf4r)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf4
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_13_12, sd_12_13] at h2
        exact h32 h2
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/9, (2 : ℚ)/9, (2 : ℚ)/9, (1 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_42 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(9 : ℚ)/21, (6 : ℚ)/21, (4 : ℚ)/21, (2 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_43 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h hf4r)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf4
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_13_12, sd_12_13] at h2
        exact h32 h2
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/11, (3 : ℚ)/11, (2 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_44 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h21t)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(10 : ℚ)/25, (7 : ℚ)/25, (6 : ℚ)/25, (2 : ℚ)/25])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_45 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/15, (4 : ℚ)/15, (4 : ℚ)/15, (1 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_46 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h21t)) h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(9 : ℚ)/22, (6 : ℚ)/22, (5 : ℚ)/22, (2 : ℚ)/22])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_47 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h12 h
        have h2 := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_1_13, sd_13_1] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_0 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) h)
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_13_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/12, (3 : ℚ)/12, (3 : ℚ)/12, (1 : ℚ)/12])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_48 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/17, (5 : ℚ)/17, (4 : ℚ)/17, (1 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_49 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf3rt : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf3r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf3r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/14, (4 : ℚ)/14, (3 : ℚ)/14, (1 : ℚ)/14])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_50 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/21, (6 : ℚ)/21, (4 : ℚ)/21, (3 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_51 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_13_03, sd_03_13] at h2
        exact h10 h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_12_02, sd_02_12] at h2
        exact h10 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/18, (5 : ℚ)/18, (3 : ℚ)/18, (3 : ℚ)/18])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_52 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf3
        have h2 := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_23_13, sd_13_23] at h2
        exact h21 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/15, (4 : ℚ)/15, (3 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_53 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_12_0 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) hf3r)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) hf3r))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf4
        have h2 := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_23_12, sd_12_23] at h2
        exact hng_3_1 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/12, (3 : ℚ)/12, (2 : ℚ)/12, (2 : ℚ)/12])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_54 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(9 : ℚ)/23, (7 : ℚ)/23, (4 : ℚ)/23, (3 : ℚ)/23])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_55 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_13_03, sd_03_13] at h2
        exact h10 h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_12_02, sd_02_12] at h2
        exact h10 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/13, (4 : ℚ)/13, (2 : ℚ)/13, (2 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_56 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/17, (5 : ℚ)/17, (3 : ℚ)/17, (2 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_57 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_12_0 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) hf3r)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) hf3r))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(3 : ℚ)/7, (2 : ℚ)/7, (1 : ℚ)/7, (1 : ℚ)/7])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_58 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(10 : ℚ)/27, (8 : ℚ)/27, (6 : ℚ)/27, (3 : ℚ)/27])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_59 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf2rt : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf2r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hf2r (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(9 : ℚ)/24, (7 : ℚ)/24, (5 : ℚ)/24, (3 : ℚ)/24])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_60 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf3
        have h2 := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_23_13, sd_13_23] at h2
        exact h21 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/21, (6 : ℚ)/21, (5 : ℚ)/21, (2 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_61 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h hf3
        have h2 := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_23_13, sd_13_23] at h2
        exact h21 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/18, (5 : ℚ)/18, (4 : ℚ)/18, (2 : ℚ)/18])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_62 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/19, (6 : ℚ)/19, (4 : ℚ)/19, (2 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_63 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/16, (5 : ℚ)/16, (3 : ℚ)/16, (2 : ℚ)/16])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_64 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/13, (4 : ℚ)/13, (3 : ℚ)/13, (1 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_65 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h hf3r)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_0 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ hf5 h)
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_23_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/10, (3 : ℚ)/10, (2 : ℚ)/10, (1 : ℚ)/10])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_66 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)) h
        have h2 := (sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_02_01, sd_01_02] at h2
        exact h21 h2
  exact cancellation_from_weights_fin4 sys (![(8 : ℚ)/23, (6 : ℚ)/23, (5 : ℚ)/23, (4 : ℚ)/23])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_67 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_23, sd_23_03]; exact h02)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_03_01, sd_01_03] at h2
        exact hng_3_1 h2
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/17, (4 : ℚ)/17, (4 : ℚ)/17, (3 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_68 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_13_03, sd_03_13] at h2
        exact h10 h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_12_02, sd_02_12] at h2
        exact h10 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)) h
        have h2 := (sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_02_01, sd_01_02] at h2
        exact h21 h2
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/15, (4 : ℚ)/15, (3 : ℚ)/15, (3 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_69 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_3_1 : sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ h32 h21)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_13_03, sd_03_13] at h2
        exact h10 h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_12_02, sd_02_12] at h2
        exact h10 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) h
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_12_01, sd_01_12] at h2
        exact hng_2_0 h2
  exact cancellation_from_weights_fin4 sys (![(3 : ℚ)/9, (2 : ℚ)/9, (2 : ℚ)/9, (2 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_70 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/19, (5 : ℚ)/19, (4 : ℚ)/19, (3 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_71 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) h
        have h2 := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_13_03, sd_03_13] at h2
        exact h10 h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) h
        have h2 := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_12_02, sd_02_12] at h2
        exact h10 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/11, (3 : ℚ)/11, (2 : ℚ)/11, (2 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_72 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hf1rt : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} := (sys.total _ _).resolve_left hf1r
  have heqr_13_0 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf1r (sys.trans _ _ _ (sys.mono {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) h)
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/13, (3 : ℚ)/13, (3 : ℚ)/13, (2 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_73 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_12_0 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) hf2r)
  have heqr_13_0 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r)
  have heqr_3_1 : sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ h32 h21)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_12_03 : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf4 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_23, sd_23_12]; exact h13)) hf2r))
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(2 : ℚ)/5, (1 : ℚ)/5, (1 : ℚ)/5, (1 : ℚ)/5])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_74 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)) h
        have h2 := (sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_02_01, sd_01_02] at h2
        exact h21 h2
  exact cancellation_from_weights_fin4 sys (![(7 : ℚ)/21, (6 : ℚ)/21, (5 : ℚ)/21, (3 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_75 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf5 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf5 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_23, sd_23_03]; exact h02)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h h01)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h32t h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)) h
        have h2 := (sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_02_01, sd_01_02] at h2
        exact h21 h2
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/13, (4 : ℚ)/13, (3 : ℚ)/13, (2 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_76 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_23, sd_23_03]; exact h02)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_03_01, sd_01_03] at h2
        exact hng_3_1 h2
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/15, (4 : ℚ)/15, (4 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_77 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_2_0 : sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ h21 h10)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf5 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hf5 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_23, sd_23_03]; exact h02)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h02 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h02)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h h10)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_23, sd_23_03]; exact h02)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_03_01, sd_01_03] at h2
        exact hng_3_1 h2
  exact cancellation_from_weights_fin4 sys (![(2 : ℚ)/7, (2 : ℚ)/7, (2 : ℚ)/7, (1 : ℚ)/7])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_78 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)) h
        have h2 := (sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_02_01, sd_01_02] at h2
        exact h21 h2
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/18, (5 : ℚ)/18, (4 : ℚ)/18, (3 : ℚ)/18])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_79 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_23, sd_23_03]; exact h02)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_03_01, sd_01_03] at h2
        exact hng_3_1 h2
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/12, (3 : ℚ)/12, (3 : ℚ)/12, (2 : ℚ)/12])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_80 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_13_02 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have heqr_12_03 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)))
  have heqr_02_13 : sys.ge {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_02_12, sd_12_02]; exact h01)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf5 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h h01)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h23 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)) h
        have h2 := (sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_02_01, sd_01_02] at h2
        exact h21 h2
  exact cancellation_from_weights_fin4 sys (![(3 : ℚ)/10, (3 : ℚ)/10, (2 : ℚ)/10, (2 : ℚ)/10])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_81 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have hf2t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf2
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_2_0 : sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ h21 h10)
  have heqr_3_0 : sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ h32 (sys.trans _ _ _ h21 h10))
  have heqr_3_1 : sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ h32 h21)
  have heqr_23_01 : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10))) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_02_01, sd_01_02]; exact h21))))
  have heqr_13_02 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have heqr_12_03 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)))
  have heqr_02_13 : sys.ge {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_02_12, sd_12_02]; exact h01)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
  have heqr_01_23 : sys.ge {(0 : Fin 4), (1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)))
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hf5 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_23, sd_23_02]; exact h03)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h02 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_01 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  exact cancellation_from_weights_fin4 sys (![(1 : ℚ)/4, (1 : ℚ)/4, (1 : ℚ)/4, (1 : ℚ)/4])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_82 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(6 : ℚ)/17, (5 : ℚ)/17, (4 : ℚ)/17, (2 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_83 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h21t h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h10t)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(5 : ℚ)/14, (4 : ℚ)/14, (3 : ℚ)/14, (2 : ℚ)/14])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_84 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_13_0 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(4 : ℚ)/11, (3 : ℚ)/11, (3 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_85 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h10t : sys.ge {(0 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left h10
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf5t : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} := (sys.total _ _).resolve_left hf5
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_13_0 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h12 h)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h12 h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) hf2r))
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h10 (sys.trans _ _ _ h13 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h32 (sys.trans _ _ _ h h12)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf3 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(3 : ℚ)/8, (2 : ℚ)/8, (2 : ℚ)/8, (1 : ℚ)/8])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_86 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have h32t : sys.ge {(2 : Fin 4)} {(3 : Fin 4)} := (sys.total _ _).resolve_left h32
  have hf1t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} := (sys.total _ _).resolve_left hf1
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_23_1 : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ hf2r h01)
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h01 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h01 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp h1
        rw [sd_0_03, sd_03_0] at h2
        exact (hpos ⟨3, by omega⟩) h2
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h h01)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h32t h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h32t h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h32t h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_13_02 : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) h
        have h2 := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_03_02, sd_02_03] at h2
        exact h32 h2
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(3 : ℚ)/9, (3 : ℚ)/9, (2 : ℚ)/9, (1 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 800000 in
private theorem chamber_87 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  have h02 := sys.trans _ _ _ h01 h12
  have h03 := sys.trans _ _ _ h02 h23
  have h13 := sys.trans _ _ _ h12 h23
  have h21t : sys.ge {(1 : Fin 4)} {(2 : Fin 4)} := (sys.total _ _).resolve_left h21
  have hf3t : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf3
  have hf4t : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf4
  have hf6t : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)} := (sys.total _ _).resolve_left hf6
  have heqr_23_1 : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)} :=
    (sys.trans _ _ _ hf2r h01)
  have heqr_13_02 : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have heqr_12_03 : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)))
  have heqr_02_13 : sys.ge {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_02_12, sd_12_02]; exact h01)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
  have hng_1_02 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ h01 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp h1
        rw [sd_0_02, sd_02_0] at h2
        exact (hpos ⟨2, by omega⟩) h2
  have hng_1_03 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))
  have hng_1_023 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_0 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h h01)
  have hng_2_01 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_2_03 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_1_03 (sys.trans _ _ _ h21t h)
  have hng_2_13 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)} :=
    fun h => hf3 (sys.trans _ _ _ h02 h)
  have hng_2_013 : ¬sys.ge {(2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_3_0 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4)} :=
    fun h => hng_2_0 (sys.trans _ _ _ h23 h)
  have hng_3_1 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4)} :=
    fun h => h21 (sys.trans _ _ _ h23 h)
  have hng_3_01 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => hng_2_01 (sys.trans _ _ _ h23 h)
  have hng_3_02 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_1_02 (sys.trans _ _ _ h13 h)
  have hng_3_12 : ¬sys.ge {(3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)} :=
    fun h => hf4 (sys.trans _ _ _ h03 h)
  have hng_3_012 : ¬sys.ge {(3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} :=
    fun h => hng_3_0 (sys.trans _ _ _ h (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
  have hng_23_01 : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)} :=
    fun h => by
        have h1 := sys.trans _ _ _ hf2 h
        have h2 := (sys.additive {(0 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp h1
        rw [sd_0_01, sd_01_0] at h2
        exact (hpos ⟨1, by omega⟩) h2
  exact cancellation_from_weights_fin4 sys (![(2 : ℚ)/6, (2 : ℚ)/6, (1 : ℚ)/6, (1 : ℚ)/6])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro A B hDisj hLt
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hLt (by native_decide)) | (exact fun h => ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) h) | assumption)
    (by intro A B hDisj hEq hGe
        rcases finset_fin4_eq A with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases finset_fin4_eq B with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Finset.coe_empty, Finset.coe_univ] at * <;>
        first | exact absurd hDisj (by decide) | (exfalso; exact absurd hEq (by native_decide)) | (exfalso; exact ge_empty_contra sys hpos (by first | exact Set.insert_nonempty _ _ | exact Set.singleton_nonempty _ | exact Set.univ_nonempty) hGe) | assumption)

set_option maxHeartbeats 3200000 in
private theorem dispatch_TTT (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hpos ⟨0, by omega⟩ (by have := (sys.additive {(1 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ h10 hf4) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_02_01, sd_01_02]; exact h21)))); rw [sd_1_01, sd_01_1] at this; exact this)
            ·
              exfalso
              exact hf6 (sys.trans _ _ _ hf3 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf5 (sys.trans _ _ _ h10 hf2)
            ·
              exfalso
              exact hf5 (sys.trans _ _ _ h10 hf2)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf6 (sys.mono {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf4 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12))))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf6 (sys.mono {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
            ·
              exact chamber_81 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))

set_option maxHeartbeats 3200000 in
private theorem dispatch_TTF (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf6) (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact hpos ⟨3, by omega⟩ (by have := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ h10 hf3); rw [sd_1_13, sd_13_1] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf6) (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact hf5 (sys.trans _ _ _ h10 hf2)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf6) (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf6) (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exact chamber_77 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6

set_option maxHeartbeats 3200000 in
private theorem dispatch_TFT (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hpos ⟨2, by omega⟩ (by have := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ h10 hf4); rw [sd_1_12, sd_12_1] at this; exact this)
            ·
              exfalso
              exact hf6 (sys.trans _ _ _ hf3 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_03, sd_03_13]; exact h10)) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
            ·
              by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_87 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
              ·
                exact chamber_23 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact hf5 (sys.trans _ _ _ h10 hf2)
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exact chamber_80 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_13, sd_13_03]; exact h01)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))

set_option maxHeartbeats 3200000 in
private theorem dispatch_TFF (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ hf1 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10))); rw [sd_03_02, sd_02_03] at this; exact this)
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf6) (sys.trans _ _ _ (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_12_02, sd_02_12]; exact h10)))); rw [sd_03_02, sd_02_03] at this; exact this)
            ·
              exfalso
              exact hpos ⟨3, by omega⟩ (by have := (sys.additive {(1 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ h10 hf3); rw [sd_1_13, sd_13_1] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) (sys.trans _ _ _ h10 hf3)); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_13_12, sd_12_13] at this; exact this)
            ·
              by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_86 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
              ·
                exact chamber_21 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf5) h10) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact hf5 (sys.trans _ _ _ h10 hf2)
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ h01 hf5)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))); rw [sd_23_13, sd_13_23] at this; exact this)
            ·
              exact chamber_75 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6

set_option maxHeartbeats 3200000 in
private theorem dispatch_FTT (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hpos ⟨1, by omega⟩ (by have := (sys.additive {(2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ h21 hf5) (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))); rw [sd_2_12, sd_12_2] at this; exact this)
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_123, sd_123_23]; exact (by have := (sys.additive {(2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ h21 hf5) (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))); rw [sd_2_12, sd_12_2] at this; exact this))) ((sys.total _ _).resolve_left hf6)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_35 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
              ·
                exact chamber_5 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
            ·
              by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_73 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
              ·
                exact chamber_29 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ (sys.trans _ _ _ hf5 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) ((sys.total _ _).resolve_left hf4)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ (sys.trans _ _ _ hf5 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) ((sys.total _ _).resolve_left hf4)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact h23)))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) ((sys.total _ _).resolve_left hf2)) (sys.trans _ _ _ (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2)))) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact h23))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact h23)))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf4 (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12))))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exact chamber_69 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32))) (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32))) (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ (sys.trans _ _ _ hf5 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) ((sys.total _ _).resolve_left hf4)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ (sys.trans _ _ _ hf5 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)) ((sys.total _ _).resolve_left hf4)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)

set_option maxHeartbeats 3200000 in
private theorem dispatch_FTF (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hpos ⟨3, by omega⟩ (by have := (sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ h21 hf5); rw [sd_2_23, sd_23_2] at this; exact this)
            ·
              exfalso
              exact hf6 (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_123, sd_123_12]; exact (by have := (sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ h21 hf5); rw [sd_2_23, sd_23_2] at this; exact this))))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_33 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
              ·
                exact chamber_3 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
            ·
              by_cases hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_41 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r
              ·
                exact chamber_27 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ ((sys.additive {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_0_03, sd_03_0]; exact (by have := (sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ h21 hf5); rw [sd_2_23, sd_23_2] at this; exact this))) hf1)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
            ·
              by_cases hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}
              ·
                by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_85 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
                ·
                  exact chamber_47 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
              ·
                by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_72 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
                ·
                  exact chamber_39 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) ((sys.total _ _).resolve_left hf2)) (sys.trans _ _ _ (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2)))) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact ((sys.total _ _).resolve_left h32)))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)) (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf4)); rw [sd_13_12, sd_12_13] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}
              ·
                exact chamber_79 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r
              ·
                exact chamber_67 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all))))
            ·
              exfalso
              exact hpos ⟨3, by omega⟩ (by have := (sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ h21 hf5); rw [sd_2_23, sd_23_2] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all))))
            ·
              by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_84 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
              ·
                exact chamber_45 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)) ((sys.total _ _).resolve_left hf3)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf2 ((sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_23_13, sd_13_23]; exact h21)))
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact h12)))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact hf2 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact h12)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exact chamber_76 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6

set_option maxHeartbeats 3200000 in
private theorem dispatch_FFT (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
              ·
                by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_37 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
                ·
                  exact chamber_7 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
              ·
                by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_11 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
                ·
                  exact chamber_1 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
            ·
              by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_57 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
                ·
                  exact chamber_19 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_31 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
                ·
                  exact chamber_9 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_34 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
              ·
                exact chamber_4 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
            ·
              by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_53 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r
              ·
                exact chamber_28 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32)))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf3 ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_13_12, sd_12_13]; exact h32)))
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact h23)))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact h23)))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact hf3 (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
              ·
                exact chamber_55 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r
              ·
                exact chamber_17 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_71 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
              ·
                exact chamber_51 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact ((sys.total _ _).resolve_left h21))) ((sys.total _ _).resolve_left hf2)) (sys.trans _ _ _ (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2)))) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact ((sys.total _ _).resolve_left h21))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact h23))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact ((sys.total _ _).resolve_left h21))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact h23)))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact h23)))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exact chamber_68 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_03_02, sd_02_03]; exact h32))); rw [sd_12_02, sd_02_12] at this; exact this)

set_option maxHeartbeats 3200000 in
private theorem dispatch_FFF (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    : Cancellation 4 sys.ge := by
  by_cases hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
              ·
                by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_36 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
                ·
                  exact chamber_6 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
              ·
                by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_10 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
                ·
                  exact chamber_0 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r hf6r
            ·
              by_cases hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)}
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_43 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r hf5r
                ·
                  exact chamber_13 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r hf5r
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_30 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r hf5r
                ·
                  exact chamber_8 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r hf5r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              by_cases hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_32 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
              ·
                exact chamber_2 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf6r
            ·
              by_cases hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_40 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r
              ·
                exact chamber_26 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf4r
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf4 (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)))
            ·
              by_cases hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}
              ·
                by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                  ·
                    exact chamber_65 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
                  ·
                    exact chamber_25 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
                ·
                  by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                  ·
                    exact chamber_49 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
                  ·
                    exact chamber_15 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
              ·
                by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                  ·
                    exact chamber_56 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
                  ·
                    exact chamber_18 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
                ·
                  by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                  ·
                    exact chamber_42 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
                  ·
                    exact chamber_12 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r hf5r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_2_23, sd_23_2]; exact (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6); rw [sd_12_123, sd_123_12] at this; exact this))) ((sys.total _ _).resolve_left hf5))
            ·
              by_cases hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}
              ·
                by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_61 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r
                ·
                  exact chamber_46 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r
              ·
                by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_52 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r
                ·
                  exact chamber_38 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf3r
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h32 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf4); rw [sd_13_12, sd_12_13] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_63 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf5r
                ·
                  exact chamber_22 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf5r
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_54 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf5r
                ·
                  exact chamber_16 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf5r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}
              ·
                by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_83 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
                ·
                  exact chamber_59 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
              ·
                by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
                ·
                  exact chamber_70 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
                ·
                  exact chamber_50 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r hf2r
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (3 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_13_23, sd_23_13]; exact ((sys.total _ _).resolve_left h21))) ((sys.total _ _).resolve_left hf2)) (sys.trans _ _ _ (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2)))) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact ((sys.total _ _).resolve_left h21))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact ((sys.total _ _).resolve_left h32)))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact ((sys.total _ _).resolve_left h21))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))) ((sys.additive {(0 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_02_03, sd_03_02]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) (sys.trans _ _ _ hf4 ((sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_12_13, sd_13_12]; exact ((sys.total _ _).resolve_left h32))))); rw [sd_23_13, sd_13_23] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}
              ·
                exact chamber_78 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r
              ·
                exact chamber_66 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf1r
  ·
    by_cases hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) hf4)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_2_23, sd_23_2]; exact (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))); rw [sd_12_123, sd_123_12] at this; exact this))) ((sys.total _ _).resolve_left hf5))
            ·
              exfalso
              exact h21 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_2_23, sd_23_2]; exact (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))); rw [sd_12_123, sd_123_12] at this; exact this))) ((sys.total _ _).resolve_left hf5))
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact hf1 (sys.trans _ _ _ (sys.mono {(0 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all)) (sys.trans _ _ _ hf6 (sys.mono {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} (by intro x hx; fin_cases x <;> simp_all))))
            ·
              by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_64 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
                ·
                  exact chamber_24 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
              ·
                by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
                ·
                  exact chamber_48 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
                ·
                  exact chamber_14 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r hf5r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h21 (sys.trans _ _ _ ((sys.additive {(2 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_2_23, sd_23_2]; exact (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6); rw [sd_12_123, sd_123_12] at this; exact this))) ((sys.total _ _).resolve_left hf5))
            ·
              by_cases hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_60 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r
              ·
                exact chamber_44 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf3r
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)}
              ·
                exact chamber_62 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r
              ·
                exact chamber_20 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf5r
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              by_cases hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)}
              ·
                exact chamber_82 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
              ·
                exact chamber_58 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6 hf2r
    ·
      by_cases hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact ((sys.total _ _).resolve_left h21))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4))) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact ((sys.total _ _).resolve_left h21))))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ (sys.trans _ _ _ ((sys.total _ _).resolve_left hf4) hf6) (sys.trans _ _ _ ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (1 : Fin 4)}).mpr (by rw [sd_123_01, sd_01_123]; exact ((sys.total _ _).resolve_left hf2))) ((sys.additive {(0 : Fin 4), (1 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_01_02, sd_02_01]; exact ((sys.total _ _).resolve_left h21))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h21 (by have := (sys.additive {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf2) hf3); rw [sd_23_13, sd_13_23] at this; exact this)
      ·
        by_cases hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)}
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf1) (sys.trans _ _ _ ((sys.additive {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_03_123, sd_123_03]; exact hf4)) ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (2 : Fin 4)}).mpr (by rw [sd_123_02, sd_02_123]; exact ((sys.total _ _).resolve_left hf3))))); rw [sd_12_02, sd_02_12] at this; exact this)
        ·
          by_cases hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)}
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
            ·
              exfalso
              exact h10 (sys.trans _ _ _ hf5 ((sys.total _ _).resolve_left hf2))
          ·
            by_cases hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}
            ·
              exfalso
              exact h10 (by have := (sys.additive {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mp (sys.trans _ _ _ ((sys.total _ _).resolve_left hf3) (sys.trans _ _ _ hf6 ((sys.additive {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)}).mpr (by rw [sd_123_03, sd_03_123]; exact ((sys.total _ _).resolve_left hf4))))); rw [sd_13_03, sd_03_13] at this; exact this)
            ·
              exact chamber_74 sys hpos h01 h12 h23 h10 h21 h32 hf1 hf2 hf3 hf4 hf5 hf6

set_option maxHeartbeats 400000 in
/-- Canonical case: 0 ≥ 1 ≥ 2 ≥ 3 with all singletons positive.
    Dispatches to 88 chambers via 9+ by_cases. -/
theorem fa_cancellation_fin4_sorted (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3}) :
    Cancellation 4 sys.ge := by
  by_cases h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)}
  ·
    by_cases h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)}
    ·
      by_cases h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)}
      ·
        exact dispatch_TTT sys hpos h01 h12 h23 h10 h21 h32
      ·
        exact dispatch_TTF sys hpos h01 h12 h23 h10 h21 h32
    ·
      by_cases h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)}
      ·
        exact dispatch_TFT sys hpos h01 h12 h23 h10 h21 h32
      ·
        exact dispatch_TFF sys hpos h01 h12 h23 h10 h21 h32
  ·
    by_cases h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)}
    ·
      by_cases h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)}
      ·
        exact dispatch_FTT sys hpos h01 h12 h23 h10 h21 h32
      ·
        exact dispatch_FTF sys hpos h01 h12 h23 h10 h21 h32
    ·
      by_cases h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)}
      ·
        exact dispatch_FFT sys hpos h01 h12 h23 h10 h21 h32
      ·
        exact dispatch_FFF sys hpos h01 h12 h23 h10 h21 h32


set_option maxHeartbeats 12800000 in
set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
private theorem fa_cancellation_fin4_allpos (sys : EpistemicSystemFA (Fin 4))
    (h0 : ¬sys.ge ∅ {(0 : Fin 4)}) (h1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (h2 : ¬sys.ge ∅ {(2 : Fin 4)}) (h3 : ¬sys.ge ∅ {(3 : Fin 4)}) :
    Cancellation 4 sys.ge := by
  by_cases h01 : sys.ge {(0 : Fin 4)} {1} <;>
  by_cases h02 : sys.ge {(0 : Fin 4)} {2} <;>
  by_cases h03 : sys.ge {(0 : Fin 4)} {3} <;>
  by_cases h12 : sys.ge {(1 : Fin 4)} {2} <;>
  by_cases h13 : sys.ge {(1 : Fin 4)} {3} <;>
  by_cases h23 : sys.ge {(2 : Fin 4)} {3}
  all_goals try (have h10 := (sys.total {1} {0}).resolve_right ‹_›)
  all_goals try (have h20 := (sys.total {2} {0}).resolve_right ‹_›)
  all_goals try (have h30 := (sys.total {3} {0}).resolve_right ‹_›)
  all_goals try (have h21 := (sys.total {2} {1}).resolve_right ‹_›)
  all_goals try (have h31 := (sys.total {3} {1}).resolve_right ‹_›)
  all_goals try (have h32 := (sys.total {3} {2}).resolve_right ‹_›)
  all_goals try (exfalso; exact ‹¬sys.ge _ _› (sys.trans _ _ _ ‹sys.ge _ _› ‹sys.ge _ _›))
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {0} {1}› ‹sys.ge {1} {2}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {0} {2}› ‹sys.ge {2} {3}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {1} {2}› ‹sys.ge {2} {3}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {1} {0}› ‹sys.ge {0} {2}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {1} {0}› ‹sys.ge {0} {3}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {2} {0}› ‹sys.ge {0} {1}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {2} {0}› ‹sys.ge {0} {3}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {2} {1}› ‹sys.ge {1} {0}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {2} {1}› ‹sys.ge {1} {3}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {3} {0}› ‹sys.ge {0} {1}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {3} {0}› ‹sys.ge {0} {2}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {3} {1}› ‹sys.ge {1} {0}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {3} {1}› ‹sys.ge {1} {2}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {3} {2}› ‹sys.ge {2} {0}›)
  all_goals try (have := sys.trans _ _ _ ‹sys.ge {3} {2}› ‹sys.ge {2} {1}›)
  all_goals first
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,1,2,3], ![0,1,2,3], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,1,3,2], ![0,1,3,2], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,2,1,3], ![0,2,1,3], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,1,2], ![0,2,3,1], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,2,3,1], ![0,3,1,2], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,2,1], ![0,3,2,1], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,0,2,3], ![1,0,2,3], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,0,3,2], ![1,0,3,2], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,0,1,3], ![1,2,0,3], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,0,1,2], ![1,2,3,0], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,0,3,1], ![1,3,0,2], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,0,2,1], ![1,3,2,0], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,2,0,3], ![2,0,1,3], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,3,0,2], ![2,0,3,1], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,1,0,3], ![2,1,0,3], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,1,0,2], ![2,1,3,0], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,3,0,1], ![2,3,0,1], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,2,0,1], ![2,3,1,0], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,2,3,0], ![3,0,1,2], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,3,2,0], ![3,0,2,1], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,1,3,0], ![3,1,0,2], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,1,2,0], ![3,1,2,0], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,3,1,0], ![3,2,0,1], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))
    | (apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,2,1,0], ![3,2,1,0], by decide, by decide⟩)
       refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
       all_goals (rw [perm_singleton_iff]; dsimp; assumption))


theorem fa_cancellation_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    Cancellation 4 sys.ge := by
  by_cases h0 : sys.ge ∅ {(0 : Fin 4)}
  · exact fa_cancellation_fin4_null0 sys h0 (by
      by_contra hall; push_neg at hall
      exact not_all_null_fin4 sys h0 (hall 0) (hall 1) (hall 2))
  · by_cases h1 : sys.ge ∅ {(1 : Fin 4)}
    · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 1) sys
        (null_elem_reduce (transportFA (Equiv.swap 0 1) sys)
          ((perm_null_convert _ _ 0 1 (by decide)).mpr h1)
          ⟨0, fun h => h0 ((perm_null_convert _ _ 1 0 (by decide)).mp h)⟩
          (fun sys' => theorem8a_fin3 sys'))
      exact representable_implies_cancellation sys m hm
    · by_cases h2 : sys.ge ∅ {(2 : Fin 4)}
      · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 2) sys
          (null_elem_reduce (transportFA (Equiv.swap 0 2) sys)
            ((perm_null_convert _ _ 0 2 (by decide)).mpr h2)
            ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
            (fun sys' => theorem8a_fin3 sys'))
        exact representable_implies_cancellation sys m hm
      · by_cases h3 : sys.ge ∅ {(3 : Fin 4)}
        · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 3) sys
            (null_elem_reduce (transportFA (Equiv.swap 0 3) sys)
              ((perm_null_convert _ _ 0 3 (by decide)).mpr h3)
              ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
              (fun sys' => theorem8a_fin3 sys'))
          exact representable_implies_cancellation sys m hm
        · exact fa_cancellation_fin4_allpos sys h0 h1 h2 h3


end Core.Scale