import Linglib.Core.Scales.EpistemicScale.Fin4.Defs
import Linglib.Core.Scales.EpistemicScale.Fin4.Case4
import Linglib.Core.Scales.EpistemicScale.Fin4.Case31
import Linglib.Core.Scales.EpistemicScale.Fin4.Case22
import Linglib.Core.Scales.EpistemicScale.Fin4.Case211
import Linglib.Core.Scales.EpistemicScale.Fin4.Case13
import Linglib.Core.Scales.EpistemicScale.Fin4.Case121
import Linglib.Core.Scales.EpistemicScale.Fin4.Case112
import Linglib.Core.Scales.EpistemicScale.Fin4.Case1111

namespace Core.Scale

attribute [local instance] Classical.propDecidable

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
  by_cases h10 : sys.ge {(1 : Fin 4)} {0}
  · by_cases h21 : sys.ge {(2 : Fin 4)} {1}
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · have h20 := sys.trans _ _ _ h21 h10
        have h31 := sys.trans _ _ _ h32 h21
        have h30 := sys.trans _ _ _ h31 h10
        exact fin4_case_4 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h13 h31 h23 h32 h02 h20 h03 h30
      · have h20 := sys.trans _ _ _ h21 h10
        exact fin4_case_31 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h23 h32 h02 h20 h03 h13
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · exact fin4_case_22 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h23 h32 h02 h13 h03
      · exact fin4_case_211 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h23 h32 h02 h13 h03
  · by_cases h21 : sys.ge {(2 : Fin 4)} {1}
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · have h31 := sys.trans _ _ _ h32 h21
        exact fin4_case_13 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h13 h31 h23 h32 h02 h03
      · exact fin4_case_121 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h23 h32 h02 h13 h03
    · by_cases h32 : sys.ge {(3 : Fin 4)} {2}
      · exact fin4_case_112 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h23 h32 h02 h13 h03
      · exact fin4_case_1111 sys hn0 hn1 hn2 hn3 h01 h10 h12 h21 h23 h32 h02 h13 h03

private def mkPerm4 (f : Fin 4 → Fin 4) (g : Fin 4 → Fin 4)
    (hfg : ∀ i, g (f i) = i) (hgf : ∀ i, f (g i) = i) : Fin 4 ≃ Fin 4 where
  toFun := f
  invFun := g
  left_inv := hfg
  right_inv := hgf

set_option maxHeartbeats 6400000 in
private theorem theorem8a_fin4_allnonnull (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)}) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  rcases sys.total {(0 : Fin 4)} {1} with h01 | h10
  · rcases sys.total {(1 : Fin 4)} {2} with h12 | h21
    · rcases sys.total {(2 : Fin 4)} {3} with h23 | h32
      · exact fin4_sorted_case sys hn0 hn1 hn2 hn3 h01 h12 h23
      · rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
        · exact perm_repr (Equiv.swap 2 3) sys
            (fin4_sorted_case _ (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h01)
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h13)
              (by rw [perm_ge_singleton]; simp; exact h32))
        · rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · exact perm_repr
              (⟨fun | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1,
                fun | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h03)
                (by rw [perm_ge_singleton]; exact h31)
                (by rw [perm_ge_singleton]; exact h12))
          · exact perm_repr
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
      · rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
        · rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
          · exact perm_repr (Equiv.swap 1 2) sys
              (fin4_sorted_case _ (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h02)
                (by rw [perm_ge_singleton]; simp; exact h21)
                (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h13))
          · exact perm_repr
              (⟨fun | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2,
                fun | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h02)
                (by rw [perm_ge_singleton]; exact h23)
                (by rw [perm_ge_singleton]; exact h31))
        · rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
            · exact perm_repr
                (⟨fun | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3,
                  fun | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3,
                  fun i => by fin_cases i <;> rfl,
                  fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
                (fin4_sorted_case _
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rw [perm_ge_singleton]; exact h20)
                  (by rw [perm_ge_singleton]; exact h01)
                  (by rw [perm_ge_singleton]; exact h13))
            · exact perm_repr
                (⟨fun | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2,
                  fun | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1,
                  fun i => by fin_cases i <;> rfl,
                  fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
                (fin4_sorted_case _
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rw [perm_ge_singleton]; exact h20)
                  (by rw [perm_ge_singleton]; exact h03)
                  (by rw [perm_ge_singleton]; exact h31))
          · exact perm_repr
              (⟨fun | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1,
                fun | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h23)
                (by rw [perm_ge_singleton]; exact h30)
                (by rw [perm_ge_singleton]; exact h01))
      · have h31 : sys.ge {(3 : Fin 4)} {1} := sys.trans _ _ _ h32 h21
        rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
        · rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
          · exact perm_repr
              (⟨fun | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1,
                fun | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h03)
                (by rw [perm_ge_singleton]; exact h32)
                (by rw [perm_ge_singleton]; exact h21))
          · exact perm_repr
              (⟨fun | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1,
                fun | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h03)
                (by rw [perm_ge_singleton]; exact h32)
                (by rw [perm_ge_singleton]; exact h21))
        · rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
          · exact perm_repr
              (⟨fun | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0,
                fun | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h30)
                (by rw [perm_ge_singleton]; exact h02)
                (by rw [perm_ge_singleton]; exact h21))
          · exact perm_repr
              (⟨fun | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0,
                fun | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h32)
                (by rw [perm_ge_singleton]; exact h20)
                (by rw [perm_ge_singleton]; exact h01))
  · rcases sys.total {(1 : Fin 4)} {2} with h12 | h21
    · rcases sys.total {(2 : Fin 4)} {3} with h23 | h32
      · rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
        · exact perm_repr (Equiv.swap 0 1) sys
            (fin4_sorted_case _ (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rw [perm_ge_singleton]; simp; exact h10)
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h02)
              (by rw [perm_ge_singleton]; simp [Equiv.swap_apply_of_ne_of_ne]; exact h23))
        · rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · exact perm_repr
              (⟨fun | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3,
                fun | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h12)
                (by rw [perm_ge_singleton]; exact h20)
                (by rw [perm_ge_singleton]; exact h03))
          · exact perm_repr
              (⟨fun | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2,
                fun | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h12)
                (by rw [perm_ge_singleton]; exact h23)
                (by rw [perm_ge_singleton]; exact h30))
      · rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
        · rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
          · exact perm_repr
              (⟨fun | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2,
                fun | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h10)
                (by rw [perm_ge_singleton]; exact h03)
                (by rw [perm_ge_singleton]; exact h32))
          · rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
            · exact perm_repr
                (⟨fun | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1,
                  fun | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2,
                  fun i => by fin_cases i <;> rfl,
                  fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
                (fin4_sorted_case _
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rw [perm_ge_singleton]; exact h13)
                  (by rw [perm_ge_singleton]; exact h30)
                  (by rw [perm_ge_singleton]; exact h02))
            · exact perm_repr
                (⟨fun | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1,
                  fun | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0,
                  fun i => by fin_cases i <;> rfl,
                  fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
                (fin4_sorted_case _
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                  (by rw [perm_ge_singleton]; exact h13)
                  (by rw [perm_ge_singleton]; exact h32)
                  (by rw [perm_ge_singleton]; exact h20))
        · rcases sys.total {(0 : Fin 4)} {2} with h02 | h20
          · exact perm_repr
              (⟨fun | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0,
                fun | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h31)
                (by rw [perm_ge_singleton]; exact h10)
                (by rw [perm_ge_singleton]; exact h02))
          · exact perm_repr
              (⟨fun | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0,
                fun | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h31)
                (by rw [perm_ge_singleton]; exact h12)
                (by rw [perm_ge_singleton]; exact h20))
    · have h20 : sys.ge {(2 : Fin 4)} {0} := sys.trans _ _ _ h21 h10
      rcases sys.total {(2 : Fin 4)} {3} with h23 | h32
      · rcases sys.total {(0 : Fin 4)} {3} with h03 | h30
        · exact perm_repr
            (⟨fun | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3,
              fun | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3,
              fun i => by fin_cases i <;> rfl,
              fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
            (fin4_sorted_case _
              (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
              (by rw [perm_ge_singleton]; exact h21)
              (by rw [perm_ge_singleton]; exact h10)
              (by rw [perm_ge_singleton]; exact h03))
        · rcases sys.total {(1 : Fin 4)} {3} with h13 | h31
          · exact perm_repr
              (⟨fun | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2,
                fun | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h21)
                (by rw [perm_ge_singleton]; exact h13)
                (by rw [perm_ge_singleton]; exact h30))
          · exact perm_repr
              (⟨fun | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1,
                fun | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0,
                fun i => by fin_cases i <;> rfl,
                fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
              (fin4_sorted_case _
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
                (by rw [perm_ge_singleton]; exact h23)
                (by rw [perm_ge_singleton]; exact h31)
                (by rw [perm_ge_singleton]; exact h10))
      · have h30 : sys.ge {(3 : Fin 4)} {0} := sys.trans _ _ _ h32 h20
        have h31 : sys.ge {(3 : Fin 4)} {1} := sys.trans _ _ _ h32 h21
        exact perm_repr
          (⟨fun | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0,
            fun | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0,
            fun i => by fin_cases i <;> rfl,
            fun i => by fin_cases i <;> rfl⟩ : Fin 4 ≃ Fin 4) sys
          (fin4_sorted_case _
            (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
            (by rwa [perm_null_iff]) (by rwa [perm_null_iff])
            (by rw [perm_ge_singleton]; exact h32)
            (by rw [perm_ge_singleton]; exact h21)
            (by rw [perm_ge_singleton]; exact h10))

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
