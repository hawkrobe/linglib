import Linglib.Core.Scales.EpistemicScale.CancellationChambers
import Linglib.Core.Scales.EpistemicScale.CancellationHelpers

/-!
# Fin 4 cancellation: dispatch + allpos + main theorem

Auto-generated: dispatches the 88 chamber proofs to prove cancellation
for all Fin 4 epistemic systems.
-/

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 3200000 in
theorem dispatch_TTT (sys : EpistemicSystemFA (Fin 4))
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
theorem dispatch_TTF (sys : EpistemicSystemFA (Fin 4))
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
theorem dispatch_TFT (sys : EpistemicSystemFA (Fin 4))
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
theorem dispatch_TFF (sys : EpistemicSystemFA (Fin 4))
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
theorem dispatch_FTT (sys : EpistemicSystemFA (Fin 4))
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
theorem dispatch_FTF (sys : EpistemicSystemFA (Fin 4))
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
theorem dispatch_FFT (sys : EpistemicSystemFA (Fin 4))
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
theorem dispatch_FFF (sys : EpistemicSystemFA (Fin 4))
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


set_option maxHeartbeats 800000 in
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
  -- 39 surviving goals, each with exact permutation (no transitivity lines needed)
  -- Goal 0 (TTTTTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,1,2,3], ![0,1,2,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 1 (TTTTTF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,1,3,2], ![0,1,3,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 3 (TTTTFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,2,3,1], ![0,3,1,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 4 (TTTFTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,2,1,3], ![0,2,1,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 6 (TTTFFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,1,2], ![0,2,3,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 7 (TTTFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,2,1], ![0,3,2,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 9 (TTFTTF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,1,3,2], ![0,1,3,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 11 (TTFTFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,2,3,0], ![3,0,1,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 12 (TTFFTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,2,1,3], ![0,2,1,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 14 (TTFFFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,1,2], ![0,2,3,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 15 (TTFFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,3,2,0], ![3,0,2,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 16 (TFTTTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,1,2,3], ![0,1,2,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 20 (TFTFTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,2,0,3], ![2,0,1,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 22 (TFTFFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,3,0,2], ![2,0,3,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 23 (TFTFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,2,1], ![0,3,2,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 25 (TFFTTF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,1,3,2], ![0,1,3,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 27 (TFFTFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,2,3,0], ![3,0,1,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 28 (TFFFTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,2,0,3], ![2,0,1,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 30 (TFFFFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,3,0,1], ![2,3,0,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 31 (TFFFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,3,1,0], ![3,2,0,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 32 (FTTTTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,0,2,3], ![1,0,2,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 33 (FTTTTF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,0,3,2], ![1,0,3,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 35 (FTTTFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,2,3,1], ![0,3,1,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 39 (FTTFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,2,1], ![0,3,2,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 41 (FTFTTF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,0,3,1], ![1,3,0,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 42 (FTFTFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,1,2], ![0,2,3,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 43 (FTFTFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,1,3,0], ![3,1,0,2], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 46 (FTFFFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,1,2], ![0,2,3,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 47 (FTFFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![1,3,2,0], ![3,0,2,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 48 (FFTTTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,0,1,3], ![1,2,0,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 52 (FFTFTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![2,1,0,3], ![2,1,0,3], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 55 (FFTFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![0,3,2,1], ![0,3,2,1], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 56 (FFFTTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,0,1,2], ![1,2,3,0], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 57 (FFFTTF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,0,2,1], ![1,3,2,0], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 58 (FFFTFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,0,1,2], ![1,2,3,0], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 59 (FFFTFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,1,2,0], ![3,1,2,0], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 60 (FFFFTT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,1,0,2], ![2,1,3,0], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 62 (FFFFFT)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,2,0,1], ![2,3,1,0], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)
  -- Goal 63 (FFFFFF)
  · apply perm_cancellation (show Fin 4 ≃ Fin 4 from ⟨![3,2,1,0], ![3,2,1,0], by decide, by decide⟩)
    refine fa_cancellation_fin4_sorted _ (fun i => by rw [perm_null_iff]; fin_cases i <;> (dsimp; assumption)) ?_ ?_ ?_
    all_goals (rw [perm_singleton_iff]; dsimp; assumption)


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


/-- **Theorem 8a for Fin 4**: every FA system on 4 elements is representable.
    Proof via Scott cancellation — see `Cancellation.lean` for the framework. -/
theorem theorem8a_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  cancellation_implies_representable sys (fa_cancellation_fin4 sys)

end Core.Scale