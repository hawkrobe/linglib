import Linglib.Core.Scales.EpistemicScale.CancellationHelpers

/-! # Chamber proofs group 4: chambers 66-87 -/

namespace Core.Scale

attribute [local instance] Classical.propDecidable

theorem chamber_66 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(8 : ℚ)/23, (6 : ℚ)/23, (5 : ℚ)/23, (4 : ℚ)/23])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    []
    (by native_decide)
    (by intro _ hmem; cases hmem)

theorem chamber_67 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(6 : ℚ)/17, (4 : ℚ)/17, (4 : ℚ)/17, (3 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({1}, {2}),
     ({2}, {1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_68 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(5 : ℚ)/15, (4 : ℚ)/15, (3 : ℚ)/15, (3 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({2}, {3}),
     ({3}, {2})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_69 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(3 : ℚ)/9, (2 : ℚ)/9, (2 : ℚ)/9, (2 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({1}, {2}),
     ({1}, {3}),
     ({2}, {1}),
     ({2}, {3}),
     ({3}, {1}),
     ({3}, {2})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_70 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(7 : ℚ)/19, (5 : ℚ)/19, (4 : ℚ)/19, (3 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {2, 3}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_71 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(4 : ℚ)/11, (3 : ℚ)/11, (2 : ℚ)/11, (2 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {2, 3}),
     ({2}, {3}),
     ({3}, {2}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_72 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(5 : ℚ)/13, (3 : ℚ)/13, (3 : ℚ)/13, (2 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 3}),
     ({0}, {2, 3}),
     ({1}, {2}),
     ({2}, {1}),
     ({1, 3}, {0}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_73 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(2 : ℚ)/5, (1 : ℚ)/5, (1 : ℚ)/5, (1 : ℚ)/5])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({1}, {2}),
     ({1}, {3}),
     ({2}, {1}),
     ({2}, {3}),
     ({3}, {1}),
     ({3}, {2}),
     ({1, 2}, {0}),
     ({1, 3}, {0}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_74 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(7 : ℚ)/21, (6 : ℚ)/21, (5 : ℚ)/21, (3 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({0, 3}, {1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    []
    (by native_decide)
    (by intro _ hmem; cases hmem)

theorem chamber_75 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(4 : ℚ)/13, (4 : ℚ)/13, (3 : ℚ)/13, (2 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({0, 3}, {1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1}),
     ({1}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_76 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(5 : ℚ)/15, (4 : ℚ)/15, (4 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({0, 3}, {1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({1}, {2}),
     ({2}, {1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_77 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(2 : ℚ)/7, (2 : ℚ)/7, (2 : ℚ)/7, (1 : ℚ)/7])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({0, 3}, {1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1}),
     ({0}, {2}),
     ({1}, {0}),
     ({1}, {2}),
     ({2}, {0}),
     ({2}, {1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_78 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(6 : ℚ)/18, (5 : ℚ)/18, (4 : ℚ)/18, (3 : ℚ)/18])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0, 3}, {1, 2}),
     ({1, 2}, {0, 3})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_79 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(4 : ℚ)/12, (3 : ℚ)/12, (3 : ℚ)/12, (2 : ℚ)/12])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({1}, {2}),
     ({2}, {1}),
     ({0, 3}, {1, 2}),
     ({1, 2}, {0, 3})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_80 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(3 : ℚ)/10, (3 : ℚ)/10, (2 : ℚ)/10, (2 : ℚ)/10])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1}),
     ({1}, {0}),
     ({2}, {3}),
     ({3}, {2}),
     ({0, 2}, {1, 3}),
     ({0, 3}, {1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_81 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(1 : ℚ)/4, (1 : ℚ)/4, (1 : ℚ)/4, (1 : ℚ)/4])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {2, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1}),
     ({0}, {2}),
     ({0}, {3}),
     ({1}, {0}),
     ({1}, {2}),
     ({1}, {3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({0, 1}, {2, 3}),
     ({0, 2}, {1, 3}),
     ({0, 3}, {1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_82 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(6 : ℚ)/17, (5 : ℚ)/17, (4 : ℚ)/17, (2 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({0, 3}, {1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {2, 3}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_83 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(5 : ℚ)/14, (4 : ℚ)/14, (3 : ℚ)/14, (2 : ℚ)/14])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {2, 3}),
     ({0, 3}, {1, 2}),
     ({1, 2}, {0, 3}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_84 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(4 : ℚ)/11, (3 : ℚ)/11, (3 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({0, 3}, {1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 3}),
     ({0}, {2, 3}),
     ({1}, {2}),
     ({2}, {1}),
     ({1, 3}, {0}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_85 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(3 : ℚ)/8, (2 : ℚ)/8, (2 : ℚ)/8, (1 : ℚ)/8])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {2, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 3}),
     ({0}, {2, 3}),
     ({1}, {2}),
     ({2}, {1}),
     ({0, 3}, {1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_86 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(3 : ℚ)/9, (3 : ℚ)/9, (2 : ℚ)/9, (1 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {2}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({0, 3}, {1, 2}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1}),
     ({0}, {2, 3}),
     ({1}, {0}),
     ({1}, {2, 3}),
     ({2, 3}, {0}),
     ({2, 3}, {1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_87 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(2 : ℚ)/6, (2 : ℚ)/6, (1 : ℚ)/6, (1 : ℚ)/6])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0, 2}),
     ({1}, {0, 3}),
     ({1}, {0, 2, 3}),
     ({2}, {0}),
     ({2}, {1}),
     ({2}, {0, 1}),
     ({2}, {0, 3}),
     ({2}, {1, 3}),
     ({2}, {0, 1, 3}),
     ({3}, {0}),
     ({3}, {1}),
     ({3}, {0, 1}),
     ({3}, {0, 2}),
     ({3}, {1, 2}),
     ({3}, {0, 1, 2}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1}),
     ({0}, {2, 3}),
     ({1}, {0}),
     ({1}, {2, 3}),
     ({2}, {3}),
     ({3}, {2}),
     ({0, 2}, {1, 3}),
     ({0, 3}, {1, 2}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

end Core.Scale