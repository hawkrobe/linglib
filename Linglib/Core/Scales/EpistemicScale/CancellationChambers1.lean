import Linglib.Core.Scales.EpistemicScale.CancellationHelpers

/-! # Chamber proofs group 1: chambers 0-21 -/

namespace Core.Scale

attribute [local instance] Classical.propDecidable

theorem chamber_0 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(8 : ℚ)/15, (4 : ℚ)/15, (2 : ℚ)/15, (1 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    []
    (by native_decide)
    (by intro _ hmem; cases hmem)

theorem chamber_1 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(6 : ℚ)/11, (3 : ℚ)/11, (1 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
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

theorem chamber_2 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(10 : ℚ)/19, (4 : ℚ)/19, (3 : ℚ)/19, (2 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    []
    (by native_decide)
    (by intro _ hmem; cases hmem)

theorem chamber_3 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(6 : ℚ)/11, (2 : ℚ)/11, (2 : ℚ)/11, (1 : ℚ)/11])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
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

theorem chamber_4 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(8 : ℚ)/15, (3 : ℚ)/15, (2 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
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

theorem chamber_5 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(4 : ℚ)/7, (1 : ℚ)/7, (1 : ℚ)/7, (1 : ℚ)/7])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
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

theorem chamber_6 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(7 : ℚ)/13, (3 : ℚ)/13, (2 : ℚ)/13, (1 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({1}, {2, 3}),
     ({2, 3}, {1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_7 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(5 : ℚ)/9, (2 : ℚ)/9, (1 : ℚ)/9, (1 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {0, 1}),
     ({1, 2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({1}, {2, 3}),
     ({2}, {3}),
     ({3}, {2}),
     ({2, 3}, {1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_8 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(10 : ℚ)/21, (6 : ℚ)/21, (3 : ℚ)/21, (2 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_9 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(8 : ℚ)/17, (5 : ℚ)/17, (2 : ℚ)/17, (2 : ℚ)/17])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_10 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(7 : ℚ)/14, (4 : ℚ)/14, (2 : ℚ)/14, (1 : ℚ)/14])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 2, 3}),
     ({1, 2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_11 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(5 : ℚ)/10, (3 : ℚ)/10, (1 : ℚ)/10, (1 : ℚ)/10])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({1}, {0}),
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
     ({1, 2}, {0}),
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 2, 3}),
     ({2}, {3}),
     ({3}, {2}),
     ({1, 2, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_12 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(10 : ℚ)/23, (7 : ℚ)/23, (4 : ℚ)/23, (2 : ℚ)/23])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_13 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(6 : ℚ)/13, (4 : ℚ)/13, (2 : ℚ)/13, (1 : ℚ)/13])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0, 3}),
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 2}),
     ({1, 2}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_14 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(8 : ℚ)/19, (6 : ℚ)/19, (4 : ℚ)/19, (1 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_15 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(7 : ℚ)/16, (5 : ℚ)/16, (3 : ℚ)/16, (1 : ℚ)/16])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 3}, {0}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_16 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(10 : ℚ)/25, (8 : ℚ)/25, (4 : ℚ)/25, (3 : ℚ)/25])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_17 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(6 : ℚ)/15, (5 : ℚ)/15, (2 : ℚ)/15, (2 : ℚ)/15])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_18 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(8 : ℚ)/19, (6 : ℚ)/19, (3 : ℚ)/19, (2 : ℚ)/19])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 3}),
     ({1, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_19 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(4 : ℚ)/9, (3 : ℚ)/9, (1 : ℚ)/9, (1 : ℚ)/9])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({1, 2}, {0, 3}),
     ({1, 3}, {0, 2}),
     ({2, 3}, {0}),
     ({2, 3}, {1}),
     ({2, 3}, {0, 1})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> assumption)
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({2}, {3}),
     ({3}, {2}),
     ({1, 2}, {0}),
     ({1, 3}, {0})]
    (by native_decide)
    (by intro ⟨A, B⟩ hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> (try simp only [Finset.coe_insert, Finset.coe_singleton])
        <;> (try intro _)
        <;> assumption)

theorem chamber_20 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(8 : ℚ)/21, (7 : ℚ)/21, (4 : ℚ)/21, (2 : ℚ)/21])
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    hpos
    [({0}, {1, 2}),
     ({0}, {1, 3}),
     ({0}, {1, 2, 3}),
     ({1}, {0}),
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
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

theorem chamber_21 (sys : EpistemicSystemFA (Fin 4))
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
  exact cancellation_from_pairs sys (![(4 : ℚ)/11, (4 : ℚ)/11, (2 : ℚ)/11, (1 : ℚ)/11])
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
     ({2, 3}, {0}),
     ({2, 3}, {1}),
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

end Core.Scale