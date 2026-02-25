import Linglib.Core.Scales.EpistemicScale.Fin4.Defs

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000 in
/-- Case (1,1,2): 17 sub-cases. -/
theorem fin4_case_112 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (hng10 : ¬sys.ge {(1 : Fin 4)} {0})
    (h12 : sys.ge {(1 : Fin 4)} {2})
    (hng21 : ¬sys.ge {(2 : Fin 4)} {1})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h32 : sys.ge {(3 : Fin 4)} {2})
    (h02 : sys.ge {(0 : Fin 4)} {2})
    (h13 : sys.ge {(1 : Fin 4)} {3})
    (h03 : sys.ge {(0 : Fin 4)} {3})
    :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  have hng20 : ¬sys.ge {(2 : Fin 4)} {0} := fun h => hng21 (sys.trans _ _ _ h h01)
  have hng31 : ¬sys.ge {(3 : Fin 4)} {1} := fun h => hng21 (sys.trans _ _ _ h23 h)
  have hng30 : ¬sys.ge {(3 : Fin 4)} {0} := fun h => hng31 (sys.trans _ _ _ h h01)
  have hne01 := nge_empty_of_elem sys hn0 (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl)
  have hne02 := nge_empty_of_elem sys hn0 (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl)
  have hne03 := nge_empty_of_elem sys hn0 (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl)
  have hne12 := nge_empty_of_elem sys hn1 (show (1:Fin 4) ∈ ({1,2}:Set _) from Or.inl rfl)
  have hne13 := nge_empty_of_elem sys hn1 (show (1:Fin 4) ∈ ({1,3}:Set _) from Or.inl rfl)
  have hne23 := nge_empty_of_elem sys hn2 (show (2:Fin 4) ∈ ({2,3}:Set _) from Or.inl rfl)
  have hne012 := nge_empty_of_elem sys hn0 (show (0:Fin 4) ∈ ({0,1,2}:Set _) from Or.inl rfl)
  have hne013 := nge_empty_of_elem sys hn0 (show (0:Fin 4) ∈ ({0,1,3}:Set _) from Or.inl rfl)
  have hne023 := nge_empty_of_elem sys hn0 (show (0:Fin 4) ∈ ({0,2,3}:Set _) from Or.inl rfl)
  have hne123 := nge_empty_of_elem sys hn1 (show (1:Fin 4) ∈ ({1,2,3}:Set _) from Or.inl rfl)
  have hd1 := ge_superset sys (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl) h01
  have hd2 := ge_superset sys (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl) h01
  have hd3 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h02
  have hd4 := ge_superset sys (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl) h02
  have hd5 := ge_superset sys (show (1:Fin 4) ∈ ({1,3}:Set _) from Or.inl rfl) h12
  have hd6 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h03
  have hd7 := ge_superset sys (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl) h03
  have hd8 := ge_superset sys (show (1:Fin 4) ∈ ({1,2}:Set _) from Or.inl rfl) h13
  have hd9 := ge_superset sys (show (0:Fin 4) ∈ ({0,2,3}:Set _) from Or.inl rfl) h01
  have hd10 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,3}:Set _) from Or.inl rfl) h02
  have hd11 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,2}:Set _) from Or.inl rfl) h03
  have hd12 := nge_singleton_pair sys h01 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd13 := nge_singleton_pair sys h01 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd14 := nge_singleton_pair sys h02 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd15 := nge_singleton_pair sys h02 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd16 := nge_singleton_pair sys h12 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd17 := nge_singleton_pair sys h03 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd18 := nge_singleton_pair sys h03 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd19 := nge_singleton_pair sys h13 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd20 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hng10
  have hd21 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hng20
  have hd22 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hng30
  have hd23 : sys.ge ({0,1} : Set (Fin 4)) ({2,3} : Set _) := by
    have h1 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
      rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
          show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h12
    have h2 : sys.ge ({0,2} : Set _) ({2,3} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {2,3},
          show ({0,2} : Set (Fin 4)) \ {2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({2,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h03
    exact sys.trans _ _ _ h1 h2
  have hd24 : sys.ge ({0,2} : Set (Fin 4)) ({1,3} : Set _) := by
    have h1 : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
          show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h23
    have h2 : sys.ge ({0,3} : Set _) ({1,3} : Set _) := by
      rw [sys.additive ({0,3} : Set (Fin 4)) {1,3},
          show ({0,3} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({1,3} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h01
    exact sys.trans _ _ _ h1 h2
  have hd25 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := by
    have h1 : sys.ge ({0,3} : Set (Fin 4)) ({0,2} : Set _) := by
      rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
          show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h32
    have h2 : sys.ge ({0,2} : Set _) ({1,2} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {1,2},
          show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h01
    exact sys.trans _ _ _ h1 h2
  have hd26 : ¬sys.ge ({2,3} : Set (Fin 4)) ({0,1} : Set _) := fun h => by
    have h_bc : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
      rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
          show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h12
    have h1 := sys.trans _ _ _ h h_bc
    rw [sys.additive ({2,3} : Set (Fin 4)) {0,2},
        show ({2,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
        show ({0,2} : Set (Fin 4)) \ {2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
    exact hng30 h1
  have hd27 : ¬sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) := fun h => by
    have h_bc : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
          show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h23
    have h1 := sys.trans _ _ _ h h_bc
    rw [sys.additive ({1,3} : Set (Fin 4)) {0,3},
        show ({1,3} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
        show ({0,3} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
    exact hng10 h1
  have hd28 : ¬sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := fun h => by
    have h_bc : sys.ge ({0,3} : Set (Fin 4)) ({0,2} : Set _) := by
      rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
          show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h32
    have h1 := sys.trans _ _ _ h h_bc
    rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
        show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
        show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
    exact hng10 h1
  by_cases h12_0_hyp : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
  · -- h12_0=T (8 pat)
    have hd29 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
      have h_s1 : sys.ge ({1,2,3} : Set _) ({0,3} : Set _) := by
        rw [sys.additive ({1,2,3} : Set _) {0,3},
            show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
            show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
        exact h12_0_hyp
      have h_s2 : sys.ge ({0,3} : Set (Fin 4)) ({0,2} : Set _) := by
        rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
            show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
            show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
        exact h32
      have h_s3 := sys.trans _ _ _ h_s1 h_s2
      rw [sys.additive ({1,2,3} : Set _) {0,2},
          show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
      exact h_s3
    by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
    · -- h1_23=T (4 pat)
      have hd30 := sys.trans _ _ _ h01 h1_23_hyp
      by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
      · -- h0_12=T (2 pat)
        have hd31 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h23
          exact sys.trans _ _ _ h0_12_hyp h_mid
        by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
        · -- h23_1=T (1 pat)
          by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
          · -- h23_0=T
            have hd32 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
            have hd33 := nge_singleton_pair sys hd32 hn2
              (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
              (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
            have hd34 := nge_singleton_pair sys hd32 hn3
              (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
              (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
            have hd35 := nge_superset sys
              (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd33
            have hd36 : sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) := by
              have h1 : sys.ge ({1,3} : Set (Fin 4)) ({0,3} : Set _) := by
                rw [sys.additive ({1,3} : Set (Fin 4)) {0,3},
                    show ({1,3} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact hd32
              have h2 : sys.ge ({0,3} : Set _) ({0,2} : Set _) := by
                rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
                    show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact h32
              exact sys.trans _ _ _ h1 h2
            have hd37 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := by
              have h1 : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                    show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact hd32
              have h2 : sys.ge ({0,2} : Set _) ({0,3} : Set _) := by
                rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                    show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact h23
              exact sys.trans _ _ _ h1 h2
            have hd38 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd35)
            exact absurd h0_12_hyp hd33
          · -- h23_0=F
            by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
            · -- h0_123=T
              have hd39 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
                have h1 := sys.trans _ _ _ h h0_123_hyp
                rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
                    show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                    show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
                exact hn3 h1
              have hd40 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
                have h1 := sys.trans _ _ _ h h0_123_hyp
                rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
                    show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                    show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
                exact hn2 h1
              exact absurd h12_0_hyp hd39
            · -- h0_123=F
              have hd41 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_123_hyp)
              exact fin4_witness sys (3/7) (2/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (3/7) (2/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  ⟨fun h => absurd h hn0, fun h => by linarith⟩
                  ⟨fun h => absurd h hn1, fun h => by linarith⟩
                  ⟨fun h => absurd h hn2, fun h => by linarith⟩
                  ⟨fun h => absurd h hn3, fun h => by linarith⟩
                  ⟨fun h => absurd h hne01, fun h => by linarith⟩
                  ⟨fun h => absurd h hne02, fun h => by linarith⟩
                  ⟨fun h => absurd h hne03, fun h => by linarith⟩
                  ⟨fun h => absurd h hne12, fun h => by linarith⟩
                  ⟨fun h => absurd h hne13, fun h => by linarith⟩
                  ⟨fun h => absurd h hne23, fun h => by linarith⟩
                  ⟨fun h => absurd h hne012, fun h => by linarith⟩
                  ⟨fun h => absurd h hne013, fun h => by linarith⟩
                  ⟨fun h => absurd h hne023, fun h => by linarith⟩
                  ⟨fun h => absurd h hne123, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h01⟩
                  ⟨fun h => absurd h hng10, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h02⟩
                  ⟨fun h => absurd h hng20, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h03⟩
                  ⟨fun h => absurd h hng30, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h12⟩
                  ⟨fun h => absurd h hng21, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h13⟩
                  ⟨fun h => absurd h hng31, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h23⟩
                  ⟨fun _ => by linarith, fun _ => h32⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd31⟩
                  ⟨fun _ => by linarith, fun _ => hd30⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd29⟩
                  ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd41⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd27, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd25⟩
                  ⟨fun h => absurd h hd28, fun h => by linarith⟩)
        · -- h23_1=F (1 pat)
          have hd42 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
            fun h => h23_1_hyp (sys.trans _ _ _ h h01)
          by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
          · -- h0_123=T
            have hd43 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
                  show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                  show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
              exact hn3 h1
            have hd44 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
                  show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                  show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
              exact hn2 h1
            exact absurd h12_0_hyp hd43
          · -- h0_123=F
            have hd45 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_123_hyp)
            exact fin4_witness sys (19/42) (5/14) (2/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (19/42) (5/14) (2/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd31⟩
                ⟨fun _ => by linarith, fun _ => hd30⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd29⟩
                ⟨fun h => absurd h hd42, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd45⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
      · -- h0_12=F (2 pat)
        have hd46 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h32
          exact h0_12_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd47 := nge_superset sys
          (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
        have hd48 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd47)
        by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
        · -- h23_1=T (1 pat)
          by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
          · -- h23_0=T
            have hd49 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
            have hd50 : sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) := by
              have h1 : sys.ge ({1,3} : Set (Fin 4)) ({0,3} : Set _) := by
                rw [sys.additive ({1,3} : Set (Fin 4)) {0,3},
                    show ({1,3} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact hd49
              have h2 : sys.ge ({0,3} : Set _) ({0,2} : Set _) := by
                rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
                    show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact h32
              exact sys.trans _ _ _ h1 h2
            have hd51 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := by
              have h1 : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                    show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact hd49
              have h2 : sys.ge ({0,2} : Set _) ({0,3} : Set _) := by
                rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                    show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact h23
              exact sys.trans _ _ _ h1 h2
            exact absurd hd49 hng10
          · -- h23_0=F
            exact fin4_witness sys (29/77) (24/77) (12/77) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (29/77) (24/77) (12/77) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd46, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd30⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd29⟩
                ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd47, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd48⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
        · -- h23_1=F (1 pat)
          have hd52 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
            fun h => h23_1_hyp (sys.trans _ _ _ h h01)
          exact fin4_witness sys (8/21) (1/3) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (8/21) (1/3) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              ⟨fun h => absurd h hn0, fun h => by linarith⟩
              ⟨fun h => absurd h hn1, fun h => by linarith⟩
              ⟨fun h => absurd h hn2, fun h => by linarith⟩
              ⟨fun h => absurd h hn3, fun h => by linarith⟩
              ⟨fun h => absurd h hne01, fun h => by linarith⟩
              ⟨fun h => absurd h hne02, fun h => by linarith⟩
              ⟨fun h => absurd h hne03, fun h => by linarith⟩
              ⟨fun h => absurd h hne12, fun h => by linarith⟩
              ⟨fun h => absurd h hne13, fun h => by linarith⟩
              ⟨fun h => absurd h hne23, fun h => by linarith⟩
              ⟨fun h => absurd h hne012, fun h => by linarith⟩
              ⟨fun h => absurd h hne013, fun h => by linarith⟩
              ⟨fun h => absurd h hne023, fun h => by linarith⟩
              ⟨fun h => absurd h hne123, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h hng10, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h02⟩
              ⟨fun h => absurd h hng20, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h03⟩
              ⟨fun h => absurd h hng30, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12⟩
              ⟨fun h => absurd h hng21, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h13⟩
              ⟨fun h => absurd h hng31, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h23⟩
              ⟨fun _ => by linarith, fun _ => h32⟩
              ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd46, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd30⟩
              ⟨fun h => absurd h hd12, fun h => by linarith⟩
              ⟨fun h => absurd h hd13, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
              ⟨fun h => absurd h hd14, fun h => by linarith⟩
              ⟨fun h => absurd h hd15, fun h => by linarith⟩
              ⟨fun h => absurd h hd16, fun h => by linarith⟩
              ⟨fun h => absurd h hd17, fun h => by linarith⟩
              ⟨fun h => absurd h hd18, fun h => by linarith⟩
              ⟨fun h => absurd h hd19, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
              ⟨fun _ => by linarith, fun _ => hd29⟩
              ⟨fun h => absurd h hd52, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd1⟩
              ⟨fun _ => by linarith, fun _ => hd2⟩
              ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd3⟩
              ⟨fun _ => by linarith, fun _ => hd4⟩
              ⟨fun _ => by linarith, fun _ => hd5⟩
              ⟨fun _ => by linarith, fun _ => hd6⟩
              ⟨fun _ => by linarith, fun _ => hd7⟩
              ⟨fun _ => by linarith, fun _ => hd8⟩
              ⟨fun h => absurd h hd47, fun h => by linarith⟩
              ⟨fun h => absurd h hd20, fun h => by linarith⟩
              ⟨fun h => absurd h hd21, fun h => by linarith⟩
              ⟨fun h => absurd h hd22, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd48⟩
              ⟨fun _ => by linarith, fun _ => hd9⟩
              ⟨fun _ => by linarith, fun _ => hd10⟩
              ⟨fun _ => by linarith, fun _ => hd11⟩
              ⟨fun _ => by linarith, fun _ => hd23⟩
              ⟨fun h => absurd h hd26, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd24⟩
              ⟨fun h => absurd h hd27, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd25⟩
              ⟨fun h => absurd h hd28, fun h => by linarith⟩)
    · -- h1_23=F (4 pat)
      have hd53 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
        (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
      by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
      · -- h23_0=T (2 pat)
        by_cases h0_23_hyp : sys.ge {(0 : Fin 4)} ({2,3} : Set _)
        · -- h0_23=T (1 pat)
          by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
          · -- h0_12=T
            have hd54 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
              have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
                rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact h23
              exact sys.trans _ _ _ h0_12_hyp h_mid
            exfalso
            have h_tr := sys.trans _ _ _ h23_0_hyp h0_12_hyp
            rw [sys.additive ({2,3} : Set (Fin 4)) {1,2},
                show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
            exact hng31 h_tr
          · -- h0_12=F
            have hd55 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
              have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
                rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                exact h32
              exact h0_12_hyp (sys.trans _ _ _ h_assumed h_mid)
            have hd56 := nge_superset sys
              (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
            have hd57 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd56)
            exact fin4_witness sys (8/21) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (8/21) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd55, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h0_23_hyp⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd29⟩
                ⟨fun _ => by linarith, fun _ => h23_0_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd53⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd56, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd57⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
        · -- h0_23=F (1 pat)
          have hd58 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
            have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({2,3} : Set _) := by
              rw [sys.additive ({1,2} : Set (Fin 4)) {2,3},
                  show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h13
            exact h0_23_hyp (sys.trans _ _ _ h_assumed h_mid)
          have hd59 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
            have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h32
            exact hd58 (sys.trans _ _ _ h_assumed h_mid)
          have hd60 := nge_superset sys
            (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd58
          have hd61 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
            (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd60)
          exact fin4_witness sys (13/42) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (13/42) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              ⟨fun h => absurd h hn0, fun h => by linarith⟩
              ⟨fun h => absurd h hn1, fun h => by linarith⟩
              ⟨fun h => absurd h hn2, fun h => by linarith⟩
              ⟨fun h => absurd h hn3, fun h => by linarith⟩
              ⟨fun h => absurd h hne01, fun h => by linarith⟩
              ⟨fun h => absurd h hne02, fun h => by linarith⟩
              ⟨fun h => absurd h hne03, fun h => by linarith⟩
              ⟨fun h => absurd h hne12, fun h => by linarith⟩
              ⟨fun h => absurd h hne13, fun h => by linarith⟩
              ⟨fun h => absurd h hne23, fun h => by linarith⟩
              ⟨fun h => absurd h hne012, fun h => by linarith⟩
              ⟨fun h => absurd h hne013, fun h => by linarith⟩
              ⟨fun h => absurd h hne023, fun h => by linarith⟩
              ⟨fun h => absurd h hne123, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h hng10, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h02⟩
              ⟨fun h => absurd h hng20, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h03⟩
              ⟨fun h => absurd h hng30, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12⟩
              ⟨fun h => absurd h hng21, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h13⟩
              ⟨fun h => absurd h hng31, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h23⟩
              ⟨fun _ => by linarith, fun _ => h32⟩
              ⟨fun h => absurd h hd58, fun h => by linarith⟩
              ⟨fun h => absurd h hd59, fun h => by linarith⟩
              ⟨fun h => absurd h h0_23_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd12, fun h => by linarith⟩
              ⟨fun h => absurd h hd13, fun h => by linarith⟩
              ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd14, fun h => by linarith⟩
              ⟨fun h => absurd h hd15, fun h => by linarith⟩
              ⟨fun h => absurd h hd16, fun h => by linarith⟩
              ⟨fun h => absurd h hd17, fun h => by linarith⟩
              ⟨fun h => absurd h hd18, fun h => by linarith⟩
              ⟨fun h => absurd h hd19, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
              ⟨fun _ => by linarith, fun _ => hd29⟩
              ⟨fun _ => by linarith, fun _ => h23_0_hyp⟩
              ⟨fun _ => by linarith, fun _ => hd1⟩
              ⟨fun _ => by linarith, fun _ => hd2⟩
              ⟨fun _ => by linarith, fun _ => hd53⟩
              ⟨fun _ => by linarith, fun _ => hd3⟩
              ⟨fun _ => by linarith, fun _ => hd4⟩
              ⟨fun _ => by linarith, fun _ => hd5⟩
              ⟨fun _ => by linarith, fun _ => hd6⟩
              ⟨fun _ => by linarith, fun _ => hd7⟩
              ⟨fun _ => by linarith, fun _ => hd8⟩
              ⟨fun h => absurd h hd60, fun h => by linarith⟩
              ⟨fun h => absurd h hd20, fun h => by linarith⟩
              ⟨fun h => absurd h hd21, fun h => by linarith⟩
              ⟨fun h => absurd h hd22, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd61⟩
              ⟨fun _ => by linarith, fun _ => hd9⟩
              ⟨fun _ => by linarith, fun _ => hd10⟩
              ⟨fun _ => by linarith, fun _ => hd11⟩
              ⟨fun _ => by linarith, fun _ => hd23⟩
              ⟨fun h => absurd h hd26, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd24⟩
              ⟨fun h => absurd h hd27, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd25⟩
              ⟨fun h => absurd h hd28, fun h => by linarith⟩)
      · -- h23_0=F (2 pat)
        have hd62 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) :=
          (sys.total {(0 : Fin 4)} ({2,3} : Set _)).elim id (fun h => absurd h h23_0_hyp)
        by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
        · -- h0_12=T (1 pat)
          have hd63 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
            have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
              rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h23
            exact sys.trans _ _ _ h0_12_hyp h_mid
          by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
          · -- h0_123=T
            have hd64 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
                  show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                  show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
              exact hn3 h1
            have hd65 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
                  show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                  show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
              exact hn2 h1
            exact absurd h12_0_hyp hd64
          · -- h0_123=F
            have hd66 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_123_hyp)
            exact fin4_witness sys (17/42) (3/14) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (17/42) (3/14) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd63⟩
                ⟨fun _ => by linarith, fun _ => hd62⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd29⟩
                ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd53⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd66⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
        · -- h0_12=F (1 pat)
          have hd67 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
            have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h32
            exact h0_12_hyp (sys.trans _ _ _ h_assumed h_mid)
          have hd68 := nge_superset sys
            (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
          have hd69 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
            (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd68)
          exact fin4_witness sys (5/14) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (5/14) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              ⟨fun h => absurd h hn0, fun h => by linarith⟩
              ⟨fun h => absurd h hn1, fun h => by linarith⟩
              ⟨fun h => absurd h hn2, fun h => by linarith⟩
              ⟨fun h => absurd h hn3, fun h => by linarith⟩
              ⟨fun h => absurd h hne01, fun h => by linarith⟩
              ⟨fun h => absurd h hne02, fun h => by linarith⟩
              ⟨fun h => absurd h hne03, fun h => by linarith⟩
              ⟨fun h => absurd h hne12, fun h => by linarith⟩
              ⟨fun h => absurd h hne13, fun h => by linarith⟩
              ⟨fun h => absurd h hne23, fun h => by linarith⟩
              ⟨fun h => absurd h hne012, fun h => by linarith⟩
              ⟨fun h => absurd h hne013, fun h => by linarith⟩
              ⟨fun h => absurd h hne023, fun h => by linarith⟩
              ⟨fun h => absurd h hne123, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h hng10, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h02⟩
              ⟨fun h => absurd h hng20, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h03⟩
              ⟨fun h => absurd h hng30, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12⟩
              ⟨fun h => absurd h hng21, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h13⟩
              ⟨fun h => absurd h hng31, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h23⟩
              ⟨fun _ => by linarith, fun _ => h32⟩
              ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd67, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd62⟩
              ⟨fun h => absurd h hd12, fun h => by linarith⟩
              ⟨fun h => absurd h hd13, fun h => by linarith⟩
              ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd14, fun h => by linarith⟩
              ⟨fun h => absurd h hd15, fun h => by linarith⟩
              ⟨fun h => absurd h hd16, fun h => by linarith⟩
              ⟨fun h => absurd h hd17, fun h => by linarith⟩
              ⟨fun h => absurd h hd18, fun h => by linarith⟩
              ⟨fun h => absurd h hd19, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
              ⟨fun _ => by linarith, fun _ => hd29⟩
              ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd1⟩
              ⟨fun _ => by linarith, fun _ => hd2⟩
              ⟨fun _ => by linarith, fun _ => hd53⟩
              ⟨fun _ => by linarith, fun _ => hd3⟩
              ⟨fun _ => by linarith, fun _ => hd4⟩
              ⟨fun _ => by linarith, fun _ => hd5⟩
              ⟨fun _ => by linarith, fun _ => hd6⟩
              ⟨fun _ => by linarith, fun _ => hd7⟩
              ⟨fun _ => by linarith, fun _ => hd8⟩
              ⟨fun h => absurd h hd68, fun h => by linarith⟩
              ⟨fun h => absurd h hd20, fun h => by linarith⟩
              ⟨fun h => absurd h hd21, fun h => by linarith⟩
              ⟨fun h => absurd h hd22, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd69⟩
              ⟨fun _ => by linarith, fun _ => hd9⟩
              ⟨fun _ => by linarith, fun _ => hd10⟩
              ⟨fun _ => by linarith, fun _ => hd11⟩
              ⟨fun _ => by linarith, fun _ => hd23⟩
              ⟨fun h => absurd h hd26, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd24⟩
              ⟨fun h => absurd h hd27, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd25⟩
              ⟨fun h => absurd h hd28, fun h => by linarith⟩)
  · -- h12_0=F (9 pat)
    have hd70 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
      have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
        rw [sys.additive ({1,2,3} : Set _) {0,2},
            show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
            show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
        exact h_assumed
      have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
        rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
            show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
            show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
        exact h23
      have h_s3 := sys.trans _ _ _ h_s1 h_s2
      rw [sys.additive ({1,2,3} : Set _) {0,3},
          show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
          show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
      exact h12_0_hyp h_s3
    have hd71 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
      have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
        rw [sys.additive ({1,2,3} : Set _) {0,1},
            show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
            show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
        exact h_assumed
      have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,3} : Set _) := by
        rw [sys.additive ({0,1} : Set (Fin 4)) {0,3},
            show ({0,1} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
            show ({0,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
        exact h13
      have h_s3 := sys.trans _ _ _ h_s1 h_s2
      rw [sys.additive ({1,2,3} : Set _) {0,3},
          show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
          show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
      exact h12_0_hyp h_s3
    have hd72 : sys.ge {(0 : Fin 4)} ({1,2} : Set _) :=
      (sys.total {(0 : Fin 4)} ({1,2} : Set _)).elim id (fun h => absurd h h12_0_hyp)
    have hd73 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) :=
      (sys.total {(0 : Fin 4)} ({1,3} : Set _)).elim id (fun h => absurd h hd70)
    have hd74 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) :=
      (sys.total {(0 : Fin 4)} ({2,3} : Set _)).elim id (fun h => absurd h hd71)
    by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
    · -- h0_123=T (6 pat)
      by_cases h123_0_hyp : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)
      · -- h123_0=T (3 pat)
        by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
        · -- h1_23=T (2 pat)
          by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
          · -- h23_1=T (1 pat)
            exact fin4_witness sys (1/2) (1/4) (1/8) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (1/2) (1/4) (1/8) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun _ => by linarith, fun _ => hd72⟩
                ⟨fun _ => by linarith, fun _ => hd73⟩
                ⟨fun _ => by linarith, fun _ => hd74⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd70, fun h => by linarith⟩
                ⟨fun h => absurd h hd71, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h123_0_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
          · -- h23_1=F (1 pat)
            exact fin4_witness sys (1/2) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (1/2) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun _ => by linarith, fun _ => hd72⟩
                ⟨fun _ => by linarith, fun _ => hd73⟩
                ⟨fun _ => by linarith, fun _ => hd74⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd70, fun h => by linarith⟩
                ⟨fun h => absurd h hd71, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h123_0_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
        · -- h1_23=F (1 pat)
          have hd75 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
            (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
          exact fin4_witness sys (1/2) (3/14) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (1/2) (3/14) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              ⟨fun h => absurd h hn0, fun h => by linarith⟩
              ⟨fun h => absurd h hn1, fun h => by linarith⟩
              ⟨fun h => absurd h hn2, fun h => by linarith⟩
              ⟨fun h => absurd h hn3, fun h => by linarith⟩
              ⟨fun h => absurd h hne01, fun h => by linarith⟩
              ⟨fun h => absurd h hne02, fun h => by linarith⟩
              ⟨fun h => absurd h hne03, fun h => by linarith⟩
              ⟨fun h => absurd h hne12, fun h => by linarith⟩
              ⟨fun h => absurd h hne13, fun h => by linarith⟩
              ⟨fun h => absurd h hne23, fun h => by linarith⟩
              ⟨fun h => absurd h hne012, fun h => by linarith⟩
              ⟨fun h => absurd h hne013, fun h => by linarith⟩
              ⟨fun h => absurd h hne023, fun h => by linarith⟩
              ⟨fun h => absurd h hne123, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h hng10, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h02⟩
              ⟨fun h => absurd h hng20, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h03⟩
              ⟨fun h => absurd h hng30, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12⟩
              ⟨fun h => absurd h hng21, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h13⟩
              ⟨fun h => absurd h hng31, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h23⟩
              ⟨fun _ => by linarith, fun _ => h32⟩
              ⟨fun _ => by linarith, fun _ => hd72⟩
              ⟨fun _ => by linarith, fun _ => hd73⟩
              ⟨fun _ => by linarith, fun _ => hd74⟩
              ⟨fun h => absurd h hd12, fun h => by linarith⟩
              ⟨fun h => absurd h hd13, fun h => by linarith⟩
              ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd14, fun h => by linarith⟩
              ⟨fun h => absurd h hd15, fun h => by linarith⟩
              ⟨fun h => absurd h hd16, fun h => by linarith⟩
              ⟨fun h => absurd h hd17, fun h => by linarith⟩
              ⟨fun h => absurd h hd18, fun h => by linarith⟩
              ⟨fun h => absurd h hd19, fun h => by linarith⟩
              ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd70, fun h => by linarith⟩
              ⟨fun h => absurd h hd71, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd1⟩
              ⟨fun _ => by linarith, fun _ => hd2⟩
              ⟨fun _ => by linarith, fun _ => hd75⟩
              ⟨fun _ => by linarith, fun _ => hd3⟩
              ⟨fun _ => by linarith, fun _ => hd4⟩
              ⟨fun _ => by linarith, fun _ => hd5⟩
              ⟨fun _ => by linarith, fun _ => hd6⟩
              ⟨fun _ => by linarith, fun _ => hd7⟩
              ⟨fun _ => by linarith, fun _ => hd8⟩
              ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
              ⟨fun h => absurd h hd20, fun h => by linarith⟩
              ⟨fun h => absurd h hd21, fun h => by linarith⟩
              ⟨fun h => absurd h hd22, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h123_0_hyp⟩
              ⟨fun _ => by linarith, fun _ => hd9⟩
              ⟨fun _ => by linarith, fun _ => hd10⟩
              ⟨fun _ => by linarith, fun _ => hd11⟩
              ⟨fun _ => by linarith, fun _ => hd23⟩
              ⟨fun h => absurd h hd26, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd24⟩
              ⟨fun h => absurd h hd27, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd25⟩
              ⟨fun h => absurd h hd28, fun h => by linarith⟩)
      · -- h123_0=F (3 pat)
        by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
        · -- h1_23=T (2 pat)
          by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
          · -- h23_1=T (1 pat)
            exact fin4_witness sys (11/21) (5/21) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (11/21) (5/21) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun _ => by linarith, fun _ => hd72⟩
                ⟨fun _ => by linarith, fun _ => hd73⟩
                ⟨fun _ => by linarith, fun _ => hd74⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd70, fun h => by linarith⟩
                ⟨fun h => absurd h hd71, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun h => absurd h h123_0_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
          · -- h23_1=F (1 pat)
            exact fin4_witness sys (11/21) (2/7) (2/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (11/21) (2/7) (2/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                ⟨fun h => absurd h hn0, fun h => by linarith⟩
                ⟨fun h => absurd h hn1, fun h => by linarith⟩
                ⟨fun h => absurd h hn2, fun h => by linarith⟩
                ⟨fun h => absurd h hn3, fun h => by linarith⟩
                ⟨fun h => absurd h hne01, fun h => by linarith⟩
                ⟨fun h => absurd h hne02, fun h => by linarith⟩
                ⟨fun h => absurd h hne03, fun h => by linarith⟩
                ⟨fun h => absurd h hne12, fun h => by linarith⟩
                ⟨fun h => absurd h hne13, fun h => by linarith⟩
                ⟨fun h => absurd h hne23, fun h => by linarith⟩
                ⟨fun h => absurd h hne012, fun h => by linarith⟩
                ⟨fun h => absurd h hne013, fun h => by linarith⟩
                ⟨fun h => absurd h hne023, fun h => by linarith⟩
                ⟨fun h => absurd h hne123, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => absurd h hng10, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => absurd h hng20, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03⟩
                ⟨fun h => absurd h hng30, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => absurd h hng21, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h13⟩
                ⟨fun h => absurd h hng31, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h23⟩
                ⟨fun _ => by linarith, fun _ => h32⟩
                ⟨fun _ => by linarith, fun _ => hd72⟩
                ⟨fun _ => by linarith, fun _ => hd73⟩
                ⟨fun _ => by linarith, fun _ => hd74⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd70, fun h => by linarith⟩
                ⟨fun h => absurd h hd71, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun h => absurd h h123_0_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd27, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd25⟩
                ⟨fun h => absurd h hd28, fun h => by linarith⟩)
        · -- h1_23=F (1 pat)
          have hd76 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
            (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
          exact fin4_witness sys (11/21) (4/21) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (11/21) (4/21) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              ⟨fun h => absurd h hn0, fun h => by linarith⟩
              ⟨fun h => absurd h hn1, fun h => by linarith⟩
              ⟨fun h => absurd h hn2, fun h => by linarith⟩
              ⟨fun h => absurd h hn3, fun h => by linarith⟩
              ⟨fun h => absurd h hne01, fun h => by linarith⟩
              ⟨fun h => absurd h hne02, fun h => by linarith⟩
              ⟨fun h => absurd h hne03, fun h => by linarith⟩
              ⟨fun h => absurd h hne12, fun h => by linarith⟩
              ⟨fun h => absurd h hne13, fun h => by linarith⟩
              ⟨fun h => absurd h hne23, fun h => by linarith⟩
              ⟨fun h => absurd h hne012, fun h => by linarith⟩
              ⟨fun h => absurd h hne013, fun h => by linarith⟩
              ⟨fun h => absurd h hne023, fun h => by linarith⟩
              ⟨fun h => absurd h hne123, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h hng10, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h02⟩
              ⟨fun h => absurd h hng20, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h03⟩
              ⟨fun h => absurd h hng30, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12⟩
              ⟨fun h => absurd h hng21, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h13⟩
              ⟨fun h => absurd h hng31, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h23⟩
              ⟨fun _ => by linarith, fun _ => h32⟩
              ⟨fun _ => by linarith, fun _ => hd72⟩
              ⟨fun _ => by linarith, fun _ => hd73⟩
              ⟨fun _ => by linarith, fun _ => hd74⟩
              ⟨fun h => absurd h hd12, fun h => by linarith⟩
              ⟨fun h => absurd h hd13, fun h => by linarith⟩
              ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd14, fun h => by linarith⟩
              ⟨fun h => absurd h hd15, fun h => by linarith⟩
              ⟨fun h => absurd h hd16, fun h => by linarith⟩
              ⟨fun h => absurd h hd17, fun h => by linarith⟩
              ⟨fun h => absurd h hd18, fun h => by linarith⟩
              ⟨fun h => absurd h hd19, fun h => by linarith⟩
              ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd70, fun h => by linarith⟩
              ⟨fun h => absurd h hd71, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd1⟩
              ⟨fun _ => by linarith, fun _ => hd2⟩
              ⟨fun _ => by linarith, fun _ => hd76⟩
              ⟨fun _ => by linarith, fun _ => hd3⟩
              ⟨fun _ => by linarith, fun _ => hd4⟩
              ⟨fun _ => by linarith, fun _ => hd5⟩
              ⟨fun _ => by linarith, fun _ => hd6⟩
              ⟨fun _ => by linarith, fun _ => hd7⟩
              ⟨fun _ => by linarith, fun _ => hd8⟩
              ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
              ⟨fun h => absurd h hd20, fun h => by linarith⟩
              ⟨fun h => absurd h hd21, fun h => by linarith⟩
              ⟨fun h => absurd h hd22, fun h => by linarith⟩
              ⟨fun h => absurd h h123_0_hyp, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd9⟩
              ⟨fun _ => by linarith, fun _ => hd10⟩
              ⟨fun _ => by linarith, fun _ => hd11⟩
              ⟨fun _ => by linarith, fun _ => hd23⟩
              ⟨fun h => absurd h hd26, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd24⟩
              ⟨fun h => absurd h hd27, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd25⟩
              ⟨fun h => absurd h hd28, fun h => by linarith⟩)
    · -- h0_123=F (3 pat)
      have hd77 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_123_hyp)
      by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
      · -- h1_23=T (2 pat)
        by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
        · -- h23_1=T (1 pat)
          exact fin4_witness sys (37/77) (20/77) (10/77) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (37/77) (20/77) (10/77) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              ⟨fun h => absurd h hn0, fun h => by linarith⟩
              ⟨fun h => absurd h hn1, fun h => by linarith⟩
              ⟨fun h => absurd h hn2, fun h => by linarith⟩
              ⟨fun h => absurd h hn3, fun h => by linarith⟩
              ⟨fun h => absurd h hne01, fun h => by linarith⟩
              ⟨fun h => absurd h hne02, fun h => by linarith⟩
              ⟨fun h => absurd h hne03, fun h => by linarith⟩
              ⟨fun h => absurd h hne12, fun h => by linarith⟩
              ⟨fun h => absurd h hne13, fun h => by linarith⟩
              ⟨fun h => absurd h hne23, fun h => by linarith⟩
              ⟨fun h => absurd h hne012, fun h => by linarith⟩
              ⟨fun h => absurd h hne013, fun h => by linarith⟩
              ⟨fun h => absurd h hne023, fun h => by linarith⟩
              ⟨fun h => absurd h hne123, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h hng10, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h02⟩
              ⟨fun h => absurd h hng20, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h03⟩
              ⟨fun h => absurd h hng30, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12⟩
              ⟨fun h => absurd h hng21, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h13⟩
              ⟨fun h => absurd h hng31, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h23⟩
              ⟨fun _ => by linarith, fun _ => h32⟩
              ⟨fun _ => by linarith, fun _ => hd72⟩
              ⟨fun _ => by linarith, fun _ => hd73⟩
              ⟨fun _ => by linarith, fun _ => hd74⟩
              ⟨fun h => absurd h hd12, fun h => by linarith⟩
              ⟨fun h => absurd h hd13, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
              ⟨fun h => absurd h hd14, fun h => by linarith⟩
              ⟨fun h => absurd h hd15, fun h => by linarith⟩
              ⟨fun h => absurd h hd16, fun h => by linarith⟩
              ⟨fun h => absurd h hd17, fun h => by linarith⟩
              ⟨fun h => absurd h hd18, fun h => by linarith⟩
              ⟨fun h => absurd h hd19, fun h => by linarith⟩
              ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd70, fun h => by linarith⟩
              ⟨fun h => absurd h hd71, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd1⟩
              ⟨fun _ => by linarith, fun _ => hd2⟩
              ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
              ⟨fun _ => by linarith, fun _ => hd3⟩
              ⟨fun _ => by linarith, fun _ => hd4⟩
              ⟨fun _ => by linarith, fun _ => hd5⟩
              ⟨fun _ => by linarith, fun _ => hd6⟩
              ⟨fun _ => by linarith, fun _ => hd7⟩
              ⟨fun _ => by linarith, fun _ => hd8⟩
              ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd20, fun h => by linarith⟩
              ⟨fun h => absurd h hd21, fun h => by linarith⟩
              ⟨fun h => absurd h hd22, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd77⟩
              ⟨fun _ => by linarith, fun _ => hd9⟩
              ⟨fun _ => by linarith, fun _ => hd10⟩
              ⟨fun _ => by linarith, fun _ => hd11⟩
              ⟨fun _ => by linarith, fun _ => hd23⟩
              ⟨fun h => absurd h hd26, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd24⟩
              ⟨fun h => absurd h hd27, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd25⟩
              ⟨fun h => absurd h hd28, fun h => by linarith⟩)
        · -- h23_1=F (1 pat)
          exact fin4_witness sys (19/42) (13/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (19/42) (13/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              ⟨fun h => absurd h hn0, fun h => by linarith⟩
              ⟨fun h => absurd h hn1, fun h => by linarith⟩
              ⟨fun h => absurd h hn2, fun h => by linarith⟩
              ⟨fun h => absurd h hn3, fun h => by linarith⟩
              ⟨fun h => absurd h hne01, fun h => by linarith⟩
              ⟨fun h => absurd h hne02, fun h => by linarith⟩
              ⟨fun h => absurd h hne03, fun h => by linarith⟩
              ⟨fun h => absurd h hne12, fun h => by linarith⟩
              ⟨fun h => absurd h hne13, fun h => by linarith⟩
              ⟨fun h => absurd h hne23, fun h => by linarith⟩
              ⟨fun h => absurd h hne012, fun h => by linarith⟩
              ⟨fun h => absurd h hne013, fun h => by linarith⟩
              ⟨fun h => absurd h hne023, fun h => by linarith⟩
              ⟨fun h => absurd h hne123, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h hng10, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h02⟩
              ⟨fun h => absurd h hng20, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h03⟩
              ⟨fun h => absurd h hng30, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h12⟩
              ⟨fun h => absurd h hng21, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h13⟩
              ⟨fun h => absurd h hng31, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h23⟩
              ⟨fun _ => by linarith, fun _ => h32⟩
              ⟨fun _ => by linarith, fun _ => hd72⟩
              ⟨fun _ => by linarith, fun _ => hd73⟩
              ⟨fun _ => by linarith, fun _ => hd74⟩
              ⟨fun h => absurd h hd12, fun h => by linarith⟩
              ⟨fun h => absurd h hd13, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
              ⟨fun h => absurd h hd14, fun h => by linarith⟩
              ⟨fun h => absurd h hd15, fun h => by linarith⟩
              ⟨fun h => absurd h hd16, fun h => by linarith⟩
              ⟨fun h => absurd h hd17, fun h => by linarith⟩
              ⟨fun h => absurd h hd18, fun h => by linarith⟩
              ⟨fun h => absurd h hd19, fun h => by linarith⟩
              ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd70, fun h => by linarith⟩
              ⟨fun h => absurd h hd71, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd1⟩
              ⟨fun _ => by linarith, fun _ => hd2⟩
              ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd3⟩
              ⟨fun _ => by linarith, fun _ => hd4⟩
              ⟨fun _ => by linarith, fun _ => hd5⟩
              ⟨fun _ => by linarith, fun _ => hd6⟩
              ⟨fun _ => by linarith, fun _ => hd7⟩
              ⟨fun _ => by linarith, fun _ => hd8⟩
              ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
              ⟨fun h => absurd h hd20, fun h => by linarith⟩
              ⟨fun h => absurd h hd21, fun h => by linarith⟩
              ⟨fun h => absurd h hd22, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd77⟩
              ⟨fun _ => by linarith, fun _ => hd9⟩
              ⟨fun _ => by linarith, fun _ => hd10⟩
              ⟨fun _ => by linarith, fun _ => hd11⟩
              ⟨fun _ => by linarith, fun _ => hd23⟩
              ⟨fun h => absurd h hd26, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd24⟩
              ⟨fun h => absurd h hd27, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hd25⟩
              ⟨fun h => absurd h hd28, fun h => by linarith⟩)
      · -- h1_23=F (1 pat)
        have hd78 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
          (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
        exact fin4_witness sys (3/7) (5/21) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
          hn0 hn1 hn2 hn3
          (fin4_dispatch sys (3/7) (5/21) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
            (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
            (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
            (mf4_univ ..)
            ⟨fun h => absurd h hn0, fun h => by linarith⟩
            ⟨fun h => absurd h hn1, fun h => by linarith⟩
            ⟨fun h => absurd h hn2, fun h => by linarith⟩
            ⟨fun h => absurd h hn3, fun h => by linarith⟩
            ⟨fun h => absurd h hne01, fun h => by linarith⟩
            ⟨fun h => absurd h hne02, fun h => by linarith⟩
            ⟨fun h => absurd h hne03, fun h => by linarith⟩
            ⟨fun h => absurd h hne12, fun h => by linarith⟩
            ⟨fun h => absurd h hne13, fun h => by linarith⟩
            ⟨fun h => absurd h hne23, fun h => by linarith⟩
            ⟨fun h => absurd h hne012, fun h => by linarith⟩
            ⟨fun h => absurd h hne013, fun h => by linarith⟩
            ⟨fun h => absurd h hne023, fun h => by linarith⟩
            ⟨fun h => absurd h hne123, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h01⟩
            ⟨fun h => absurd h hng10, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h02⟩
            ⟨fun h => absurd h hng20, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h03⟩
            ⟨fun h => absurd h hng30, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h12⟩
            ⟨fun h => absurd h hng21, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h13⟩
            ⟨fun h => absurd h hng31, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h23⟩
            ⟨fun _ => by linarith, fun _ => h32⟩
            ⟨fun _ => by linarith, fun _ => hd72⟩
            ⟨fun _ => by linarith, fun _ => hd73⟩
            ⟨fun _ => by linarith, fun _ => hd74⟩
            ⟨fun h => absurd h hd12, fun h => by linarith⟩
            ⟨fun h => absurd h hd13, fun h => by linarith⟩
            ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
            ⟨fun h => absurd h hd14, fun h => by linarith⟩
            ⟨fun h => absurd h hd15, fun h => by linarith⟩
            ⟨fun h => absurd h hd16, fun h => by linarith⟩
            ⟨fun h => absurd h hd17, fun h => by linarith⟩
            ⟨fun h => absurd h hd18, fun h => by linarith⟩
            ⟨fun h => absurd h hd19, fun h => by linarith⟩
            ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
            ⟨fun h => absurd h hd70, fun h => by linarith⟩
            ⟨fun h => absurd h hd71, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd1⟩
            ⟨fun _ => by linarith, fun _ => hd2⟩
            ⟨fun _ => by linarith, fun _ => hd78⟩
            ⟨fun _ => by linarith, fun _ => hd3⟩
            ⟨fun _ => by linarith, fun _ => hd4⟩
            ⟨fun _ => by linarith, fun _ => hd5⟩
            ⟨fun _ => by linarith, fun _ => hd6⟩
            ⟨fun _ => by linarith, fun _ => hd7⟩
            ⟨fun _ => by linarith, fun _ => hd8⟩
            ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
            ⟨fun h => absurd h hd20, fun h => by linarith⟩
            ⟨fun h => absurd h hd21, fun h => by linarith⟩
            ⟨fun h => absurd h hd22, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd77⟩
            ⟨fun _ => by linarith, fun _ => hd9⟩
            ⟨fun _ => by linarith, fun _ => hd10⟩
            ⟨fun _ => by linarith, fun _ => hd11⟩
            ⟨fun _ => by linarith, fun _ => hd23⟩
            ⟨fun h => absurd h hd26, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd24⟩
            ⟨fun h => absurd h hd27, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd25⟩
            ⟨fun h => absurd h hd28, fun h => by linarith⟩)


end Core.Scale
