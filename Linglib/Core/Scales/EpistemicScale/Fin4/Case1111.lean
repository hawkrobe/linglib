import Linglib.Core.Scales.EpistemicScale.Fin4.Defs

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000 in
/-- Case (1,1,1,1): 45 sub-cases. -/
theorem fin4_case_1111 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (hng10 : ¬sys.ge {(1 : Fin 4)} {0})
    (h12 : sys.ge {(1 : Fin 4)} {2})
    (hng21 : ¬sys.ge {(2 : Fin 4)} {1})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (hng32 : ¬sys.ge {(3 : Fin 4)} {2})
    (h02 : sys.ge {(0 : Fin 4)} {2})
    (h13 : sys.ge {(1 : Fin 4)} {3})
    (h03 : sys.ge {(0 : Fin 4)} {3})
    :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  have hng20 : ¬sys.ge {(2 : Fin 4)} {0} := fun h => hng21 (sys.trans _ _ _ h h01)
  have hng31 : ¬sys.ge {(3 : Fin 4)} {1} := fun h => hng32 (sys.trans _ _ _ h h12)
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
  have hd25 : ¬sys.ge ({2,3} : Set (Fin 4)) ({0,1} : Set _) := fun h => by
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
  have hd26 : ¬sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) := fun h => by
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
  by_cases h12_03_hyp : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _)
  · -- h12_03=T (22 pat)
    by_cases h03_12_hyp : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _)
    · -- h03_12=T (11 pat)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (6 pat)
        have hd27 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (3 pat)
          have hd28 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h13_0_hyp
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                  show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h23
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,3},
                show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
            exact h_s3
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                exfalso
                have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
                rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hn3 h_tr
              · -- h0_12=F
                have hd29 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd30 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd29)
                by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
                · -- h23_0=T
                  have hd31 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
                  have hd32 := nge_singleton_pair sys hd31 hn3
                    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
                    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
                  have hd33 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := fun h => by
                    have h_bc : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                      rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                          show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                          show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                      exact hd31
                    have h1 := sys.trans _ _ _ h h_bc
                    rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
                        show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                        show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
                    exact hng32 h1
                  exact absurd h03_12_hyp hd33
                · -- h23_0=F
                  exact fin4_witness sys (2/5) (3/10) (1/5) (by linarith) (by linarith) (by linarith) (by linarith)
                    hn0 hn1 hn2 hn3
                    (fin4_dispatch sys (2/5) (3/10) (1/5) (by linarith) (by linarith) (by linarith) (by linarith)
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
                      ⟨fun h => absurd h hng32, fun h => by linarith⟩
                      ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                      ⟨fun _ => by linarith, fun _ => hd27⟩
                      ⟨fun h => absurd h hd12, fun h => by linarith⟩
                      ⟨fun h => absurd h hd13, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                      ⟨fun h => absurd h hd14, fun h => by linarith⟩
                      ⟨fun h => absurd h hd15, fun h => by linarith⟩
                      ⟨fun h => absurd h hd16, fun h => by linarith⟩
                      ⟨fun h => absurd h hd17, fun h => by linarith⟩
                      ⟨fun h => absurd h hd18, fun h => by linarith⟩
                      ⟨fun h => absurd h hd19, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hd28⟩
                      ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
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
                      ⟨fun h => absurd h hd29, fun h => by linarith⟩
                      ⟨fun h => absurd h hd20, fun h => by linarith⟩
                      ⟨fun h => absurd h hd21, fun h => by linarith⟩
                      ⟨fun h => absurd h hd22, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hd30⟩
                      ⟨fun _ => by linarith, fun _ => hd9⟩
                      ⟨fun _ => by linarith, fun _ => hd10⟩
                      ⟨fun _ => by linarith, fun _ => hd11⟩
                      ⟨fun _ => by linarith, fun _ => hd23⟩
                      ⟨fun h => absurd h hd25, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hd24⟩
                      ⟨fun h => absurd h hd26, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                      ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
            · -- h23_1=F (1 pat)
              have hd34 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                fun h => h23_1_hyp (sys.trans _ _ _ h h01)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                exfalso
                have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
                rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hn3 h_tr
              · -- h0_12=F
                have hd35 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd36 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd35)
                exact fin4_witness sys (17/42) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (17/42) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd27⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd28⟩
                    ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
                    ⟨fun h => absurd h hd34, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd35, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd36⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h1_23=F (1 pat)
            have hd37 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
            · -- h0_12=T
              exfalso
              have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
              rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                  show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                  show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
              exact hn3 h_tr
            · -- h0_12=F
              have hd38 := nge_superset sys
                (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
              have hd39 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd38)
              by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
              · -- h23_0=T
                exfalso
                have h_tr := sys.trans _ _ _ h23_0_hyp h0_13_hyp
                rw [sys.additive ({2,3} : Set (Fin 4)) {1,3},
                    show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hng21 h_tr
              · -- h23_0=F
                exact fin4_witness sys (8/21) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (8/21) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd27⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd28⟩
                    ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
                    ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun _ => by linarith, fun _ => hd37⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd38, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd39⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
        · -- h13_0=F (3 pat)
          have hd40 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h_assumed
            have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
              rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h12
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,2},
                show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
            exact h13_0_hyp h_s3
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                exfalso
                have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
                rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hn3 h_tr
              · -- h0_12=F
                have hd41 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd42 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
                have hd43 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd41)
                exact fin4_witness sys (3/7) (2/7) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (3/7) (2/7) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd27⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd42⟩
                    ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                    ⟨fun h => absurd h hd40, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd41, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd43⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
            · -- h23_1=F (1 pat)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                exfalso
                have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
                rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hn3 h_tr
              · -- h0_12=F
                have hd44 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd45 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
                have hd46 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd44)
                exact fin4_witness sys (3/7) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (3/7) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd27⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd45⟩
                    ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                    ⟨fun h => absurd h hd40, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd44, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd46⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h1_23=F (1 pat)
            have hd47 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
            · -- h0_12=T
              exfalso
              have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
              rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                  show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by ext x; fin_cases x <;> simp_all,
                  show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
              exact hn3 h_tr
            · -- h0_12=F
              have hd48 := nge_superset sys
                (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
              have hd49 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
              have hd50 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd48)
              exact fin4_witness sys (17/42) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (17/42) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd27⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd49⟩
                  ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd40, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd47⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd48, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd50⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
      · -- h0_13=F (5 pat)
        have hd51 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h23
          exact h0_13_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd52 := nge_superset sys
          (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd51
        have hd53 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd51)
        have hd54 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_13_hyp)
        have hd55 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd52)
        by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
        · -- h1_23=T (2 pat)
          have hd56 := sys.trans _ _ _ h01 h1_23_hyp
          by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
          · -- h23_1=T (1 pat)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T
              have hd57 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
              have hd58 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := fun h => by
                have h_bc : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                  rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                      show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                      show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                  exact hd57
                have h1 := sys.trans _ _ _ h h_bc
                rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
                    show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
                exact hng32 h1
              exact absurd h03_12_hyp hd58
            · -- h23_0=F
              exact fin4_witness sys (8/21) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (8/21) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h hd51, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd56⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd53⟩
                  ⟨fun _ => by linarith, fun _ => hd54⟩
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
                  ⟨fun h => absurd h hd52, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd55⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h23_1=F (1 pat)
            have hd59 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              fun h => h23_1_hyp (sys.trans _ _ _ h h01)
            exact fin4_witness sys (5/14) (1/3) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (5/14) (1/3) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun h => absurd h hd51, fun h => by linarith⟩
                ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd56⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd53⟩
                ⟨fun _ => by linarith, fun _ => hd54⟩
                ⟨fun h => absurd h hd59, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd52, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd55⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
        · -- h1_23=F (3 pat)
          have hd60 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
            (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
          by_cases h0_23_hyp : sys.ge {(0 : Fin 4)} ({2,3} : Set _)
          · -- h0_23=T (2 pat)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T (1 pat)
              exact fin4_witness sys (5/14) (2/7) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (5/14) (2/7) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h hd51, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd53⟩
                  ⟨fun _ => by linarith, fun _ => hd54⟩
                  ⟨fun _ => by linarith, fun _ => h23_0_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd60⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd52, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd55⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
            · -- h23_0=F (1 pat)
              exact fin4_witness sys (5/14) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (5/14) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h hd51, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd53⟩
                  ⟨fun _ => by linarith, fun _ => hd54⟩
                  ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd60⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd52, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd55⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h0_23=F (1 pat)
            have hd61 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_23_hyp)
            exact fin4_witness sys (2/7) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (2/7) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun h => absurd h hd51, fun h => by linarith⟩
                ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                ⟨fun _ => by linarith, fun _ => hd53⟩
                ⟨fun _ => by linarith, fun _ => hd54⟩
                ⟨fun _ => by linarith, fun _ => hd61⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd60⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd52, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd55⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h03_12_hyp⟩
                ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
    · -- h03_12=F (11 pat)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (6 pat)
        have hd62 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (3 pat)
          have hd63 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h13_0_hyp
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                  show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h23
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,3},
                show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
            exact h_s3
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                have hd64 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                  sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
                exact absurd hd64 h03_12_hyp
              · -- h0_12=F
                have hd65 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd66 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd65)
                by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
                · -- h23_0=T
                  have hd67 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
                  have hd68 := nge_singleton_pair sys hd67 hn3
                    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
                    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
                  exact absurd h0_13_hyp hd68
                · -- h23_0=F
                  exact fin4_witness sys (8/21) (13/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
                    hn0 hn1 hn2 hn3
                    (fin4_dispatch sys (8/21) (13/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                      ⟨fun h => absurd h hng32, fun h => by linarith⟩
                      ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                      ⟨fun _ => by linarith, fun _ => hd62⟩
                      ⟨fun h => absurd h hd12, fun h => by linarith⟩
                      ⟨fun h => absurd h hd13, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                      ⟨fun h => absurd h hd14, fun h => by linarith⟩
                      ⟨fun h => absurd h hd15, fun h => by linarith⟩
                      ⟨fun h => absurd h hd16, fun h => by linarith⟩
                      ⟨fun h => absurd h hd17, fun h => by linarith⟩
                      ⟨fun h => absurd h hd18, fun h => by linarith⟩
                      ⟨fun h => absurd h hd19, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hd63⟩
                      ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
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
                      ⟨fun h => absurd h hd65, fun h => by linarith⟩
                      ⟨fun h => absurd h hd20, fun h => by linarith⟩
                      ⟨fun h => absurd h hd21, fun h => by linarith⟩
                      ⟨fun h => absurd h hd22, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hd66⟩
                      ⟨fun _ => by linarith, fun _ => hd9⟩
                      ⟨fun _ => by linarith, fun _ => hd10⟩
                      ⟨fun _ => by linarith, fun _ => hd11⟩
                      ⟨fun _ => by linarith, fun _ => hd23⟩
                      ⟨fun h => absurd h hd25, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hd24⟩
                      ⟨fun h => absurd h hd26, fun h => by linarith⟩
                      ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
            · -- h23_1=F (1 pat)
              have hd69 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                fun h => h23_1_hyp (sys.trans _ _ _ h h01)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                have hd70 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                  sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
                exact absurd hd70 h03_12_hyp
              · -- h0_12=F
                have hd71 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd72 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd71)
                exact fin4_witness sys (5/14) (1/3) (2/7) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (5/14) (1/3) (2/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd62⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd63⟩
                    ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
                    ⟨fun h => absurd h hd69, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd71, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd72⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h1_23=F (1 pat)
            have hd73 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
            · -- h0_12=T
              have hd74 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
              exact absurd hd74 h03_12_hyp
            · -- h0_12=F
              have hd75 := nge_superset sys
                (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
              have hd76 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd75)
              by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
              · -- h23_0=T
                exfalso
                have h_tr := sys.trans _ _ _ h23_0_hyp h0_13_hyp
                rw [sys.additive ({2,3} : Set (Fin 4)) {1,3},
                    show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hng21 h_tr
              · -- h23_0=F
                exact fin4_witness sys (5/14) (13/42) (2/7) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (5/14) (13/42) (2/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
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
                    ⟨fun _ => by linarith, fun _ => hd63⟩
                    ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
                    ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun _ => by linarith, fun _ => hd73⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd75, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd76⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
        · -- h13_0=F (3 pat)
          have hd77 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h_assumed
            have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
              rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h12
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,2},
                show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
            exact h13_0_hyp h_s3
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                have hd78 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                  sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
                exact absurd hd78 h03_12_hyp
              · -- h0_12=F
                have hd79 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd80 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
                have hd81 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd79)
                exact fin4_witness sys (8/21) (13/42) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (8/21) (13/42) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd62⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd80⟩
                    ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                    ⟨fun h => absurd h hd77, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd79, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd81⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
            · -- h23_1=F (1 pat)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                have hd82 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                  sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
                exact absurd hd82 h03_12_hyp
              · -- h0_12=F
                have hd83 := nge_superset sys
                  (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
                have hd84 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
                have hd85 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                  (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd83)
                exact fin4_witness sys (8/21) (1/3) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (8/21) (1/3) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd62⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd84⟩
                    ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                    ⟨fun h => absurd h hd77, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd1⟩
                    ⟨fun _ => by linarith, fun _ => hd2⟩
                    ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd3⟩
                    ⟨fun _ => by linarith, fun _ => hd4⟩
                    ⟨fun _ => by linarith, fun _ => hd5⟩
                    ⟨fun _ => by linarith, fun _ => hd6⟩
                    ⟨fun _ => by linarith, fun _ => hd7⟩
                    ⟨fun _ => by linarith, fun _ => hd8⟩
                    ⟨fun h => absurd h hd83, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd85⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h1_23=F (1 pat)
            have hd86 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
            · -- h0_12=T
              have hd87 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
              exact absurd hd87 h03_12_hyp
            · -- h0_12=F
              have hd88 := nge_superset sys
                (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
              have hd89 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
              have hd90 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
                (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd88)
              exact fin4_witness sys (8/21) (2/7) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (8/21) (2/7) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
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
                  ⟨fun _ => by linarith, fun _ => hd89⟩
                  ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd77, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd86⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd88, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd90⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
      · -- h0_13=F (5 pat)
        have hd91 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h23
          exact h0_13_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd92 := nge_superset sys
          (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd91
        have hd93 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd91)
        have hd94 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_13_hyp)
        have hd95 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd92)
        by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
        · -- h1_23=T (2 pat)
          have hd96 := sys.trans _ _ _ h01 h1_23_hyp
          by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
          · -- h23_1=T (1 pat)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T
              have hd97 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
              exact absurd hd97 hng10
            · -- h23_0=F
              exact fin4_witness sys (8/21) (13/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (8/21) (13/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h hd91, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd96⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd93⟩
                  ⟨fun _ => by linarith, fun _ => hd94⟩
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
                  ⟨fun h => absurd h hd92, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd95⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h23_1=F (1 pat)
            have hd98 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              fun h => h23_1_hyp (sys.trans _ _ _ h h01)
            exact fin4_witness sys (5/14) (1/3) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (5/14) (1/3) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun h => absurd h hd91, fun h => by linarith⟩
                ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd96⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd93⟩
                ⟨fun _ => by linarith, fun _ => hd94⟩
                ⟨fun h => absurd h hd98, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd92, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd95⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
        · -- h1_23=F (3 pat)
          have hd99 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
            (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
          by_cases h0_23_hyp : sys.ge {(0 : Fin 4)} ({2,3} : Set _)
          · -- h0_23=T (2 pat)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T (1 pat)
              exact fin4_witness sys (5/14) (2/7) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (5/14) (2/7) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h hd91, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd93⟩
                  ⟨fun _ => by linarith, fun _ => hd94⟩
                  ⟨fun _ => by linarith, fun _ => h23_0_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd99⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd92, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd95⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
            · -- h23_0=F (1 pat)
              exact fin4_witness sys (5/14) (13/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (5/14) (13/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h hd91, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd93⟩
                  ⟨fun _ => by linarith, fun _ => hd94⟩
                  ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd99⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd92, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd95⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
          · -- h0_23=F (1 pat)
            have hd100 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_23_hyp)
            exact fin4_witness sys (13/42) (2/7) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (13/42) (2/7) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun h => absurd h hd91, fun h => by linarith⟩
                ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                ⟨fun _ => by linarith, fun _ => hd93⟩
                ⟨fun _ => by linarith, fun _ => hd94⟩
                ⟨fun _ => by linarith, fun _ => hd100⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd99⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd92, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd95⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun h => absurd h h03_12_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h12_03_hyp⟩)
  · -- h12_03=F (23 pat)
    have hd101 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
      (sys.total ({0,3} : Set (Fin 4)) ({1,2} : Set _)).elim id (fun h => absurd h h12_03_hyp)
    by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
    · -- h0_12=T (12 pat)
      have hd102 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
              show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
              show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
          exact h23
        exact sys.trans _ _ _ h0_12_hyp h_mid
      have hd103 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({2,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {2,3},
              show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
              show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
          exact h13
        exact sys.trans _ _ _ h0_12_hyp h_mid
      by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
      · -- h0_123=T (6 pat)
        have hd104 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
              show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
              show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
          exact hn3 h1
        have hd105 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
              show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
              show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
          exact hn2 h1
        have hd106 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({2,3} : Set (Fin 4)) {1,2,3},
              show ({2,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
              show ({1,2,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
          exact hn1 h1
        by_cases h123_0_hyp : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)
        · -- h123_0=T (3 pat)
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              exact fin4_witness sys (1/2) (1/4) (11/84) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (1/2) (1/4) (11/84) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd102⟩
                  ⟨fun _ => by linarith, fun _ => hd103⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun h => absurd h hd104, fun h => by linarith⟩
                  ⟨fun h => absurd h hd105, fun h => by linarith⟩
                  ⟨fun h => absurd h hd106, fun h => by linarith⟩
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
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (1/2) (11/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (1/2) (11/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd102⟩
                  ⟨fun _ => by linarith, fun _ => hd103⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun h => absurd h hd104, fun h => by linarith⟩
                  ⟨fun h => absurd h hd105, fun h => by linarith⟩
                  ⟨fun h => absurd h hd106, fun h => by linarith⟩
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
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h1_23=F (1 pat)
            have hd107 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            exact fin4_witness sys (1/2) (4/21) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (1/2) (4/21) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd102⟩
                ⟨fun _ => by linarith, fun _ => hd103⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun h => absurd h hd104, fun h => by linarith⟩
                ⟨fun h => absurd h hd105, fun h => by linarith⟩
                ⟨fun h => absurd h hd106, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd107⟩
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
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd101⟩
                ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
        · -- h123_0=F (3 pat)
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              exact fin4_witness sys (11/21) (5/21) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (11/21) (5/21) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd102⟩
                  ⟨fun _ => by linarith, fun _ => hd103⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun h => absurd h hd104, fun h => by linarith⟩
                  ⟨fun h => absurd h hd105, fun h => by linarith⟩
                  ⟨fun h => absurd h hd106, fun h => by linarith⟩
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
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (11/21) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (11/21) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd102⟩
                  ⟨fun _ => by linarith, fun _ => hd103⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun h => absurd h hd104, fun h => by linarith⟩
                  ⟨fun h => absurd h hd105, fun h => by linarith⟩
                  ⟨fun h => absurd h hd106, fun h => by linarith⟩
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
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h1_23=F (1 pat)
            have hd108 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            exact fin4_witness sys (11/21) (4/21) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (11/21) (4/21) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd102⟩
                ⟨fun _ => by linarith, fun _ => hd103⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun h => absurd h hd104, fun h => by linarith⟩
                ⟨fun h => absurd h hd105, fun h => by linarith⟩
                ⟨fun h => absurd h hd106, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd108⟩
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
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd101⟩
                ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
      · -- h0_123=F (6 pat)
        have hd109 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_123_hyp)
        by_cases h12_0_hyp : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h12_0=T (3 pat)
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
              · -- h13_0=T
                exfalso
                have h_tr := sys.trans _ _ _ h13_0_hyp h0_12_hyp
                rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hng32 h_tr
              · -- h13_0=F
                have hd110 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
                  have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
                    rw [sys.additive ({1,2,3} : Set _) {0,1},
                        show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                        show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                    exact h_assumed
                  have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
                    rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                        show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                        show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                    exact h12
                  have h_s3 := sys.trans _ _ _ h_s1 h_s2
                  rw [sys.additive ({1,2,3} : Set _) {0,2},
                      show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                      show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
                  exact h13_0_hyp h_s3
                exact fin4_witness sys (10/21) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (10/21) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd102⟩
                    ⟨fun _ => by linarith, fun _ => hd103⟩
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
                    ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                    ⟨fun h => absurd h hd110, fun h => by linarith⟩
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
                    ⟨fun _ => by linarith, fun _ => hd109⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd101⟩
                    ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
            · -- h23_1=F (1 pat)
              have hd111 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                fun h => h23_1_hyp (sys.trans _ _ _ h h01)
              by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
              · -- h13_0=T
                exfalso
                have h_tr := sys.trans _ _ _ h13_0_hyp h0_12_hyp
                rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
                exact hng32 h_tr
              · -- h13_0=F
                exact fin4_witness sys (19/42) (2/7) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (19/42) (2/7) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd102⟩
                    ⟨fun _ => by linarith, fun _ => hd103⟩
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
                    ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                    ⟨fun h => absurd h hd111, fun h => by linarith⟩
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
                    ⟨fun _ => by linarith, fun _ => hd109⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd101⟩
                    ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h1_23=F (1 pat)
            have hd112 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h13_0=T
              exfalso
              have h_tr := sys.trans _ _ _ h13_0_hyp h0_12_hyp
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
              exact hng32 h_tr
            · -- h13_0=F
              have hd113 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
                have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
                  rw [sys.additive ({1,2,3} : Set _) {0,1},
                      show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                      show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                  exact h_assumed
                have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
                  rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                      show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                      show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                  exact h12
                have h_s3 := sys.trans _ _ _ h_s1 h_s2
                rw [sys.additive ({1,2,3} : Set _) {0,2},
                    show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                    show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
                exact h13_0_hyp h_s3
              exact fin4_witness sys (3/7) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (3/7) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd102⟩
                  ⟨fun _ => by linarith, fun _ => hd103⟩
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
                  ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd113, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd112⟩
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
                  ⟨fun _ => by linarith, fun _ => hd109⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
        · -- h12_0=F (3 pat)
          have hd114 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
          have hd115 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              exact fin4_witness sys (10/21) (11/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (10/21) (11/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd102⟩
                  ⟨fun _ => by linarith, fun _ => hd103⟩
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
                  ⟨fun h => absurd h hd114, fun h => by linarith⟩
                  ⟨fun h => absurd h hd115, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd109⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (19/42) (2/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (19/42) (2/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd102⟩
                  ⟨fun _ => by linarith, fun _ => hd103⟩
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
                  ⟨fun h => absurd h hd114, fun h => by linarith⟩
                  ⟨fun h => absurd h hd115, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd109⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h1_23=F (1 pat)
            have hd116 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            exact fin4_witness sys (3/7) (3/14) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (3/7) (3/14) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd102⟩
                ⟨fun _ => by linarith, fun _ => hd103⟩
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
                ⟨fun h => absurd h hd114, fun h => by linarith⟩
                ⟨fun h => absurd h hd115, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd116⟩
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
                ⟨fun _ => by linarith, fun _ => hd109⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd101⟩
                ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
    · -- h0_12=F (11 pat)
      have hd117 := nge_superset sys
        (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
      have hd118 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
      have hd119 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd117)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (6 pat)
        have hd120 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (3 pat)
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
              · -- h23_0=T
                have hd121 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
                have hd122 := nge_singleton_pair sys hd121 hn3
                  (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
                  (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
                have hd123 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := by
                  have h1 : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                    rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                        show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                        show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                    exact hd121
                  have h2 : sys.ge ({0,2} : Set _) ({0,3} : Set _) := by
                    rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                        show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                        show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                    exact h23
                  exact sys.trans _ _ _ h1 h2
                have hd124 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := fun h => by
                  have h_bc : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                    rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                        show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                        show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                    exact hd121
                  have h1 := sys.trans _ _ _ h h_bc
                  rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
                      show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                      show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
                  exact hng32 h1
                exact absurd hd101 hd124
              · -- h23_0=F
                exact fin4_witness sys (31/77) (23/77) (15/77) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (31/77) (23/77) (15/77) (by linarith) (by linarith) (by linarith) (by linarith)
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
                    ⟨fun h => absurd h hng32, fun h => by linarith⟩
                    ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                    ⟨fun _ => by linarith, fun _ => hd120⟩
                    ⟨fun h => absurd h hd12, fun h => by linarith⟩
                    ⟨fun h => absurd h hd13, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                    ⟨fun h => absurd h hd14, fun h => by linarith⟩
                    ⟨fun h => absurd h hd15, fun h => by linarith⟩
                    ⟨fun h => absurd h hd16, fun h => by linarith⟩
                    ⟨fun h => absurd h hd17, fun h => by linarith⟩
                    ⟨fun h => absurd h hd18, fun h => by linarith⟩
                    ⟨fun h => absurd h hd19, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd118⟩
                    ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
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
                    ⟨fun h => absurd h hd117, fun h => by linarith⟩
                    ⟨fun h => absurd h hd20, fun h => by linarith⟩
                    ⟨fun h => absurd h hd21, fun h => by linarith⟩
                    ⟨fun h => absurd h hd22, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd119⟩
                    ⟨fun _ => by linarith, fun _ => hd9⟩
                    ⟨fun _ => by linarith, fun _ => hd10⟩
                    ⟨fun _ => by linarith, fun _ => hd11⟩
                    ⟨fun _ => by linarith, fun _ => hd23⟩
                    ⟨fun h => absurd h hd25, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd24⟩
                    ⟨fun h => absurd h hd26, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hd101⟩
                    ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
            · -- h23_1=F (1 pat)
              have hd125 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                fun h => h23_1_hyp (sys.trans _ _ _ h h01)
              exact fin4_witness sys (3/7) (13/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (3/7) (13/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd120⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd118⟩
                  ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
                  ⟨fun h => absurd h hd125, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd117, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd119⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h1_23=F (1 pat)
            have hd126 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T
              exfalso
              have h_tr := sys.trans _ _ _ h23_0_hyp h0_13_hyp
              rw [sys.additive ({2,3} : Set (Fin 4)) {1,3},
                  show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_tr
              exact hng21 h_tr
            · -- h23_0=F
              exact fin4_witness sys (17/42) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (17/42) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd120⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd118⟩
                  ⟨fun _ => by linarith, fun _ => h13_0_hyp⟩
                  ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd126⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd117, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd119⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
        · -- h13_0=F (3 pat)
          have hd127 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h_assumed
            have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
              rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
              exact h12
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,2},
                show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
            exact h13_0_hyp h_s3
          by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
          · -- h1_23=T (2 pat)
            by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
            · -- h23_1=T (1 pat)
              exact fin4_witness sys (3/7) (2/7) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (3/7) (2/7) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd120⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd118⟩
                  ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd127, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => h23_1_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd117, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd119⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (3/7) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (3/7) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd120⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd118⟩
                  ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h hd127, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd117, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd119⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h1_23=F (1 pat)
            have hd128 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            exact fin4_witness sys (17/42) (5/21) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (17/42) (5/21) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h0_13_hyp⟩
                ⟨fun _ => by linarith, fun _ => hd120⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun h => absurd h h1_23_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd118⟩
                ⟨fun h => absurd h h13_0_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h hd127, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd128⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd117, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd119⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd101⟩
                ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
      · -- h0_13=F (5 pat)
        have hd129 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_13_hyp)
        by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
        · -- h1_23=T (2 pat)
          have hd130 := sys.trans _ _ _ h01 h1_23_hyp
          by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
          · -- h23_1=T (1 pat)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T
              have hd131 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
              have hd132 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := by
                have h1 : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                  rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                      show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                      show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                  exact hd131
                have h2 : sys.ge ({0,2} : Set _) ({0,3} : Set _) := by
                  rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                      show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                      show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                  exact h23
                exact sys.trans _ _ _ h1 h2
              have hd133 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := fun h => by
                have h_bc : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
                  rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
                      show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                      show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
                  exact hd131
                have h1 := sys.trans _ _ _ h h_bc
                rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
                    show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                    show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
                exact hng32 h1
              exact absurd hd101 hd133
            · -- h23_0=F
              exact fin4_witness sys (8/21) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (8/21) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd130⟩
                  ⟨fun h => absurd h hd12, fun h => by linarith⟩
                  ⟨fun h => absurd h hd13, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                  ⟨fun h => absurd h hd14, fun h => by linarith⟩
                  ⟨fun h => absurd h hd15, fun h => by linarith⟩
                  ⟨fun h => absurd h hd16, fun h => by linarith⟩
                  ⟨fun h => absurd h hd17, fun h => by linarith⟩
                  ⟨fun h => absurd h hd18, fun h => by linarith⟩
                  ⟨fun h => absurd h hd19, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd118⟩
                  ⟨fun _ => by linarith, fun _ => hd129⟩
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
                  ⟨fun h => absurd h hd117, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd119⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h23_1=F (1 pat)
            have hd134 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              fun h => h23_1_hyp (sys.trans _ _ _ h h01)
            exact fin4_witness sys (17/42) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (17/42) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd130⟩
                ⟨fun h => absurd h hd12, fun h => by linarith⟩
                ⟨fun h => absurd h hd13, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h1_23_hyp⟩
                ⟨fun h => absurd h hd14, fun h => by linarith⟩
                ⟨fun h => absurd h hd15, fun h => by linarith⟩
                ⟨fun h => absurd h hd16, fun h => by linarith⟩
                ⟨fun h => absurd h hd17, fun h => by linarith⟩
                ⟨fun h => absurd h hd18, fun h => by linarith⟩
                ⟨fun h => absurd h hd19, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd118⟩
                ⟨fun _ => by linarith, fun _ => hd129⟩
                ⟨fun h => absurd h hd134, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun h => absurd h h23_1_hyp, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd117, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd119⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd101⟩
                ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
        · -- h1_23=F (3 pat)
          have hd135 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
            (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
          by_cases h0_23_hyp : sys.ge {(0 : Fin 4)} ({2,3} : Set _)
          · -- h0_23=T (2 pat)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T (1 pat)
              exact fin4_witness sys (5/14) (2/7) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (5/14) (2/7) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd118⟩
                  ⟨fun _ => by linarith, fun _ => hd129⟩
                  ⟨fun _ => by linarith, fun _ => h23_0_hyp⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd135⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd117, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd119⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
            · -- h23_0=F (1 pat)
              exact fin4_witness sys (8/21) (11/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (8/21) (11/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
                  ⟨fun h => absurd h hng32, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                  ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                  ⟨fun _ => by linarith, fun _ => hd118⟩
                  ⟨fun _ => by linarith, fun _ => hd129⟩
                  ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd1⟩
                  ⟨fun _ => by linarith, fun _ => hd2⟩
                  ⟨fun _ => by linarith, fun _ => hd135⟩
                  ⟨fun _ => by linarith, fun _ => hd3⟩
                  ⟨fun _ => by linarith, fun _ => hd4⟩
                  ⟨fun _ => by linarith, fun _ => hd5⟩
                  ⟨fun _ => by linarith, fun _ => hd6⟩
                  ⟨fun _ => by linarith, fun _ => hd7⟩
                  ⟨fun _ => by linarith, fun _ => hd8⟩
                  ⟨fun h => absurd h hd117, fun h => by linarith⟩
                  ⟨fun h => absurd h hd20, fun h => by linarith⟩
                  ⟨fun h => absurd h hd21, fun h => by linarith⟩
                  ⟨fun h => absurd h hd22, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd119⟩
                  ⟨fun _ => by linarith, fun _ => hd9⟩
                  ⟨fun _ => by linarith, fun _ => hd10⟩
                  ⟨fun _ => by linarith, fun _ => hd11⟩
                  ⟨fun _ => by linarith, fun _ => hd23⟩
                  ⟨fun h => absurd h hd25, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd24⟩
                  ⟨fun h => absurd h hd26, fun h => by linarith⟩
                  ⟨fun _ => by linarith, fun _ => hd101⟩
                  ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
          · -- h0_23=F (1 pat)
            have hd136 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_23_hyp)
            exact fin4_witness sys (1/3) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (1/3) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
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
                ⟨fun h => absurd h hng32, fun h => by linarith⟩
                ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
                ⟨fun h => absurd h h0_13_hyp, fun h => by linarith⟩
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
                ⟨fun _ => by linarith, fun _ => hd118⟩
                ⟨fun _ => by linarith, fun _ => hd129⟩
                ⟨fun _ => by linarith, fun _ => hd136⟩
                ⟨fun _ => by linarith, fun _ => hd1⟩
                ⟨fun _ => by linarith, fun _ => hd2⟩
                ⟨fun _ => by linarith, fun _ => hd135⟩
                ⟨fun _ => by linarith, fun _ => hd3⟩
                ⟨fun _ => by linarith, fun _ => hd4⟩
                ⟨fun _ => by linarith, fun _ => hd5⟩
                ⟨fun _ => by linarith, fun _ => hd6⟩
                ⟨fun _ => by linarith, fun _ => hd7⟩
                ⟨fun _ => by linarith, fun _ => hd8⟩
                ⟨fun h => absurd h hd117, fun h => by linarith⟩
                ⟨fun h => absurd h hd20, fun h => by linarith⟩
                ⟨fun h => absurd h hd21, fun h => by linarith⟩
                ⟨fun h => absurd h hd22, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd119⟩
                ⟨fun _ => by linarith, fun _ => hd9⟩
                ⟨fun _ => by linarith, fun _ => hd10⟩
                ⟨fun _ => by linarith, fun _ => hd11⟩
                ⟨fun _ => by linarith, fun _ => hd23⟩
                ⟨fun h => absurd h hd25, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd24⟩
                ⟨fun h => absurd h hd26, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hd101⟩
                ⟨fun h => absurd h h12_03_hyp, fun h => by linarith⟩)
-- ═══════════════════════════════════════════════════════════════
-- § 6d. All-non-null case tree
-- ═══════════════════════════════════════════════════════════════


end Core.Scale
