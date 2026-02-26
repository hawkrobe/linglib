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
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd13 := nge_singleton_pair sys h01 hn3
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd14 := nge_singleton_pair sys h02 hn1
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd15 := nge_singleton_pair sys h02 hn3
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd16 := nge_singleton_pair sys h12 hn3
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd17 := nge_singleton_pair sys h03 hn1
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd18 := nge_singleton_pair sys h03 hn2
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd19 := nge_singleton_pair sys h13 hn2
      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd20 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hng10
  have hd21 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hng20
  have hd22 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hng30
  have hd23 : sys.ge ({0,1} : Set (Fin 4)) ({2,3} : Set _) :=
    ge_pair_via_mid sys {0,1} {2,3} {0,2} h12 h03 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd24 : sys.ge ({0,2} : Set (Fin 4)) ({1,3} : Set _) :=
    ge_pair_via_mid sys {0,2} {1,3} {0,3} h23 h01 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd25 : ¬sys.ge ({2,3} : Set (Fin 4)) ({0,1} : Set _) :=
    nge_pair_via_contra sys {2,3} {0,1} {0,2} h12 hng30 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd26 : ¬sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) :=
    nge_pair_via_contra sys {1,3} {0,2} {0,3} h23 hng10 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  by_cases h12_03_hyp : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _)
  · -- h12_03=T (22 pat)
    by_cases h03_12_hyp : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _)
    · -- h03_12=T (11 pat)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (6 pat)
        have hd27 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (3 pat)
          have hd28 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h13_0_hyp
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                  show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by sdiff,
                  show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by sdiff]
              exact h23
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,3},
                show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by sdiff,
                show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
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
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by sdiff,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by sdiff] at h_tr
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
                      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
                  have hd33 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                    nge_pair_via_contra sys {0,3} {1,2} {0,2} hd31 hng32 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
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
                      (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                      (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                      (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                      (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                      (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                      (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                      (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                      (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                      (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                      (bp h0_13_hyp (by linarith)) (bp hd27 (by linarith)) (bn hd12 (fun h => by linarith))
                      (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                      (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                      (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd28 (by linarith))
                      (bp h13_0_hyp (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                      (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                      (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                      (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd29 (fun h => by linarith))
                      (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                      (bp hd30 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                      (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                      (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                      (bp h12_03_hyp (by linarith)))
            · -- h23_1=F (1 pat)
              have hd34 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                fun h => h23_1_hyp (sys.trans _ _ _ h h01)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                exfalso
                have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
                rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by sdiff,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by sdiff] at h_tr
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd27 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd28 (by linarith))
                    (bp h13_0_hyp (by linarith)) (bn hd34 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd35 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd36 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                    (bp h12_03_hyp (by linarith)))
          · -- h1_23=F (1 pat)
            have hd37 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
            · -- h0_12=T
              exfalso
              have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
              rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                  show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by sdiff,
                  show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by sdiff] at h_tr
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
                    show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                    show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff] at h_tr
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd27 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd28 (by linarith))
                    (bp h13_0_hyp (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bp hd37 (by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd38 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd39 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                    (bp h12_03_hyp (by linarith)))
        · -- h13_0=F (3 pat)
          have hd40 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h_assumed
            have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
              rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff]
              exact h12
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,2},
                show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
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
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by sdiff,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by sdiff] at h_tr
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd27 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd42 (by linarith))
                    (bn h13_0_hyp (fun h => by linarith)) (bn hd40 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd41 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd43 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                    (bp h12_03_hyp (by linarith)))
            · -- h23_1=F (1 pat)
              by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
              · -- h0_12=T
                exfalso
                have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
                rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                    show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by sdiff,
                    show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by sdiff] at h_tr
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd27 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd45 (by linarith))
                    (bn h13_0_hyp (fun h => by linarith)) (bn hd40 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd44 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd46 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                    (bp h12_03_hyp (by linarith)))
          · -- h1_23=F (1 pat)
            have hd47 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
            · -- h0_12=T
              exfalso
              have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
              rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                  show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by sdiff,
                  show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by sdiff] at h_tr
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bp h0_13_hyp (by linarith)) (bp hd27 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd49 (by linarith))
                  (bn h13_0_hyp (fun h => by linarith)) (bn hd40 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd47 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd48 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd50 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                  (bp h12_03_hyp (by linarith)))
      · -- h0_13=F (5 pat)
        have hd51 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
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
              have hd58 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                nge_pair_via_contra sys {0,3} {1,2} {0,2} hd57 hng32 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd51 (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp hd56 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd53 (by linarith))
                  (bp hd54 (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd52 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd55 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                  (bp h12_03_hyp (by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd51 (fun h => by linarith))
                (bn h0_13_hyp (fun h => by linarith)) (bp hd56 (by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd53 (by linarith))
                (bp hd54 (by linarith)) (bn hd59 (fun h => by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd52 (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd55 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                (bp h12_03_hyp (by linarith)))
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd51 (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp h0_23_hyp (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd53 (by linarith))
                  (bp hd54 (by linarith)) (bp h23_0_hyp (by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd60 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd52 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd55 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                  (bp h12_03_hyp (by linarith)))
            · -- h23_0=F (1 pat)
              exact fin4_witness sys (5/14) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (5/14) (13/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd51 (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp h0_23_hyp (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd53 (by linarith))
                  (bp hd54 (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd60 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd52 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd55 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                  (bp h12_03_hyp (by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd51 (fun h => by linarith))
                (bn h0_13_hyp (fun h => by linarith)) (bn h0_23_hyp (fun h => by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd53 (by linarith))
                (bp hd54 (by linarith)) (bp hd61 (by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bp hd60 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd52 (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd55 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp h03_12_hyp (by linarith))
                (bp h12_03_hyp (by linarith)))
    · -- h03_12=F (11 pat)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (6 pat)
        have hd62 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (3 pat)
          have hd63 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h13_0_hyp
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                  show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by sdiff,
                  show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by sdiff]
              exact h23
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,3},
                show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by sdiff,
                show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
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
                      (by sdiff) (by sdiff) (by sdiff) (by sdiff)
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
                      (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                      (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                      (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                      (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                      (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                      (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                      (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                      (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                      (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                      (bp h0_13_hyp (by linarith)) (bp hd62 (by linarith)) (bn hd12 (fun h => by linarith))
                      (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                      (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                      (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd63 (by linarith))
                      (bp h13_0_hyp (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                      (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                      (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                      (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd65 (fun h => by linarith))
                      (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                      (bp hd66 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                      (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                      (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                      (bp h12_03_hyp (by linarith)))
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd62 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd63 (by linarith))
                    (bp h13_0_hyp (by linarith)) (bn hd69 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd71 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd72 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                    (bp h12_03_hyp (by linarith)))
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
                    show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                    show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff] at h_tr
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd62 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd63 (by linarith))
                    (bp h13_0_hyp (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bp hd73 (by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd75 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd76 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                    (bp h12_03_hyp (by linarith)))
        · -- h13_0=F (3 pat)
          have hd77 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h_assumed
            have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
              rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff]
              exact h12
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,2},
                show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd62 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd80 (by linarith))
                    (bn h13_0_hyp (fun h => by linarith)) (bn hd77 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd79 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd81 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                    (bp h12_03_hyp (by linarith)))
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd62 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd84 (by linarith))
                    (bn h13_0_hyp (fun h => by linarith)) (bn hd77 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd83 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd85 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                    (bp h12_03_hyp (by linarith)))
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bp h0_13_hyp (by linarith)) (bp hd62 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd89 (by linarith))
                  (bn h13_0_hyp (fun h => by linarith)) (bn hd77 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd86 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd88 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd90 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                  (bp h12_03_hyp (by linarith)))
      · -- h0_13=F (5 pat)
        have hd91 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd91 (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp hd96 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd93 (by linarith))
                  (bp hd94 (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd92 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd95 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                  (bp h12_03_hyp (by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd91 (fun h => by linarith))
                (bn h0_13_hyp (fun h => by linarith)) (bp hd96 (by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd93 (by linarith))
                (bp hd94 (by linarith)) (bn hd98 (fun h => by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd92 (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd95 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                (bp h12_03_hyp (by linarith)))
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd91 (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp h0_23_hyp (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd93 (by linarith))
                  (bp hd94 (by linarith)) (bp h23_0_hyp (by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd99 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd92 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd95 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                  (bp h12_03_hyp (by linarith)))
            · -- h23_0=F (1 pat)
              exact fin4_witness sys (5/14) (13/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (5/14) (13/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd91 (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp h0_23_hyp (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd93 (by linarith))
                  (bp hd94 (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd99 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd92 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd95 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                  (bp h12_03_hyp (by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn hd91 (fun h => by linarith))
                (bn h0_13_hyp (fun h => by linarith)) (bn h0_23_hyp (fun h => by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd93 (by linarith))
                (bp hd94 (by linarith)) (bp hd100 (by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bp hd99 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd92 (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd95 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bn h03_12_hyp (fun h => by linarith))
                (bp h12_03_hyp (by linarith)))
  · -- h12_03=F (23 pat)
    have hd101 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
      (sys.total ({0,3} : Set (Fin 4)) ({1,2} : Set _)).elim id (fun h => absurd h h12_03_hyp)
    by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
    · -- h0_12=T (12 pat)
      have hd102 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
              show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
              show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
          exact h23
        exact sys.trans _ _ _ h0_12_hyp h_mid
      have hd103 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({2,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {2,3},
              show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
              show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
          exact h13
        exact sys.trans _ _ _ h0_12_hyp h_mid
      by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
      · -- h0_123=T (6 pat)
        have hd104 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
              show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
              show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff] at h1
          exact hn3 h1
        have hd105 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
              show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
              show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h1
          exact hn2 h1
        have hd106 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({2,3} : Set (Fin 4)) {1,2,3},
              show ({2,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
              show ({1,2,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff] at h1
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                  (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn hd104 (fun h => by linarith))
                  (bn hd105 (fun h => by linarith)) (bn hd106 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp h0_123_hyp (by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp h123_0_hyp (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (1/2) (11/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (1/2) (11/42) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                  (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn hd104 (fun h => by linarith))
                  (bn hd105 (fun h => by linarith)) (bn hd106 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp h0_123_hyp (by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp h123_0_hyp (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn hd104 (fun h => by linarith))
                (bn hd105 (fun h => by linarith)) (bn hd106 (fun h => by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bp hd107 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp h0_123_hyp (by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp h123_0_hyp (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                (bn h12_03_hyp (fun h => by linarith)))
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                  (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn hd104 (fun h => by linarith))
                  (bn hd105 (fun h => by linarith)) (bn hd106 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp h0_123_hyp (by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bn h123_0_hyp (fun h => by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (11/21) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (11/21) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                  (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn hd104 (fun h => by linarith))
                  (bn hd105 (fun h => by linarith)) (bn hd106 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp h0_123_hyp (by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bn h123_0_hyp (fun h => by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn hd104 (fun h => by linarith))
                (bn hd105 (fun h => by linarith)) (bn hd106 (fun h => by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bp hd108 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp h0_123_hyp (by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn h123_0_hyp (fun h => by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                (bn h12_03_hyp (fun h => by linarith)))
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
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h_tr
                exact hng32 h_tr
              · -- h13_0=F
                have hd110 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
                  have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
                    rw [sys.additive ({1,2,3} : Set _) {0,1},
                        show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                        show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
                    exact h_assumed
                  have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
                    rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                        show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff,
                        show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff]
                    exact h12
                  have h_s3 := sys.trans _ _ _ h_s1 h_s2
                  rw [sys.additive ({1,2,3} : Set _) {0,2},
                      show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                      show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
                  exact h13_0_hyp h_s3
                exact fin4_witness sys (10/21) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (fin4_dispatch sys (10/21) (11/42) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                    hn0 hn1 hn2 hn3
                    (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                    (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                    (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                    (mf4_univ ..)
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                    (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp h12_0_hyp (by linarith))
                    (bn h13_0_hyp (fun h => by linarith)) (bn hd110 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn h0_123_hyp (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd109 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                    (bn h12_03_hyp (fun h => by linarith)))
            · -- h23_1=F (1 pat)
              have hd111 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
                fun h => h23_1_hyp (sys.trans _ _ _ h h01)
              by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
              · -- h13_0=T
                exfalso
                have h_tr := sys.trans _ _ _ h13_0_hyp h0_12_hyp
                rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h_tr
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                    (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp h12_0_hyp (by linarith))
                    (bn h13_0_hyp (fun h => by linarith)) (bn hd111 (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn h0_123_hyp (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd109 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                    (bn h12_03_hyp (fun h => by linarith)))
          · -- h1_23=F (1 pat)
            have hd112 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h13_0=T
              exfalso
              have h_tr := sys.trans _ _ _ h13_0_hyp h0_12_hyp
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h_tr
              exact hng32 h_tr
            · -- h13_0=F
              have hd113 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
                have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
                  rw [sys.additive ({1,2,3} : Set _) {0,1},
                      show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                      show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
                  exact h_assumed
                have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
                  rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                      show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff,
                      show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff]
                  exact h12
                have h_s3 := sys.trans _ _ _ h_s1 h_s2
                rw [sys.additive ({1,2,3} : Set _) {0,2},
                    show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                    show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
                exact h13_0_hyp h_s3
              exact fin4_witness sys (3/7) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (3/7) (5/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                  (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp h12_0_hyp (by linarith))
                  (bn h13_0_hyp (fun h => by linarith)) (bn hd113 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd112 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn h0_123_hyp (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd109 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
        · -- h12_0=F (3 pat)
          have hd114 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h_assumed
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,3} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
                  show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by sdiff,
                  show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by sdiff]
              exact h23
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,3},
                show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by sdiff,
                show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
            exact h12_0_hyp h_s3
          have hd115 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h_assumed
            have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,3} : Set _) := by
              rw [sys.additive ({0,1} : Set (Fin 4)) {0,3},
                  show ({0,1} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by sdiff,
                  show ({0,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by sdiff]
              exact h13
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,3},
                show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by sdiff,
                show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                  (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn h12_0_hyp (fun h => by linarith))
                  (bn hd114 (fun h => by linarith)) (bn hd115 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn h0_123_hyp (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd109 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (19/42) (2/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (19/42) (2/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                  (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn h12_0_hyp (fun h => by linarith))
                  (bn hd114 (fun h => by linarith)) (bn hd115 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn h0_123_hyp (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd109 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bp h0_12_hyp (by linarith))
                (bp hd102 (by linarith)) (bp hd103 (by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bn h12_0_hyp (fun h => by linarith))
                (bn hd114 (fun h => by linarith)) (bn hd115 (fun h => by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bp hd116 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn h0_123_hyp (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd109 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                (bn h12_03_hyp (fun h => by linarith)))
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
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
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
                    (by sdiff) (by sdiff) (by sdiff) (by sdiff)
                have hd123 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) :=
                  ge_pair_via_mid sys {1,2} {0,3} {0,2} hd121 h23 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
                have hd124 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                  nge_pair_via_contra sys {0,3} {1,2} {0,2} hd121 hng32 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
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
                    (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                    (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                    (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                    (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                    (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                    (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                    (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                    (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                    (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                    (bp h0_13_hyp (by linarith)) (bp hd120 (by linarith)) (bn hd12 (fun h => by linarith))
                    (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                    (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                    (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                    (bp h13_0_hyp (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                    (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                    (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                    (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                    (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                    (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                    (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                    (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                    (bn h12_03_hyp (fun h => by linarith)))
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bp h0_13_hyp (by linarith)) (bp hd120 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                  (bp h13_0_hyp (by linarith)) (bn hd125 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
          · -- h1_23=F (1 pat)
            have hd126 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
              (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h h1_23_hyp)
            by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
            · -- h23_0=T
              exfalso
              have h_tr := sys.trans _ _ _ h23_0_hyp h0_13_hyp
              rw [sys.additive ({2,3} : Set (Fin 4)) {1,3},
                  show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                  show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff] at h_tr
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bp h0_13_hyp (by linarith)) (bp hd120 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                  (bp h13_0_hyp (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd126 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
        · -- h13_0=F (3 pat)
          have hd127 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,1} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h_assumed
            have h_s2 : sys.ge ({0,1} : Set (Fin 4)) ({0,2} : Set _) := by
              rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff]
              exact h12
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,2},
                show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bp h0_13_hyp (by linarith)) (bp hd120 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                  (bn h13_0_hyp (fun h => by linarith)) (bn hd127 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
            · -- h23_1=F (1 pat)
              exact fin4_witness sys (3/7) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (3/7) (13/42) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bp h0_13_hyp (by linarith)) (bp hd120 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                  (bn h13_0_hyp (fun h => by linarith)) (bn hd127 (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                (bp h0_13_hyp (by linarith)) (bp hd120 (by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                (bn h13_0_hyp (fun h => by linarith)) (bn hd127 (fun h => by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bp hd128 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                (bn h12_03_hyp (fun h => by linarith)))
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
              have hd132 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) :=
                ge_pair_via_mid sys {1,2} {0,3} {0,2} hd131 h23 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
              have hd133 : ¬sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
                nge_pair_via_contra sys {0,3} {1,2} {0,2} hd131 hng32 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp hd130 (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                  (bp hd129 (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp h23_1_hyp (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                (bn h0_13_hyp (fun h => by linarith)) (bp hd130 (by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bp h1_23_hyp (by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                (bp hd129 (by linarith)) (bn hd134 (fun h => by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bn h23_1_hyp (fun h => by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                (bn h12_03_hyp (fun h => by linarith)))
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
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp h0_23_hyp (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                  (bp hd129 (by linarith)) (bp h23_0_hyp (by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd135 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
            · -- h23_0=F (1 pat)
              exact fin4_witness sys (8/21) (11/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (fin4_dispatch sys (8/21) (11/42) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
                  hn0 hn1 hn2 hn3
                  (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                  (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                  (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                  (mf4_univ ..)
                  (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                  (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                  (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                  (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                  (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                  (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                  (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                  (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                  (bn h0_13_hyp (fun h => by linarith)) (bp h0_23_hyp (by linarith)) (bn hd12 (fun h => by linarith))
                  (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                  (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                  (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                  (bp hd129 (by linarith)) (bn h23_0_hyp (fun h => by linarith)) (bp hd1 (by linarith))
                  (bp hd2 (by linarith)) (bp hd135 (by linarith)) (bp hd3 (by linarith))
                  (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                  (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                  (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                  (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                  (bn h12_03_hyp (fun h => by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith)) (bn hn2 (fun h => by linarith))
                (bn hn3 (fun h => by linarith)) (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith)) (bn hne13 (fun h => by linarith))
                (bn hne23 (fun h => by linarith)) (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith)) (bp h01 (by linarith))
                (bn hng10 (fun h => by linarith)) (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith)) (bp h12 (by linarith))
                (bn hng21 (fun h => by linarith)) (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith)) (bn h0_12_hyp (fun h => by linarith))
                (bn h0_13_hyp (fun h => by linarith)) (bn h0_23_hyp (fun h => by linarith)) (bn hd12 (fun h => by linarith))
                (bn hd13 (fun h => by linarith)) (bn h1_23_hyp (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith)) (bn hd17 (fun h => by linarith))
                (bn hd18 (fun h => by linarith)) (bn hd19 (fun h => by linarith)) (bp hd118 (by linarith))
                (bp hd129 (by linarith)) (bp hd136 (by linarith)) (bp hd1 (by linarith))
                (bp hd2 (by linarith)) (bp hd135 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bn hd117 (fun h => by linarith))
                (bn hd20 (fun h => by linarith)) (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd119 (by linarith)) (bp hd9 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd23 (by linarith)) (bn hd25 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd26 (fun h => by linarith)) (bp hd101 (by linarith))
                (bn h12_03_hyp (fun h => by linarith)))
-- ═══════════════════════════════════════════════════════════════
-- § 6d. All-non-null case tree
-- ═══════════════════════════════════════════════════════════════


end Core.Scale
