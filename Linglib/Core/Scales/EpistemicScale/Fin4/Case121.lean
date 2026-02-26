import Linglib.Core.Scales.EpistemicScale.Fin4.Defs

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000 in
/-- Case (1,2,1): 13 sub-cases. -/
theorem fin4_case_121 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (hng10 : ¬sys.ge {(1 : Fin 4)} {0})
    (h12 : sys.ge {(1 : Fin 4)} {2})
    (h21 : sys.ge {(2 : Fin 4)} {1})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (hng32 : ¬sys.ge {(3 : Fin 4)} {2})
    (h02 : sys.ge {(0 : Fin 4)} {2})
    (h13 : sys.ge {(1 : Fin 4)} {3})
    (h03 : sys.ge {(0 : Fin 4)} {3})
    :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  have hng20 : ¬sys.ge {(2 : Fin 4)} {0} := fun h => hng10 (sys.trans _ _ _ h12 h)
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
  have hd3 := ge_superset sys (show (2:Fin 4) ∈ ({2,3}:Set _) from Or.inl rfl) h21
  have hd4 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h02
  have hd5 := ge_superset sys (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl) h02
  have hd6 := ge_superset sys (show (1:Fin 4) ∈ ({1,3}:Set _) from Or.inl rfl) h12
  have hd7 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h03
  have hd8 := ge_superset sys (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl) h03
  have hd9 := ge_superset sys (show (1:Fin 4) ∈ ({1,2}:Set _) from Or.inl rfl) h13
  have hd10 := ge_superset sys (show (0:Fin 4) ∈ ({0,2,3}:Set _) from Or.inl rfl) h01
  have hd11 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,3}:Set _) from Or.inl rfl) h02
  have hd12 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,2}:Set _) from Or.inl rfl) h03
  have hd13 := nge_singleton_pair sys h01 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd14 := nge_singleton_pair sys h01 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd15 := nge_singleton_pair sys h21 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd16 := nge_singleton_pair sys h02 hn1 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd17 := nge_singleton_pair sys h02 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd18 := nge_singleton_pair sys h12 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd19 := nge_singleton_pair sys h03 hn1 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd20 := nge_singleton_pair sys h03 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd21 := nge_singleton_pair sys h13 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd22 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hng10
  have hd23 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hng20
  have hd24 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hng30
  -- pair vs pair
  have hd25 := ge_pair_via_mid sys ({0,1} : Set _) ({2,3} : Set _) ({0,2} : Set _)
    h12 h03 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd26 := ge_pair_via_mid sys ({0,2} : Set _) ({1,3} : Set _) ({0,1} : Set _)
    h21 h03 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd27 := nge_pair_via_contra sys ({2,3} : Set _) ({0,1} : Set _) ({0,2} : Set _)
    h12 hng30 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd28 := nge_pair_via_contra sys ({1,3} : Set _) ({0,2} : Set _) ({0,1} : Set _)
    h21 hng30 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  by_cases h12_03_hyp : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _)
  · -- h12_03=T (6 pat)
    by_cases h03_12_hyp : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _)
    · -- h03_12=T (3 pat)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (2 pat)
        have hd29 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (1 pat)
          have hd30 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
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
          have hd31 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h13_0_hyp
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,1} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,1},
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff]
              exact h21
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,1},
                show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
            exact h_s3
          by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
          · -- h0_12=T
            exfalso
            have h_tr := sys.trans _ _ _ h0_12_hyp h12_03_hyp
            rw [sys.additive ({(0 : Fin 4)} : Set (Fin 4)) {0,3},
                show ({(0 : Fin 4)} : Set (Fin 4)) \ {0,3} = ∅ from by sdiff,
                show ({0,3} : Set (Fin 4)) \ {(0 : Fin 4)} = {(3 : Fin 4)} from by sdiff] at h_tr
            exact hn3 h_tr
          · -- h0_12=F
            have hd32 := nge_superset sys
              (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
            have hd33 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd32)
            exact fin4_witness sys (3/8) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (3/8) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                -- ∅ vs singletons (4)
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                -- ∅ vs pairs (6)
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                -- ∅ vs triples (4)
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                -- singleton vs singleton (12)
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bp h21 (by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
                -- singleton vs pair (24)
                (bn h0_12_hyp (fun h => by linarith)) (bp h0_13_hyp (by linarith))
                (bp hd29 (by linarith))
                (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith))
                -- pair vs singleton (12)
                (bp hd30 (by linarith)) (bp h13_0_hyp (by linarith))
                (bp hd31 (by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
                -- singleton vs triple (4)
                (bn hd32 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
                -- triple vs singleton (4)
                (bp hd33 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd12 (by linarith))
                -- pair vs pair (6)
                (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
                (bp h03_12_hyp (by linarith)) (bp h12_03_hyp (by linarith)))
        · -- h13_0=F (1 pat)
          have hd34 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
            have hd36 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
            have hd37 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd35)
            exact fin4_witness sys (8/21) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (8/21) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                -- ∅ vs singletons (4)
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                -- ∅ vs pairs (6)
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                -- ∅ vs triples (4)
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                -- singleton vs singleton (12)
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bp h21 (by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
                -- singleton vs pair (24)
                (bn h0_12_hyp (fun h => by linarith)) (bp h0_13_hyp (by linarith))
                (bp hd29 (by linarith))
                (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith))
                -- pair vs singleton (12)
                (bp hd36 (by linarith)) (bn h13_0_hyp (fun h => by linarith))
                (bn hd34 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
                -- singleton vs triple (4)
                (bn hd35 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
                -- triple vs singleton (4)
                (bp hd37 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd12 (by linarith))
                -- pair vs pair (6)
                (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
                (bp h03_12_hyp (by linarith)) (bp h12_03_hyp (by linarith)))
      · -- h0_13=F (1 pat)
        have hd38 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
            exact h23
          exact h0_13_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd39 : ¬sys.ge {(0 : Fin 4)} ({2,3} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({2,3} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({2,3} : Set (Fin 4)) {1,3},
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff]
            exact h21
          exact h0_13_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd40 := nge_superset sys
          (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd38
        have hd41 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd38)
        have hd42 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_13_hyp)
        have hd43 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd39)
        have hd44 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd40)
        exact fin4_witness sys (11/42) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
          hn0 hn1 hn2 hn3
          (fin4_dispatch sys (11/42) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
            (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
            (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
            (mf4_univ ..)
            -- ∅ vs singletons (4)
            (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
            (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
            -- ∅ vs pairs (6)
            (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
            (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
            (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
            -- ∅ vs triples (4)
            (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
            (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
            -- singleton vs singleton (12)
            (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
            (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
            (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
            (bp h12 (by linarith)) (bp h21 (by linarith))
            (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
            (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
            -- singleton vs pair (24)
            (bn hd38 (fun h => by linarith)) (bn h0_13_hyp (fun h => by linarith))
            (bn hd39 (fun h => by linarith))
            (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
            (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
            (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
            (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
            (bn hd21 (fun h => by linarith))
            -- pair vs singleton (12)
            (bp hd41 (by linarith)) (bp hd42 (by linarith))
            (bp hd43 (by linarith))
            (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
            (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
            (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
            -- singleton vs triple (4)
            (bn hd40 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
            (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
            -- triple vs singleton (4)
            (bp hd44 (by linarith)) (bp hd10 (by linarith))
            (bp hd11 (by linarith)) (bp hd12 (by linarith))
            -- pair vs pair (6)
            (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
            (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
            (bp h03_12_hyp (by linarith)) (bp h12_03_hyp (by linarith)))
    · -- h03_12=F (3 pat)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (2 pat)
        have hd45 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (1 pat)
          have hd46 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
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
          have hd47 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h13_0_hyp
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,1} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,1},
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff]
              exact h21
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,1},
                show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
            exact h_s3
          by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
          · -- h0_12=T
            have hd48 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
              sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
            exact absurd hd48 h03_12_hyp
          · -- h0_12=F
            have hd49 := nge_superset sys
              (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
            have hd50 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd49)
            exact fin4_witness sys (5/14) (2/7) (2/7) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (5/14) (2/7) (2/7) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                -- ∅ vs singletons (4)
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                -- ∅ vs pairs (6)
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                -- ∅ vs triples (4)
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                -- singleton vs singleton (12)
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bp h21 (by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
                -- singleton vs pair (24)
                (bn h0_12_hyp (fun h => by linarith)) (bp h0_13_hyp (by linarith))
                (bp hd45 (by linarith))
                (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith))
                -- pair vs singleton (12)
                (bp hd46 (by linarith)) (bp h13_0_hyp (by linarith))
                (bp hd47 (by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
                -- singleton vs triple (4)
                (bn hd49 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
                -- triple vs singleton (4)
                (bp hd50 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd12 (by linarith))
                -- pair vs pair (6)
                (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
                (bn h03_12_hyp (fun h => by linarith)) (bp h12_03_hyp (by linarith)))
        · -- h13_0=F (1 pat)
          have hd51 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
          by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
          · -- h0_12=T
            have hd52 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
              sys.trans _ _ _ (sys.mono _ _ (show ({0} : Set (Fin 4)) ⊆ {0,3} from fun x hx => by fin_cases x <;> simp_all)) h0_12_hyp
            exact absurd hd52 h03_12_hyp
          · -- h0_12=F
            have hd53 := nge_superset sys
              (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
            have hd54 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
            have hd55 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd53)
            exact fin4_witness sys (5/14) (13/42) (13/42) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (5/14) (13/42) (13/42) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                -- ∅ vs singletons (4)
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                -- ∅ vs pairs (6)
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                -- ∅ vs triples (4)
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                -- singleton vs singleton (12)
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bp h21 (by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
                -- singleton vs pair (24)
                (bn h0_12_hyp (fun h => by linarith)) (bp h0_13_hyp (by linarith))
                (bp hd45 (by linarith))
                (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith))
                -- pair vs singleton (12)
                (bp hd54 (by linarith)) (bn h13_0_hyp (fun h => by linarith))
                (bn hd51 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
                -- singleton vs triple (4)
                (bn hd53 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
                -- triple vs singleton (4)
                (bp hd55 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd12 (by linarith))
                -- pair vs pair (6)
                (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
                (bn h03_12_hyp (fun h => by linarith)) (bp h12_03_hyp (by linarith)))
      · -- h0_13=F (1 pat)
        have hd56 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
            exact h23
          exact h0_13_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd57 : ¬sys.ge {(0 : Fin 4)} ({2,3} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({2,3} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({2,3} : Set (Fin 4)) {1,3},
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff]
            exact h21
          exact h0_13_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd58 := nge_superset sys
          (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd56
        have hd59 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd56)
        have hd60 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_13_hyp)
        have hd61 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd57)
        have hd62 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd58)
        exact fin4_witness sys (2/7) (11/42) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
          hn0 hn1 hn2 hn3
          (fin4_dispatch sys (2/7) (11/42) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
            (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
            (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
            (mf4_univ ..)
            -- ∅ vs singletons (4)
            (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
            (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
            -- ∅ vs pairs (6)
            (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
            (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
            (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
            -- ∅ vs triples (4)
            (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
            (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
            -- singleton vs singleton (12)
            (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
            (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
            (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
            (bp h12 (by linarith)) (bp h21 (by linarith))
            (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
            (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
            -- singleton vs pair (24)
            (bn hd56 (fun h => by linarith)) (bn h0_13_hyp (fun h => by linarith))
            (bn hd57 (fun h => by linarith))
            (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
            (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
            (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
            (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
            (bn hd21 (fun h => by linarith))
            -- pair vs singleton (12)
            (bp hd59 (by linarith)) (bp hd60 (by linarith))
            (bp hd61 (by linarith))
            (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
            (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
            (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
            -- singleton vs triple (4)
            (bn hd58 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
            (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
            -- triple vs singleton (4)
            (bp hd62 (by linarith)) (bp hd10 (by linarith))
            (bp hd11 (by linarith)) (bp hd12 (by linarith))
            -- pair vs pair (6)
            (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
            (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
            (bn h03_12_hyp (fun h => by linarith)) (bp h12_03_hyp (by linarith)))
  · -- h12_03=F (7 pat)
    have hd63 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) :=
      (sys.total ({0,3} : Set (Fin 4)) ({1,2} : Set _)).elim id (fun h => absurd h h12_03_hyp)
    by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
    · -- h0_12=T (4 pat)
      have hd64 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
              show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
              show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
          exact h23
        exact sys.trans _ _ _ h0_12_hyp h_mid
      have hd65 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({2,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {2,3},
              show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
              show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
          exact h13
        exact sys.trans _ _ _ h0_12_hyp h_mid
      by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
      · -- h0_123=T (2 pat)
        have hd66 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
              show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
              show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff] at h1
          exact hn3 h1
        have hd67 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
              show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
              show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h1
          exact hn2 h1
        have hd68 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
          have h1 := sys.trans _ _ _ h h0_123_hyp
          rw [sys.additive ({2,3} : Set (Fin 4)) {1,2,3},
              show ({2,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
              show ({1,2,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff] at h1
          exact hn1 h1
        by_cases h123_0_hyp : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)
        · -- h123_0=T (1 pat)
          exact fin4_witness sys (1/2) (4/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (1/2) (4/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              -- ∅ vs singletons (4)
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              -- ∅ vs pairs (6)
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              -- ∅ vs triples (4)
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              -- singleton vs singleton (12)
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bp h21 (by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
              -- singleton vs pair (24)
              (bp h0_12_hyp (by linarith)) (bp hd64 (by linarith))
              (bp hd65 (by linarith))
              (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
              (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith))
              -- pair vs singleton (12)
              (bn hd66 (fun h => by linarith)) (bn hd67 (fun h => by linarith))
              (bn hd68 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
              (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
              (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
              -- singleton vs triple (4)
              (bp h0_123_hyp (by linarith)) (bn hd22 (fun h => by linarith))
              (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
              -- triple vs singleton (4)
              (bp h123_0_hyp (by linarith)) (bp hd10 (by linarith))
              (bp hd11 (by linarith)) (bp hd12 (by linarith))
              -- pair vs pair (6)
              (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
              (bp hd63 (by linarith)) (bn h12_03_hyp (fun h => by linarith)))
        · -- h123_0=F (1 pat)
          exact fin4_witness sys (11/21) (1/6) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (11/21) (1/6) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              -- ∅ vs singletons (4)
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              -- ∅ vs pairs (6)
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              -- ∅ vs triples (4)
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              -- singleton vs singleton (12)
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bp h21 (by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
              -- singleton vs pair (24)
              (bp h0_12_hyp (by linarith)) (bp hd64 (by linarith))
              (bp hd65 (by linarith))
              (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
              (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith))
              -- pair vs singleton (12)
              (bn hd66 (fun h => by linarith)) (bn hd67 (fun h => by linarith))
              (bn hd68 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
              (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
              (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
              -- singleton vs triple (4)
              (bp h0_123_hyp (by linarith)) (bn hd22 (fun h => by linarith))
              (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
              -- triple vs singleton (4)
              (bn h123_0_hyp (fun h => by linarith)) (bp hd10 (by linarith))
              (bp hd11 (by linarith)) (bp hd12 (by linarith))
              -- pair vs pair (6)
              (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
              (bp hd63 (by linarith)) (bn h12_03_hyp (fun h => by linarith)))
      · -- h0_123=F (2 pat)
        have hd69 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_123_hyp)
        by_cases h12_0_hyp : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h12_0=T (1 pat)
          by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
          · -- h13_0=T
            have hd70 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
              have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
                rw [sys.additive ({1,2,3} : Set _) {0,2},
                    show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                    show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
                exact h13_0_hyp
              have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,1} : Set _) := by
                rw [sys.additive ({0,2} : Set (Fin 4)) {0,1},
                    show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff,
                    show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff]
                exact h21
              have h_s3 := sys.trans _ _ _ h_s1 h_s2
              rw [sys.additive ({1,2,3} : Set _) {0,1},
                  show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
              exact h_s3
            exfalso
            have h_tr := sys.trans _ _ _ h13_0_hyp h0_12_hyp
            rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h_tr
            exact hng32 h_tr
          · -- h13_0=F
            have hd71 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
            exact fin4_witness sys (3/7) (3/14) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (3/7) (3/14) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                -- ∅ vs singletons (4)
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                -- ∅ vs pairs (6)
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                -- ∅ vs triples (4)
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                -- singleton vs singleton (12)
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bp h21 (by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
                -- singleton vs pair (24)
                (bp h0_12_hyp (by linarith)) (bp hd64 (by linarith))
                (bp hd65 (by linarith))
                (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
                (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith))
                -- pair vs singleton (12)
                (bp h12_0_hyp (by linarith)) (bn h13_0_hyp (fun h => by linarith))
                (bn hd71 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
                (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
                (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
                -- singleton vs triple (4)
                (bn h0_123_hyp (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
                -- triple vs singleton (4)
                (bp hd69 (by linarith)) (bp hd10 (by linarith))
                (bp hd11 (by linarith)) (bp hd12 (by linarith))
                -- pair vs pair (6)
                (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
                (bp hd63 (by linarith)) (bn h12_03_hyp (fun h => by linarith)))
        · -- h12_0=F (1 pat)
          have hd72 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
          have hd73 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
          exact fin4_witness sys (19/42) (4/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (19/42) (4/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              -- ∅ vs singletons (4)
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              -- ∅ vs pairs (6)
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              -- ∅ vs triples (4)
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              -- singleton vs singleton (12)
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bp h21 (by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
              -- singleton vs pair (24)
              (bp h0_12_hyp (by linarith)) (bp hd64 (by linarith))
              (bp hd65 (by linarith))
              (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
              (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith))
              -- pair vs singleton (12)
              (bn h12_0_hyp (fun h => by linarith)) (bn hd72 (fun h => by linarith))
              (bn hd73 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
              (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
              (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
              -- singleton vs triple (4)
              (bn h0_123_hyp (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
              -- triple vs singleton (4)
              (bp hd69 (by linarith)) (bp hd10 (by linarith))
              (bp hd11 (by linarith)) (bp hd12 (by linarith))
              -- pair vs pair (6)
              (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
              (bp hd63 (by linarith)) (bn h12_03_hyp (fun h => by linarith)))
    · -- h0_12=F (3 pat)
      have hd74 := nge_superset sys
        (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) h0_12_hyp
      have hd75 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
      have hd76 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd74)
      by_cases h0_13_hyp : sys.ge {(0 : Fin 4)} ({1,3} : Set _)
      · -- h0_13=T (2 pat)
        have hd77 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({2,3} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {2,3},
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
            exact h12
          exact sys.trans _ _ _ h0_13_hyp h_mid
        by_cases h13_0_hyp : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
        · -- h13_0=T (1 pat)
          have hd78 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
            have h_s1 : sys.ge ({1,2,3} : Set _) ({0,2} : Set _) := by
              rw [sys.additive ({1,2,3} : Set _) {0,2},
                  show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
                  show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
              exact h13_0_hyp
            have h_s2 : sys.ge ({0,2} : Set (Fin 4)) ({0,1} : Set _) := by
              rw [sys.additive ({0,2} : Set (Fin 4)) {0,1},
                  show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by sdiff,
                  show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by sdiff]
              exact h21
            have h_s3 := sys.trans _ _ _ h_s1 h_s2
            rw [sys.additive ({1,2,3} : Set _) {0,1},
                show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by sdiff,
                show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
            exact h_s3
          exact fin4_witness sys (8/21) (5/21) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (8/21) (5/21) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              -- ∅ vs singletons (4)
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              -- ∅ vs pairs (6)
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              -- ∅ vs triples (4)
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              -- singleton vs singleton (12)
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bp h21 (by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
              -- singleton vs pair (24)
              (bn h0_12_hyp (fun h => by linarith)) (bp h0_13_hyp (by linarith))
              (bp hd77 (by linarith))
              (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
              (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith))
              -- pair vs singleton (12)
              (bp hd75 (by linarith)) (bp h13_0_hyp (by linarith))
              (bp hd78 (by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
              (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
              (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
              -- singleton vs triple (4)
              (bn hd74 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
              -- triple vs singleton (4)
              (bp hd76 (by linarith)) (bp hd10 (by linarith))
              (bp hd11 (by linarith)) (bp hd12 (by linarith))
              -- pair vs pair (6)
              (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
              (bp hd63 (by linarith)) (bn h12_03_hyp (fun h => by linarith)))
        · -- h13_0=F (1 pat)
          have hd79 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
          exact fin4_witness sys (17/42) (3/14) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (17/42) (3/14) (3/14) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              -- ∅ vs singletons (4)
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              -- ∅ vs pairs (6)
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              -- ∅ vs triples (4)
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              -- singleton vs singleton (12)
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bp h21 (by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
              -- singleton vs pair (24)
              (bn h0_12_hyp (fun h => by linarith)) (bp h0_13_hyp (by linarith))
              (bp hd77 (by linarith))
              (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
              (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith))
              -- pair vs singleton (12)
              (bp hd75 (by linarith)) (bn h13_0_hyp (fun h => by linarith))
              (bn hd79 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
              (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
              (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
              -- singleton vs triple (4)
              (bn hd74 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
              -- triple vs singleton (4)
              (bp hd76 (by linarith)) (bp hd10 (by linarith))
              (bp hd11 (by linarith)) (bp hd12 (by linarith))
              -- pair vs pair (6)
              (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
              (bp hd63 (by linarith)) (bn h12_03_hyp (fun h => by linarith)))
      · -- h0_13=F (1 pat)
        have hd80 : ¬sys.ge {(0 : Fin 4)} ({2,3} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({2,3} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({2,3} : Set (Fin 4)) {1,3},
                show ({2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff]
            exact h21
          exact h0_13_hyp (sys.trans _ _ _ h_assumed h_mid)
        have hd81 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_13_hyp)
        have hd82 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
          (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd80)
        exact fin4_witness sys (13/42) (5/21) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
          hn0 hn1 hn2 hn3
          (fin4_dispatch sys (13/42) (5/21) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
            (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
            (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
            (mf4_univ ..)
            -- ∅ vs singletons (4)
            (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
            (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
            -- ∅ vs pairs (6)
            (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
            (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
            (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
            -- ∅ vs triples (4)
            (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
            (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
            -- singleton vs singleton (12)
            (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
            (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
            (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
            (bp h12 (by linarith)) (bp h21 (by linarith))
            (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
            (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
            -- singleton vs pair (24)
            (bn h0_12_hyp (fun h => by linarith)) (bn h0_13_hyp (fun h => by linarith))
            (bn hd80 (fun h => by linarith))
            (bn hd13 (fun h => by linarith)) (bn hd14 (fun h => by linarith))
            (bn hd15 (fun h => by linarith)) (bn hd16 (fun h => by linarith))
            (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
            (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
            (bn hd21 (fun h => by linarith))
            -- pair vs singleton (12)
            (bp hd75 (by linarith)) (bp hd81 (by linarith))
            (bp hd82 (by linarith))
            (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
            (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
            (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
            -- singleton vs triple (4)
            (bn hd74 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
            (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
            -- triple vs singleton (4)
            (bp hd76 (by linarith)) (bp hd10 (by linarith))
            (bp hd11 (by linarith)) (bp hd12 (by linarith))
            -- pair vs pair (6)
            (bp hd25 (by linarith)) (bn hd27 (fun h => by linarith))
            (bp hd26 (by linarith)) (bn hd28 (fun h => by linarith))
            (bp hd63 (by linarith)) (bn h12_03_hyp (fun h => by linarith)))


end Core.Scale
