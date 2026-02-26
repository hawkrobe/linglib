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
  have hd12 := nge_singleton_pair sys h01 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd13 := nge_singleton_pair sys h01 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd14 := nge_singleton_pair sys h02 hn1 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd15 := nge_singleton_pair sys h02 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd16 := nge_singleton_pair sys h12 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd17 := nge_singleton_pair sys h03 hn1 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd18 := nge_singleton_pair sys h03 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd19 := nge_singleton_pair sys h13 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd20 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hng10
  have hd21 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hng20
  have hd22 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hng30
  have hd23 := ge_pair_via_mid sys ({0,1} : Set _) ({2,3} : Set _) ({0,2} : Set _)
    h12 h03 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd24 := ge_pair_via_mid sys ({0,2} : Set _) ({1,3} : Set _) ({0,3} : Set _)
    h23 h01 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd25 := ge_pair_via_mid sys ({0,3} : Set _) ({1,2} : Set _) ({0,2} : Set _)
    h32 h01 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd26 := nge_pair_via_contra sys ({2,3} : Set _) ({0,1} : Set _) ({0,2} : Set _)
    h12 hng30 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd27 := nge_pair_via_contra sys ({1,3} : Set _) ({0,2} : Set _) ({0,3} : Set _)
    h23 hng10 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd28 := nge_pair_via_contra sys ({1,2} : Set _) ({0,3} : Set _) ({0,2} : Set _)
    h32 hng10 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  by_cases h12_0_hyp : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
  · -- h12_0=T (8 pat)
    have hd29 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
      have h_s1 : sys.ge ({1,2,3} : Set _) ({0,3} : Set _) := by
        rw [sys.additive ({1,2,3} : Set _) {0,3},
            show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by sdiff,
            show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff]
        exact h12_0_hyp
      have h_s2 : sys.ge ({0,3} : Set (Fin 4)) ({0,2} : Set _) := by
        rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
            show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by sdiff,
            show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by sdiff]
        exact h32
      have h_s3 := sys.trans _ _ _ h_s1 h_s2
      rw [sys.additive ({1,2,3} : Set _) {0,2},
          show ({1,2,3} : Set _) \ {0,2} = ({1,3} : Set (Fin 4)) from by sdiff,
          show ({0,2} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by sdiff] at h_s3
      exact h_s3
    by_cases h1_23_hyp : sys.ge {(1 : Fin 4)} ({2,3} : Set _)
    · -- h1_23=T (4 pat)
      have hd30 := sys.trans _ _ _ h01 h1_23_hyp
      by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
      · -- h0_12=T (2 pat)
        have hd31 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
          have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
            rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
            exact h23
          exact sys.trans _ _ _ h0_12_hyp h_mid
        by_cases h23_1_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)
        · -- h23_1=T (1 pat)
          by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
          · -- h23_0=T
            have hd32 := sys.trans _ _ _ h1_23_hyp h23_0_hyp
            have hd33 := nge_singleton_pair sys hd32 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
            have hd34 := nge_singleton_pair sys hd32 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
            have hd35 := nge_superset sys
              (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd33
            have hd36 := ge_pair_via_mid sys ({1,3} : Set _) ({0,2} : Set _) ({0,3} : Set _)
              hd32 h32 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
            have hd37 := ge_pair_via_mid sys ({1,2} : Set _) ({0,3} : Set _) ({0,2} : Set _)
              hd32 h23 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
            have hd38 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
              (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd35)
            exact absurd h0_12_hyp hd33
          · -- h23_0=F
            by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
            · -- h0_123=T
              have hd39 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
                have h1 := sys.trans _ _ _ h h0_123_hyp
                rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
                    show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
                    show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff] at h1
                exact hn3 h1
              have hd40 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
                have h1 := sys.trans _ _ _ h h0_123_hyp
                rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
                    show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
                    show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h1
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
                  (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                  (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                  (bp h23 (by linarith)) (bp h32 (by linarith))
                  -- singleton vs pair (24)
                  (bp h0_12_hyp (by linarith)) (bp hd31 (by linarith))
                  (bp hd30 (by linarith))
                  (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                  (bp h1_23_hyp (by linarith))
                  (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                  (bn hd16 (fun h => by linarith))
                  (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                  (bn hd19 (fun h => by linarith))
                  -- pair vs singleton (12)
                  (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
                  (bn h23_0_hyp (fun h => by linarith))
                  (bp hd1 (by linarith)) (bp hd2 (by linarith))
                  (bp h23_1_hyp (by linarith))
                  (bp hd3 (by linarith)) (bp hd4 (by linarith))
                  (bp hd5 (by linarith))
                  (bp hd6 (by linarith)) (bp hd7 (by linarith))
                  (bp hd8 (by linarith))
                  -- singleton vs triple (8)
                  (bn h0_123_hyp (fun h => by linarith))
                  (bn hd20 (fun h => by linarith))
                  (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                  (bp hd41 (by linarith))
                  (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                  -- pair vs pair (6)
                  (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                  (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                  (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
        · -- h23_1=F (1 pat)
          have hd42 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
            fun h => h23_1_hyp (sys.trans _ _ _ h h01)
          by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
          · -- h0_123=T
            have hd43 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
                  show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
                  show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff] at h1
              exact hn3 h1
            have hd44 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
                  show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
                  show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h1
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bp h0_12_hyp (by linarith)) (bp hd31 (by linarith))
                (bp hd30 (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bp h1_23_hyp (by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
                (bn hd42 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bn h23_1_hyp (fun h => by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bn h0_123_hyp (fun h => by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd45 (by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
      · -- h0_12=F (2 pat)
        have hd46 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
          have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
            rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
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
            have hd50 := ge_pair_via_mid sys ({1,3} : Set _) ({0,2} : Set _) ({0,3} : Set _)
              hd49 h32 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
            have hd51 := ge_pair_via_mid sys ({1,2} : Set _) ({0,3} : Set _) ({0,2} : Set _)
              hd49 h23 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bn h0_12_hyp (fun h => by linarith)) (bn hd46 (fun h => by linarith))
                (bp hd30 (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bp h1_23_hyp (by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
                (bn h23_0_hyp (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bp h23_1_hyp (by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bn hd47 (fun h => by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd48 (by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
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
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bp h32 (by linarith))
              (bn h0_12_hyp (fun h => by linarith)) (bn hd46 (fun h => by linarith))
              (bp hd30 (by linarith))
              (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
              (bp h1_23_hyp (by linarith))
              (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
              (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith))
              (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
              (bn hd52 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith))
              (bn h23_1_hyp (fun h => by linarith))
              (bp hd3 (by linarith)) (bp hd4 (by linarith))
              (bp hd5 (by linarith))
              (bp hd6 (by linarith)) (bp hd7 (by linarith))
              (bp hd8 (by linarith))
              (bn hd47 (fun h => by linarith))
              (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bp hd48 (by linarith))
              (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
              (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
              (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
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
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
                exact h23
              exact sys.trans _ _ _ h0_12_hyp h_mid
            exfalso
            have h_tr := sys.trans _ _ _ h23_0_hyp h0_12_hyp
            rw [sys.additive ({2,3} : Set (Fin 4)) {1,2},
                show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff] at h_tr
            exact hng31 h_tr
          · -- h0_12=F
            have hd55 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
              have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
                rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                    show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                    show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bn h0_12_hyp (fun h => by linarith)) (bn hd55 (fun h => by linarith))
                (bp h0_23_hyp (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bn h1_23_hyp (fun h => by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
                (bp h23_0_hyp (by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bp hd53 (by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bn hd56 (fun h => by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd57 (by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
        · -- h0_23=F (1 pat)
          have hd58 : ¬sys.ge {(0 : Fin 4)} ({1,2} : Set _) := fun h_assumed => by
            have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({2,3} : Set _) := by
              rw [sys.additive ({1,2} : Set (Fin 4)) {2,3},
                  show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by sdiff,
                  show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
              exact h13
            exact h0_23_hyp (sys.trans _ _ _ h_assumed h_mid)
          have hd59 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
            have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
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
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bp h32 (by linarith))
              (bn hd58 (fun h => by linarith)) (bn hd59 (fun h => by linarith))
              (bn h0_23_hyp (fun h => by linarith))
              (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
              (bn h1_23_hyp (fun h => by linarith))
              (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
              (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith))
              (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
              (bp h23_0_hyp (by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith))
              (bp hd53 (by linarith))
              (bp hd3 (by linarith)) (bp hd4 (by linarith))
              (bp hd5 (by linarith))
              (bp hd6 (by linarith)) (bp hd7 (by linarith))
              (bp hd8 (by linarith))
              (bn hd60 (fun h => by linarith))
              (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bp hd61 (by linarith))
              (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
              (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
              (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
      · -- h23_0=F (2 pat)
        have hd62 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) :=
          (sys.total {(0 : Fin 4)} ({2,3} : Set _)).elim id (fun h => absurd h h23_0_hyp)
        by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
        · -- h0_12=T (1 pat)
          have hd63 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
            have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
              rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff,
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff]
              exact h23
            exact sys.trans _ _ _ h0_12_hyp h_mid
          by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
          · -- h0_123=T
            have hd64 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
                  show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
                  show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff] at h1
              exact hn3 h1
            have hd65 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
              have h1 := sys.trans _ _ _ h h0_123_hyp
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
                  show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by sdiff,
                  show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff] at h1
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bp h0_12_hyp (by linarith)) (bp hd63 (by linarith))
                (bp hd62 (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bn h1_23_hyp (fun h => by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
                (bn h23_0_hyp (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bp hd53 (by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bn h0_123_hyp (fun h => by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp hd66 (by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
        · -- h0_12=F (1 pat)
          have hd67 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
            have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
              rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
                  show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by sdiff,
                  show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by sdiff]
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
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bp h32 (by linarith))
              (bn h0_12_hyp (fun h => by linarith)) (bn hd67 (fun h => by linarith))
              (bp hd62 (by linarith))
              (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
              (bn h1_23_hyp (fun h => by linarith))
              (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
              (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith))
              (bp h12_0_hyp (by linarith)) (bp hd29 (by linarith))
              (bn h23_0_hyp (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith))
              (bp hd53 (by linarith))
              (bp hd3 (by linarith)) (bp hd4 (by linarith))
              (bp hd5 (by linarith))
              (bp hd6 (by linarith)) (bp hd7 (by linarith))
              (bp hd8 (by linarith))
              (bn hd68 (fun h => by linarith))
              (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bp hd69 (by linarith))
              (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
              (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
              (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
  · -- h12_0=F (9 pat)
    have hd70 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
    have hd71 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bp hd72 (by linarith)) (bp hd73 (by linarith))
                (bp hd74 (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bp h1_23_hyp (by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
                (bn hd71 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bp h23_1_hyp (by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bp h0_123_hyp (by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp h123_0_hyp (by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
          · -- h23_1=F (1 pat)
            exact fin4_witness sys (1/2) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (1/2) (11/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bp hd72 (by linarith)) (bp hd73 (by linarith))
                (bp hd74 (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bp h1_23_hyp (by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
                (bn hd71 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bn h23_1_hyp (fun h => by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bp h0_123_hyp (by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bp h123_0_hyp (by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
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
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bp h32 (by linarith))
              (bp hd72 (by linarith)) (bp hd73 (by linarith))
              (bp hd74 (by linarith))
              (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
              (bn h1_23_hyp (fun h => by linarith))
              (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
              (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith))
              (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
              (bn hd71 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith))
              (bp hd75 (by linarith))
              (bp hd3 (by linarith)) (bp hd4 (by linarith))
              (bp hd5 (by linarith))
              (bp hd6 (by linarith)) (bp hd7 (by linarith))
              (bp hd8 (by linarith))
              (bp h0_123_hyp (by linarith))
              (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bp h123_0_hyp (by linarith))
              (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
              (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
              (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
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
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bp hd72 (by linarith)) (bp hd73 (by linarith))
                (bp hd74 (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bp h1_23_hyp (by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
                (bn hd71 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bp h23_1_hyp (by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bp h0_123_hyp (by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn h123_0_hyp (fun h => by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
          · -- h23_1=F (1 pat)
            exact fin4_witness sys (11/21) (2/7) (2/21) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (fin4_dispatch sys (11/21) (2/7) (2/21) (by linarith) (by linarith) (by linarith) (by linarith)
                hn0 hn1 hn2 hn3
                (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
                (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
                (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
                (mf4_univ ..)
                (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
                (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
                (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
                (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
                (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
                (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
                (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
                (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
                (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
                (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
                (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
                (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
                (bp h23 (by linarith)) (bp h32 (by linarith))
                (bp hd72 (by linarith)) (bp hd73 (by linarith))
                (bp hd74 (by linarith))
                (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
                (bp h1_23_hyp (by linarith))
                (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
                (bn hd16 (fun h => by linarith))
                (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
                (bn hd19 (fun h => by linarith))
                (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
                (bn hd71 (fun h => by linarith))
                (bp hd1 (by linarith)) (bp hd2 (by linarith))
                (bn h23_1_hyp (fun h => by linarith))
                (bp hd3 (by linarith)) (bp hd4 (by linarith))
                (bp hd5 (by linarith))
                (bp hd6 (by linarith)) (bp hd7 (by linarith))
                (bp hd8 (by linarith))
                (bp h0_123_hyp (by linarith))
                (bn hd20 (fun h => by linarith))
                (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
                (bn h123_0_hyp (fun h => by linarith))
                (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
                (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
                (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
                (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
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
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bp h32 (by linarith))
              (bp hd72 (by linarith)) (bp hd73 (by linarith))
              (bp hd74 (by linarith))
              (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
              (bn h1_23_hyp (fun h => by linarith))
              (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
              (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith))
              (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
              (bn hd71 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith))
              (bp hd76 (by linarith))
              (bp hd3 (by linarith)) (bp hd4 (by linarith))
              (bp hd5 (by linarith))
              (bp hd6 (by linarith)) (bp hd7 (by linarith))
              (bp hd8 (by linarith))
              (bp h0_123_hyp (by linarith))
              (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bn h123_0_hyp (fun h => by linarith))
              (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
              (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
              (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
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
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bp h32 (by linarith))
              (bp hd72 (by linarith)) (bp hd73 (by linarith))
              (bp hd74 (by linarith))
              (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
              (bp h1_23_hyp (by linarith))
              (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
              (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith))
              (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
              (bn hd71 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith))
              (bp h23_1_hyp (by linarith))
              (bp hd3 (by linarith)) (bp hd4 (by linarith))
              (bp hd5 (by linarith))
              (bp hd6 (by linarith)) (bp hd7 (by linarith))
              (bp hd8 (by linarith))
              (bn h0_123_hyp (fun h => by linarith))
              (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bp hd77 (by linarith))
              (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
              (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
              (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
        · -- h23_1=F (1 pat)
          exact fin4_witness sys (19/42) (13/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
            hn0 hn1 hn2 hn3
            (fin4_dispatch sys (19/42) (13/42) (5/42) (by linarith) (by linarith) (by linarith) (by linarith)
              hn0 hn1 hn2 hn3
              (mf4_empty ..) (mf4_s0 ..) (mf4_s1 ..) (mf4_s2 ..) (mf4_s3 ..)
              (mf4_p01 ..) (mf4_p02 ..) (mf4_p03 ..) (mf4_p12 ..) (mf4_p13 ..) (mf4_p23 ..)
              (mf4_t012 ..) (mf4_t013 ..) (mf4_t023 ..) (mf4_t123 ..)
              (mf4_univ ..)
              (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
              (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
              (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
              (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
              (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
              (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
              (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
              (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
              (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
              (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
              (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
              (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
              (bp h23 (by linarith)) (bp h32 (by linarith))
              (bp hd72 (by linarith)) (bp hd73 (by linarith))
              (bp hd74 (by linarith))
              (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
              (bp h1_23_hyp (by linarith))
              (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
              (bn hd16 (fun h => by linarith))
              (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
              (bn hd19 (fun h => by linarith))
              (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
              (bn hd71 (fun h => by linarith))
              (bp hd1 (by linarith)) (bp hd2 (by linarith))
              (bn h23_1_hyp (fun h => by linarith))
              (bp hd3 (by linarith)) (bp hd4 (by linarith))
              (bp hd5 (by linarith))
              (bp hd6 (by linarith)) (bp hd7 (by linarith))
              (bp hd8 (by linarith))
              (bn h0_123_hyp (fun h => by linarith))
              (bn hd20 (fun h => by linarith))
              (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
              (bp hd77 (by linarith))
              (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
              (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
              (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
              (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))
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
            (bn hn0 (fun h => by linarith)) (bn hn1 (fun h => by linarith))
            (bn hn2 (fun h => by linarith)) (bn hn3 (fun h => by linarith))
            (bn hne01 (fun h => by linarith)) (bn hne02 (fun h => by linarith))
            (bn hne03 (fun h => by linarith)) (bn hne12 (fun h => by linarith))
            (bn hne13 (fun h => by linarith)) (bn hne23 (fun h => by linarith))
            (bn hne012 (fun h => by linarith)) (bn hne013 (fun h => by linarith))
            (bn hne023 (fun h => by linarith)) (bn hne123 (fun h => by linarith))
            (bp h01 (by linarith)) (bn hng10 (fun h => by linarith))
            (bp h02 (by linarith)) (bn hng20 (fun h => by linarith))
            (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
            (bp h12 (by linarith)) (bn hng21 (fun h => by linarith))
            (bp h13 (by linarith)) (bn hng31 (fun h => by linarith))
            (bp h23 (by linarith)) (bp h32 (by linarith))
            (bp hd72 (by linarith)) (bp hd73 (by linarith))
            (bp hd74 (by linarith))
            (bn hd12 (fun h => by linarith)) (bn hd13 (fun h => by linarith))
            (bn h1_23_hyp (fun h => by linarith))
            (bn hd14 (fun h => by linarith)) (bn hd15 (fun h => by linarith))
            (bn hd16 (fun h => by linarith))
            (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
            (bn hd19 (fun h => by linarith))
            (bn h12_0_hyp (fun h => by linarith)) (bn hd70 (fun h => by linarith))
            (bn hd71 (fun h => by linarith))
            (bp hd1 (by linarith)) (bp hd2 (by linarith))
            (bp hd78 (by linarith))
            (bp hd3 (by linarith)) (bp hd4 (by linarith))
            (bp hd5 (by linarith))
            (bp hd6 (by linarith)) (bp hd7 (by linarith))
            (bp hd8 (by linarith))
            (bn h0_123_hyp (fun h => by linarith))
            (bn hd20 (fun h => by linarith))
            (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
            (bp hd77 (by linarith))
            (bp hd9 (by linarith)) (bp hd10 (by linarith)) (bp hd11 (by linarith))
            (bp hd23 (by linarith)) (bn hd26 (fun h => by linarith))
            (bp hd24 (by linarith)) (bn hd27 (fun h => by linarith))
            (bp hd25 (by linarith)) (bn hd28 (fun h => by linarith)))


end Core.Scale
