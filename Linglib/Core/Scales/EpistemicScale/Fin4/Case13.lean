import Linglib.Core.Scales.EpistemicScale.Fin4.Defs

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000 in
/-- Case (1,3): 5 sub-cases. -/
theorem fin4_case_13 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (hng10 : ¬sys.ge {(1 : Fin 4)} {0})
    (h12 : sys.ge {(1 : Fin 4)} {2})
    (h21 : sys.ge {(2 : Fin 4)} {1})
    (h13 : sys.ge {(1 : Fin 4)} {3})
    (h31 : sys.ge {(3 : Fin 4)} {1})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h32 : sys.ge {(3 : Fin 4)} {2})
    (h02 : sys.ge {(0 : Fin 4)} {2})
    (h03 : sys.ge {(0 : Fin 4)} {3})
    :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  have hng20 : ¬sys.ge {(2 : Fin 4)} {0} := fun h => hng10 (sys.trans _ _ _ h12 h)
  have hng30 : ¬sys.ge {(3 : Fin 4)} {0} := fun h => hng10 (sys.trans _ _ _ h13 h)
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
  have hd13 := nge_singleton_pair sys h01 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd14 := nge_singleton_pair sys h01 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd15 := nge_singleton_pair sys h21 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd16 := nge_singleton_pair sys h02 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd17 := nge_singleton_pair sys h02 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd18 := nge_singleton_pair sys h12 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd19 := nge_singleton_pair sys h03 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd20 := nge_singleton_pair sys h03 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd21 := nge_singleton_pair sys h13 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd22 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hng10
  have hd23 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hng20
  have hd24 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hng30
  have hd25 : sys.ge ({0,1} : Set (Fin 4)) ({2,3} : Set _) := by
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
  have hd26 : sys.ge ({0,2} : Set (Fin 4)) ({1,3} : Set _) := by
    have h1 : sys.ge ({0,2} : Set (Fin 4)) ({0,1} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {0,1},
          show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h21
    have h2 : sys.ge ({0,1} : Set _) ({1,3} : Set _) := by
      rw [sys.additive ({0,1} : Set (Fin 4)) {1,3},
          show ({0,1} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({1,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h03
    exact sys.trans _ _ _ h1 h2
  have hd27 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := by
    have h1 : sys.ge ({0,3} : Set (Fin 4)) ({0,1} : Set _) := by
      rw [sys.additive ({0,3} : Set (Fin 4)) {0,1},
          show ({0,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,1} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h31
    have h2 : sys.ge ({0,1} : Set _) ({1,2} : Set _) := by
      rw [sys.additive ({0,1} : Set (Fin 4)) {1,2},
          show ({0,1} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({1,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h02
    exact sys.trans _ _ _ h1 h2
  have hd28 : ¬sys.ge ({2,3} : Set (Fin 4)) ({0,1} : Set _) := fun h => by
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
  have hd29 : ¬sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) := fun h => by
    have h_bc : sys.ge ({0,2} : Set (Fin 4)) ({0,1} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {0,1},
          show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h21
    have h1 := sys.trans _ _ _ h h_bc
    rw [sys.additive ({1,3} : Set (Fin 4)) {0,1},
        show ({1,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
        show ({0,1} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
    exact hng30 h1
  have hd30 : ¬sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := fun h => by
    have h_bc : sys.ge ({0,3} : Set (Fin 4)) ({0,1} : Set _) := by
      rw [sys.additive ({0,3} : Set (Fin 4)) {0,1},
          show ({0,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,1} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h31
    have h1 := sys.trans _ _ _ h h_bc
    rw [sys.additive ({1,2} : Set (Fin 4)) {0,1},
        show ({1,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
        show ({0,1} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
    exact hng20 h1
  by_cases h0_123_hyp : sys.ge {(0 : Fin 4)} ({1,2,3} : Set _)
  · -- h0_123=T (2 pat)
    have hd31 : ¬sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
      have h1 := sys.trans _ _ _ h h0_123_hyp
      rw [sys.additive ({1,2} : Set (Fin 4)) {1,2,3},
          show ({1,2} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
          show ({1,2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
      exact hn3 h1
    have hd32 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
      have h1 := sys.trans _ _ _ h h0_123_hyp
      rw [sys.additive ({1,3} : Set (Fin 4)) {1,2,3},
          show ({1,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
          show ({1,2,3} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
      exact hn2 h1
    have hd33 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h => by
      have h1 := sys.trans _ _ _ h h0_123_hyp
      rw [sys.additive ({2,3} : Set (Fin 4)) {1,2,3},
          show ({2,3} : Set (Fin 4)) \ {1,2,3} = ∅ from by ext x; fin_cases x <;> simp_all,
          show ({1,2,3} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h1
      exact hn1 h1
    have hd34 : sys.ge {(0 : Fin 4)} ({1,2} : Set _) :=
      (sys.total {(0 : Fin 4)} ({1,2} : Set _)).elim id (fun h => absurd h hd31)
    have hd35 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) :=
      (sys.total {(0 : Fin 4)} ({1,3} : Set _)).elim id (fun h => absurd h hd32)
    have hd36 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) :=
      (sys.total {(0 : Fin 4)} ({2,3} : Set _)).elim id (fun h => absurd h hd33)
    by_cases h123_0_hyp : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)
    · -- h123_0=T (1 pat)
      exact fin4_witness sys (1/2) (1/6) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
        hn0 hn1 hn2 hn3
        (fin4_dispatch sys (1/2) (1/6) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
          ⟨fun _ => by linarith, fun _ => h21⟩
          ⟨fun _ => by linarith, fun _ => h13⟩
          ⟨fun _ => by linarith, fun _ => h31⟩
          ⟨fun _ => by linarith, fun _ => h23⟩
          ⟨fun _ => by linarith, fun _ => h32⟩
          ⟨fun _ => by linarith, fun _ => hd34⟩
          ⟨fun _ => by linarith, fun _ => hd35⟩
          ⟨fun _ => by linarith, fun _ => hd36⟩
          ⟨fun h => absurd h hd13, fun h => by linarith⟩
          ⟨fun h => absurd h hd14, fun h => by linarith⟩
          ⟨fun h => absurd h hd15, fun h => by linarith⟩
          ⟨fun h => absurd h hd16, fun h => by linarith⟩
          ⟨fun h => absurd h hd17, fun h => by linarith⟩
          ⟨fun h => absurd h hd18, fun h => by linarith⟩
          ⟨fun h => absurd h hd19, fun h => by linarith⟩
          ⟨fun h => absurd h hd20, fun h => by linarith⟩
          ⟨fun h => absurd h hd21, fun h => by linarith⟩
          ⟨fun h => absurd h hd31, fun h => by linarith⟩
          ⟨fun h => absurd h hd32, fun h => by linarith⟩
          ⟨fun h => absurd h hd33, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd1⟩
          ⟨fun _ => by linarith, fun _ => hd2⟩
          ⟨fun _ => by linarith, fun _ => hd3⟩
          ⟨fun _ => by linarith, fun _ => hd4⟩
          ⟨fun _ => by linarith, fun _ => hd5⟩
          ⟨fun _ => by linarith, fun _ => hd6⟩
          ⟨fun _ => by linarith, fun _ => hd7⟩
          ⟨fun _ => by linarith, fun _ => hd8⟩
          ⟨fun _ => by linarith, fun _ => hd9⟩
          ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
          ⟨fun h => absurd h hd22, fun h => by linarith⟩
          ⟨fun h => absurd h hd23, fun h => by linarith⟩
          ⟨fun h => absurd h hd24, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => h123_0_hyp⟩
          ⟨fun _ => by linarith, fun _ => hd10⟩
          ⟨fun _ => by linarith, fun _ => hd11⟩
          ⟨fun _ => by linarith, fun _ => hd12⟩
          ⟨fun _ => by linarith, fun _ => hd25⟩
          ⟨fun h => absurd h hd28, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd26⟩
          ⟨fun h => absurd h hd29, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd27⟩
          ⟨fun h => absurd h hd30, fun h => by linarith⟩)
    · -- h123_0=F (1 pat)
      exact fin4_witness sys (4/7) (1/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
        hn0 hn1 hn2 hn3
        (fin4_dispatch sys (4/7) (1/7) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
          ⟨fun _ => by linarith, fun _ => h21⟩
          ⟨fun _ => by linarith, fun _ => h13⟩
          ⟨fun _ => by linarith, fun _ => h31⟩
          ⟨fun _ => by linarith, fun _ => h23⟩
          ⟨fun _ => by linarith, fun _ => h32⟩
          ⟨fun _ => by linarith, fun _ => hd34⟩
          ⟨fun _ => by linarith, fun _ => hd35⟩
          ⟨fun _ => by linarith, fun _ => hd36⟩
          ⟨fun h => absurd h hd13, fun h => by linarith⟩
          ⟨fun h => absurd h hd14, fun h => by linarith⟩
          ⟨fun h => absurd h hd15, fun h => by linarith⟩
          ⟨fun h => absurd h hd16, fun h => by linarith⟩
          ⟨fun h => absurd h hd17, fun h => by linarith⟩
          ⟨fun h => absurd h hd18, fun h => by linarith⟩
          ⟨fun h => absurd h hd19, fun h => by linarith⟩
          ⟨fun h => absurd h hd20, fun h => by linarith⟩
          ⟨fun h => absurd h hd21, fun h => by linarith⟩
          ⟨fun h => absurd h hd31, fun h => by linarith⟩
          ⟨fun h => absurd h hd32, fun h => by linarith⟩
          ⟨fun h => absurd h hd33, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd1⟩
          ⟨fun _ => by linarith, fun _ => hd2⟩
          ⟨fun _ => by linarith, fun _ => hd3⟩
          ⟨fun _ => by linarith, fun _ => hd4⟩
          ⟨fun _ => by linarith, fun _ => hd5⟩
          ⟨fun _ => by linarith, fun _ => hd6⟩
          ⟨fun _ => by linarith, fun _ => hd7⟩
          ⟨fun _ => by linarith, fun _ => hd8⟩
          ⟨fun _ => by linarith, fun _ => hd9⟩
          ⟨fun _ => by linarith, fun _ => h0_123_hyp⟩
          ⟨fun h => absurd h hd22, fun h => by linarith⟩
          ⟨fun h => absurd h hd23, fun h => by linarith⟩
          ⟨fun h => absurd h hd24, fun h => by linarith⟩
          ⟨fun h => absurd h h123_0_hyp, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd10⟩
          ⟨fun _ => by linarith, fun _ => hd11⟩
          ⟨fun _ => by linarith, fun _ => hd12⟩
          ⟨fun _ => by linarith, fun _ => hd25⟩
          ⟨fun h => absurd h hd28, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd26⟩
          ⟨fun h => absurd h hd29, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd27⟩
          ⟨fun h => absurd h hd30, fun h => by linarith⟩)
  · -- h0_123=F (3 pat)
    have hd37 : sys.ge ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _) :=
      (sys.total ({1,2,3} : Set _) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_123_hyp)
    by_cases h0_12_hyp : sys.ge {(0 : Fin 4)} ({1,2} : Set _)
    · -- h0_12=T (2 pat)
      have hd38 : sys.ge {(0 : Fin 4)} ({1,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({1,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {1,3},
              show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
              show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
          exact h23
        exact sys.trans _ _ _ h0_12_hyp h_mid
      have hd39 : sys.ge {(0 : Fin 4)} ({2,3} : Set _) := by
        have h_mid : sys.ge ({1,2} : Set (Fin 4)) ({2,3} : Set _) := by
          rw [sys.additive ({1,2} : Set (Fin 4)) {2,3},
              show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
              show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
          exact h13
        exact sys.trans _ _ _ h0_12_hyp h_mid
      by_cases h12_0_hyp : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
      · -- h12_0=T (1 pat)
        have hd40 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
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
        have hd41 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := by
          have h_s1 : sys.ge ({1,2,3} : Set _) ({0,3} : Set _) := by
            rw [sys.additive ({1,2,3} : Set _) {0,3},
                show ({1,2,3} : Set _) \ {0,3} = ({1,2} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
                show ({0,3} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h12_0_hyp
          have h_s2 : sys.ge ({0,3} : Set (Fin 4)) ({0,1} : Set _) := by
            rw [sys.additive ({0,3} : Set (Fin 4)) {0,1},
                show ({0,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
                show ({0,1} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
            exact h31
          have h_s3 := sys.trans _ _ _ h_s1 h_s2
          rw [sys.additive ({1,2,3} : Set _) {0,1},
              show ({1,2,3} : Set _) \ {0,1} = ({2,3} : Set (Fin 4)) from by ext x; fin_cases x <;> simp_all,
              show ({0,1} : Set (Fin 4)) \ {1,2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all] at h_s3
          exact h_s3
        exact fin4_witness sys (2/5) (1/5) (1/5) (by linarith) (by linarith) (by linarith) (by linarith)
          hn0 hn1 hn2 hn3
          (fin4_dispatch sys (2/5) (1/5) (1/5) (by linarith) (by linarith) (by linarith) (by linarith)
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
            ⟨fun _ => by linarith, fun _ => h21⟩
            ⟨fun _ => by linarith, fun _ => h13⟩
            ⟨fun _ => by linarith, fun _ => h31⟩
            ⟨fun _ => by linarith, fun _ => h23⟩
            ⟨fun _ => by linarith, fun _ => h32⟩
            ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
            ⟨fun _ => by linarith, fun _ => hd38⟩
            ⟨fun _ => by linarith, fun _ => hd39⟩
            ⟨fun h => absurd h hd13, fun h => by linarith⟩
            ⟨fun h => absurd h hd14, fun h => by linarith⟩
            ⟨fun h => absurd h hd15, fun h => by linarith⟩
            ⟨fun h => absurd h hd16, fun h => by linarith⟩
            ⟨fun h => absurd h hd17, fun h => by linarith⟩
            ⟨fun h => absurd h hd18, fun h => by linarith⟩
            ⟨fun h => absurd h hd19, fun h => by linarith⟩
            ⟨fun h => absurd h hd20, fun h => by linarith⟩
            ⟨fun h => absurd h hd21, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h12_0_hyp⟩
            ⟨fun _ => by linarith, fun _ => hd40⟩
            ⟨fun _ => by linarith, fun _ => hd41⟩
            ⟨fun _ => by linarith, fun _ => hd1⟩
            ⟨fun _ => by linarith, fun _ => hd2⟩
            ⟨fun _ => by linarith, fun _ => hd3⟩
            ⟨fun _ => by linarith, fun _ => hd4⟩
            ⟨fun _ => by linarith, fun _ => hd5⟩
            ⟨fun _ => by linarith, fun _ => hd6⟩
            ⟨fun _ => by linarith, fun _ => hd7⟩
            ⟨fun _ => by linarith, fun _ => hd8⟩
            ⟨fun _ => by linarith, fun _ => hd9⟩
            ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
            ⟨fun h => absurd h hd22, fun h => by linarith⟩
            ⟨fun h => absurd h hd23, fun h => by linarith⟩
            ⟨fun h => absurd h hd24, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd37⟩
            ⟨fun _ => by linarith, fun _ => hd10⟩
            ⟨fun _ => by linarith, fun _ => hd11⟩
            ⟨fun _ => by linarith, fun _ => hd12⟩
            ⟨fun _ => by linarith, fun _ => hd25⟩
            ⟨fun h => absurd h hd28, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd26⟩
            ⟨fun h => absurd h hd29, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd27⟩
            ⟨fun h => absurd h hd30, fun h => by linarith⟩)
      · -- h12_0=F (1 pat)
        have hd42 : ¬sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
        have hd43 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) := fun h_assumed => by
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
        exact fin4_witness sys (3/7) (4/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
          hn0 hn1 hn2 hn3
          (fin4_dispatch sys (3/7) (4/21) (4/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
            ⟨fun _ => by linarith, fun _ => h21⟩
            ⟨fun _ => by linarith, fun _ => h13⟩
            ⟨fun _ => by linarith, fun _ => h31⟩
            ⟨fun _ => by linarith, fun _ => h23⟩
            ⟨fun _ => by linarith, fun _ => h32⟩
            ⟨fun _ => by linarith, fun _ => h0_12_hyp⟩
            ⟨fun _ => by linarith, fun _ => hd38⟩
            ⟨fun _ => by linarith, fun _ => hd39⟩
            ⟨fun h => absurd h hd13, fun h => by linarith⟩
            ⟨fun h => absurd h hd14, fun h => by linarith⟩
            ⟨fun h => absurd h hd15, fun h => by linarith⟩
            ⟨fun h => absurd h hd16, fun h => by linarith⟩
            ⟨fun h => absurd h hd17, fun h => by linarith⟩
            ⟨fun h => absurd h hd18, fun h => by linarith⟩
            ⟨fun h => absurd h hd19, fun h => by linarith⟩
            ⟨fun h => absurd h hd20, fun h => by linarith⟩
            ⟨fun h => absurd h hd21, fun h => by linarith⟩
            ⟨fun h => absurd h h12_0_hyp, fun h => by linarith⟩
            ⟨fun h => absurd h hd42, fun h => by linarith⟩
            ⟨fun h => absurd h hd43, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd1⟩
            ⟨fun _ => by linarith, fun _ => hd2⟩
            ⟨fun _ => by linarith, fun _ => hd3⟩
            ⟨fun _ => by linarith, fun _ => hd4⟩
            ⟨fun _ => by linarith, fun _ => hd5⟩
            ⟨fun _ => by linarith, fun _ => hd6⟩
            ⟨fun _ => by linarith, fun _ => hd7⟩
            ⟨fun _ => by linarith, fun _ => hd8⟩
            ⟨fun _ => by linarith, fun _ => hd9⟩
            ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
            ⟨fun h => absurd h hd22, fun h => by linarith⟩
            ⟨fun h => absurd h hd23, fun h => by linarith⟩
            ⟨fun h => absurd h hd24, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd37⟩
            ⟨fun _ => by linarith, fun _ => hd10⟩
            ⟨fun _ => by linarith, fun _ => hd11⟩
            ⟨fun _ => by linarith, fun _ => hd12⟩
            ⟨fun _ => by linarith, fun _ => hd25⟩
            ⟨fun h => absurd h hd28, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd26⟩
            ⟨fun h => absurd h hd29, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hd27⟩
            ⟨fun h => absurd h hd30, fun h => by linarith⟩)
    · -- h0_12=F (1 pat)
      have hd44 : ¬sys.ge {(0 : Fin 4)} ({1,3} : Set _) := fun h_assumed => by
        have h_mid : sys.ge ({1,3} : Set (Fin 4)) ({1,2} : Set _) := by
          rw [sys.additive ({1,3} : Set (Fin 4)) {1,2},
              show ({1,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
              show ({1,2} : Set (Fin 4)) \ {1,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
          exact h32
        exact h0_12_hyp (sys.trans _ _ _ h_assumed h_mid)
      have hd45 : ¬sys.ge {(0 : Fin 4)} ({2,3} : Set _) := fun h_assumed => by
        have h_mid : sys.ge ({2,3} : Set (Fin 4)) ({1,2} : Set _) := by
          rw [sys.additive ({2,3} : Set (Fin 4)) {1,2},
              show ({2,3} : Set (Fin 4)) \ {1,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
              show ({1,2} : Set (Fin 4)) \ {2,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
          exact h31
        exact h0_12_hyp (sys.trans _ _ _ h_assumed h_mid)
      have hd46 : sys.ge ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({1,2} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_12_hyp)
      have hd47 : sys.ge ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({1,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd44)
      have hd48 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
        (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h hd45)
      exact fin4_witness sys (2/7) (5/21) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
        hn0 hn1 hn2 hn3
        (fin4_dispatch sys (2/7) (5/21) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
          ⟨fun _ => by linarith, fun _ => h21⟩
          ⟨fun _ => by linarith, fun _ => h13⟩
          ⟨fun _ => by linarith, fun _ => h31⟩
          ⟨fun _ => by linarith, fun _ => h23⟩
          ⟨fun _ => by linarith, fun _ => h32⟩
          ⟨fun h => absurd h h0_12_hyp, fun h => by linarith⟩
          ⟨fun h => absurd h hd44, fun h => by linarith⟩
          ⟨fun h => absurd h hd45, fun h => by linarith⟩
          ⟨fun h => absurd h hd13, fun h => by linarith⟩
          ⟨fun h => absurd h hd14, fun h => by linarith⟩
          ⟨fun h => absurd h hd15, fun h => by linarith⟩
          ⟨fun h => absurd h hd16, fun h => by linarith⟩
          ⟨fun h => absurd h hd17, fun h => by linarith⟩
          ⟨fun h => absurd h hd18, fun h => by linarith⟩
          ⟨fun h => absurd h hd19, fun h => by linarith⟩
          ⟨fun h => absurd h hd20, fun h => by linarith⟩
          ⟨fun h => absurd h hd21, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd46⟩
          ⟨fun _ => by linarith, fun _ => hd47⟩
          ⟨fun _ => by linarith, fun _ => hd48⟩
          ⟨fun _ => by linarith, fun _ => hd1⟩
          ⟨fun _ => by linarith, fun _ => hd2⟩
          ⟨fun _ => by linarith, fun _ => hd3⟩
          ⟨fun _ => by linarith, fun _ => hd4⟩
          ⟨fun _ => by linarith, fun _ => hd5⟩
          ⟨fun _ => by linarith, fun _ => hd6⟩
          ⟨fun _ => by linarith, fun _ => hd7⟩
          ⟨fun _ => by linarith, fun _ => hd8⟩
          ⟨fun _ => by linarith, fun _ => hd9⟩
          ⟨fun h => absurd h h0_123_hyp, fun h => by linarith⟩
          ⟨fun h => absurd h hd22, fun h => by linarith⟩
          ⟨fun h => absurd h hd23, fun h => by linarith⟩
          ⟨fun h => absurd h hd24, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd37⟩
          ⟨fun _ => by linarith, fun _ => hd10⟩
          ⟨fun _ => by linarith, fun _ => hd11⟩
          ⟨fun _ => by linarith, fun _ => hd12⟩
          ⟨fun _ => by linarith, fun _ => hd25⟩
          ⟨fun h => absurd h hd28, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd26⟩
          ⟨fun h => absurd h hd29, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd27⟩
          ⟨fun h => absurd h hd30, fun h => by linarith⟩)


end Core.Scale
