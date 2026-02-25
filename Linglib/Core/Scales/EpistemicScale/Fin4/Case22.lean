import Linglib.Core.Scales.EpistemicScale.Fin4.Defs

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000 in
/-- Case (2,2): 3 sub-cases. -/
theorem fin4_case_22 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (h10 : sys.ge {(1 : Fin 4)} {0})
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
  have hd1 := ge_superset sys (show (1:Fin 4) ∈ ({1,2}:Set _) from Or.inl rfl) h10
  have hd2 := ge_superset sys (show (1:Fin 4) ∈ ({1,3}:Set _) from Or.inl rfl) h10
  have hd3 := ge_superset sys (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl) h01
  have hd4 := ge_superset sys (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl) h01
  have hd5 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h02
  have hd6 := ge_superset sys (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl) h02
  have hd7 := ge_superset sys (show (1:Fin 4) ∈ ({1,3}:Set _) from Or.inl rfl) h12
  have hd8 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h03
  have hd9 := ge_superset sys (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl) h03
  have hd10 := ge_superset sys (show (1:Fin 4) ∈ ({1,2}:Set _) from Or.inl rfl) h13
  have hd11 := ge_superset sys (show (1:Fin 4) ∈ ({1,2,3}:Set _) from Or.inl rfl) h10
  have hd12 := ge_superset sys (show (0:Fin 4) ∈ ({0,2,3}:Set _) from Or.inl rfl) h01
  have hd13 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,3}:Set _) from Or.inl rfl) h02
  have hd14 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,2}:Set _) from Or.inl rfl) h03
  have hd15 := nge_singleton_pair sys h10 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd16 := nge_singleton_pair sys h10 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd17 := nge_singleton_pair sys h01 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd18 := nge_singleton_pair sys h01 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd19 := nge_singleton_pair sys h02 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd20 := nge_singleton_pair sys h02 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd21 := nge_singleton_pair sys h12 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd22 := nge_singleton_pair sys h03 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd23 := nge_singleton_pair sys h03 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd24 := nge_singleton_pair sys h13 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd25 := nge_superset sys
    (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd15
  have hd26 := nge_superset sys
    (show ({0,2}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hd17
  have hd27 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hng20
  have hd28 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hng30
  have hd29 : sys.ge ({0,1} : Set (Fin 4)) ({2,3} : Set _) := by
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
  have hd30 : sys.ge ({0,2} : Set (Fin 4)) ({1,3} : Set _) := by
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
  have hd31 : sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) := by
    have h1 : sys.ge ({1,3} : Set (Fin 4)) ({0,3} : Set _) := by
      rw [sys.additive ({1,3} : Set (Fin 4)) {0,3},
          show ({1,3} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,3} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h10
    have h2 : sys.ge ({0,3} : Set _) ({0,2} : Set _) := by
      rw [sys.additive ({0,3} : Set (Fin 4)) {0,2},
          show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h32
    exact sys.trans _ _ _ h1 h2
  have hd32 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := by
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
  have hd33 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := by
    have h1 : sys.ge ({1,2} : Set (Fin 4)) ({0,2} : Set _) := by
      rw [sys.additive ({1,2} : Set (Fin 4)) {0,2},
          show ({1,2} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h10
    have h2 : sys.ge ({0,2} : Set _) ({0,3} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {0,3},
          show ({0,2} : Set (Fin 4)) \ {0,3} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h23
    exact sys.trans _ _ _ h1 h2
  have hd34 : ¬sys.ge ({2,3} : Set (Fin 4)) ({0,1} : Set _) := fun h => by
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
  by_cases h0_23_hyp : sys.ge {(0 : Fin 4)} ({2,3} : Set _)
  · -- h0_23=T (2 pat)
    have hd35 := sys.trans _ _ _ h10 h0_23_hyp
    by_cases h23_0_hyp : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)
    · -- h23_0=T (1 pat)
      have hd36 := sys.trans _ _ _ h23_0_hyp h01
      exact fin4_witness sys (1/3) (1/3) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
        hn0 hn1 hn2 hn3
        (fin4_dispatch sys (1/3) (1/3) (1/6) (by linarith) (by linarith) (by linarith) (by linarith)
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
          ⟨fun _ => by linarith, fun _ => h10⟩
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
          ⟨fun h => absurd h hd15, fun h => by linarith⟩
          ⟨fun h => absurd h hd16, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => h0_23_hyp⟩
          ⟨fun h => absurd h hd17, fun h => by linarith⟩
          ⟨fun h => absurd h hd18, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd35⟩
          ⟨fun h => absurd h hd19, fun h => by linarith⟩
          ⟨fun h => absurd h hd20, fun h => by linarith⟩
          ⟨fun h => absurd h hd21, fun h => by linarith⟩
          ⟨fun h => absurd h hd22, fun h => by linarith⟩
          ⟨fun h => absurd h hd23, fun h => by linarith⟩
          ⟨fun h => absurd h hd24, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd1⟩
          ⟨fun _ => by linarith, fun _ => hd2⟩
          ⟨fun _ => by linarith, fun _ => h23_0_hyp⟩
          ⟨fun _ => by linarith, fun _ => hd3⟩
          ⟨fun _ => by linarith, fun _ => hd4⟩
          ⟨fun _ => by linarith, fun _ => hd36⟩
          ⟨fun _ => by linarith, fun _ => hd5⟩
          ⟨fun _ => by linarith, fun _ => hd6⟩
          ⟨fun _ => by linarith, fun _ => hd7⟩
          ⟨fun _ => by linarith, fun _ => hd8⟩
          ⟨fun _ => by linarith, fun _ => hd9⟩
          ⟨fun _ => by linarith, fun _ => hd10⟩
          ⟨fun h => absurd h hd25, fun h => by linarith⟩
          ⟨fun h => absurd h hd26, fun h => by linarith⟩
          ⟨fun h => absurd h hd27, fun h => by linarith⟩
          ⟨fun h => absurd h hd28, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd11⟩
          ⟨fun _ => by linarith, fun _ => hd12⟩
          ⟨fun _ => by linarith, fun _ => hd13⟩
          ⟨fun _ => by linarith, fun _ => hd14⟩
          ⟨fun _ => by linarith, fun _ => hd29⟩
          ⟨fun h => absurd h hd34, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd30⟩
          ⟨fun _ => by linarith, fun _ => hd31⟩
          ⟨fun _ => by linarith, fun _ => hd32⟩
          ⟨fun _ => by linarith, fun _ => hd33⟩)
    · -- h23_0=F (1 pat)
      have hd37 : ¬sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
        fun h => h23_0_hyp (sys.trans _ _ _ h h10)
      exact fin4_witness sys (5/14) (5/14) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
        hn0 hn1 hn2 hn3
        (fin4_dispatch sys (5/14) (5/14) (1/7) (by linarith) (by linarith) (by linarith) (by linarith)
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
          ⟨fun _ => by linarith, fun _ => h10⟩
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
          ⟨fun h => absurd h hd15, fun h => by linarith⟩
          ⟨fun h => absurd h hd16, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => h0_23_hyp⟩
          ⟨fun h => absurd h hd17, fun h => by linarith⟩
          ⟨fun h => absurd h hd18, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd35⟩
          ⟨fun h => absurd h hd19, fun h => by linarith⟩
          ⟨fun h => absurd h hd20, fun h => by linarith⟩
          ⟨fun h => absurd h hd21, fun h => by linarith⟩
          ⟨fun h => absurd h hd22, fun h => by linarith⟩
          ⟨fun h => absurd h hd23, fun h => by linarith⟩
          ⟨fun h => absurd h hd24, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd1⟩
          ⟨fun _ => by linarith, fun _ => hd2⟩
          ⟨fun h => absurd h h23_0_hyp, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd3⟩
          ⟨fun _ => by linarith, fun _ => hd4⟩
          ⟨fun h => absurd h hd37, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd5⟩
          ⟨fun _ => by linarith, fun _ => hd6⟩
          ⟨fun _ => by linarith, fun _ => hd7⟩
          ⟨fun _ => by linarith, fun _ => hd8⟩
          ⟨fun _ => by linarith, fun _ => hd9⟩
          ⟨fun _ => by linarith, fun _ => hd10⟩
          ⟨fun h => absurd h hd25, fun h => by linarith⟩
          ⟨fun h => absurd h hd26, fun h => by linarith⟩
          ⟨fun h => absurd h hd27, fun h => by linarith⟩
          ⟨fun h => absurd h hd28, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd11⟩
          ⟨fun _ => by linarith, fun _ => hd12⟩
          ⟨fun _ => by linarith, fun _ => hd13⟩
          ⟨fun _ => by linarith, fun _ => hd14⟩
          ⟨fun _ => by linarith, fun _ => hd29⟩
          ⟨fun h => absurd h hd34, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => hd30⟩
          ⟨fun _ => by linarith, fun _ => hd31⟩
          ⟨fun _ => by linarith, fun _ => hd32⟩
          ⟨fun _ => by linarith, fun _ => hd33⟩)
  · -- h0_23=F (1 pat)
    have hd38 : ¬sys.ge {(1 : Fin 4)} ({2,3} : Set _) :=
      fun h => h0_23_hyp (sys.trans _ _ _ h01 h)
    have hd39 : sys.ge ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _) :=
      (sys.total ({2,3} : Set (Fin 4)) ({(0 : Fin 4)} : Set _)).elim id (fun h => absurd h h0_23_hyp)
    have hd40 : sys.ge ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _) :=
      (sys.total ({2,3} : Set (Fin 4)) ({(1 : Fin 4)} : Set _)).elim id (fun h => absurd h hd38)
    exact fin4_witness sys (11/42) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
      hn0 hn1 hn2 hn3
      (fin4_dispatch sys (11/42) (11/42) (5/21) (by linarith) (by linarith) (by linarith) (by linarith)
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
        ⟨fun _ => by linarith, fun _ => h10⟩
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
        ⟨fun h => absurd h hd15, fun h => by linarith⟩
        ⟨fun h => absurd h hd16, fun h => by linarith⟩
        ⟨fun h => absurd h h0_23_hyp, fun h => by linarith⟩
        ⟨fun h => absurd h hd17, fun h => by linarith⟩
        ⟨fun h => absurd h hd18, fun h => by linarith⟩
        ⟨fun h => absurd h hd38, fun h => by linarith⟩
        ⟨fun h => absurd h hd19, fun h => by linarith⟩
        ⟨fun h => absurd h hd20, fun h => by linarith⟩
        ⟨fun h => absurd h hd21, fun h => by linarith⟩
        ⟨fun h => absurd h hd22, fun h => by linarith⟩
        ⟨fun h => absurd h hd23, fun h => by linarith⟩
        ⟨fun h => absurd h hd24, fun h => by linarith⟩
        ⟨fun _ => by linarith, fun _ => hd1⟩
        ⟨fun _ => by linarith, fun _ => hd2⟩
        ⟨fun _ => by linarith, fun _ => hd39⟩
        ⟨fun _ => by linarith, fun _ => hd3⟩
        ⟨fun _ => by linarith, fun _ => hd4⟩
        ⟨fun _ => by linarith, fun _ => hd40⟩
        ⟨fun _ => by linarith, fun _ => hd5⟩
        ⟨fun _ => by linarith, fun _ => hd6⟩
        ⟨fun _ => by linarith, fun _ => hd7⟩
        ⟨fun _ => by linarith, fun _ => hd8⟩
        ⟨fun _ => by linarith, fun _ => hd9⟩
        ⟨fun _ => by linarith, fun _ => hd10⟩
        ⟨fun h => absurd h hd25, fun h => by linarith⟩
        ⟨fun h => absurd h hd26, fun h => by linarith⟩
        ⟨fun h => absurd h hd27, fun h => by linarith⟩
        ⟨fun h => absurd h hd28, fun h => by linarith⟩
        ⟨fun _ => by linarith, fun _ => hd11⟩
        ⟨fun _ => by linarith, fun _ => hd12⟩
        ⟨fun _ => by linarith, fun _ => hd13⟩
        ⟨fun _ => by linarith, fun _ => hd14⟩
        ⟨fun _ => by linarith, fun _ => hd29⟩
        ⟨fun h => absurd h hd34, fun h => by linarith⟩
        ⟨fun _ => by linarith, fun _ => hd30⟩
        ⟨fun _ => by linarith, fun _ => hd31⟩
        ⟨fun _ => by linarith, fun _ => hd32⟩
        ⟨fun _ => by linarith, fun _ => hd33⟩)


end Core.Scale
