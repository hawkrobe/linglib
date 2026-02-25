import Linglib.Core.Scales.EpistemicScale.Fin4.Defs

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000 in
/-- Case (4): 1 sub-cases. -/
theorem fin4_case_4 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (h10 : sys.ge {(1 : Fin 4)} {0})
    (h12 : sys.ge {(1 : Fin 4)} {2})
    (h21 : sys.ge {(2 : Fin 4)} {1})
    (h13 : sys.ge {(1 : Fin 4)} {3})
    (h31 : sys.ge {(3 : Fin 4)} {1})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h32 : sys.ge {(3 : Fin 4)} {2})
    (h02 : sys.ge {(0 : Fin 4)} {2})
    (h20 : sys.ge {(2 : Fin 4)} {0})
    (h03 : sys.ge {(0 : Fin 4)} {3})
    (h30 : sys.ge {(3 : Fin 4)} {0})
    :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
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
  have hd3 := ge_superset sys (show (2:Fin 4) ∈ ({2,3}:Set _) from Or.inl rfl) h20
  have hd4 := ge_superset sys (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl) h01
  have hd5 := ge_superset sys (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl) h01
  have hd6 := ge_superset sys (show (2:Fin 4) ∈ ({2,3}:Set _) from Or.inl rfl) h21
  have hd7 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h02
  have hd8 := ge_superset sys (show (0:Fin 4) ∈ ({0,3}:Set _) from Or.inl rfl) h02
  have hd9 := ge_superset sys (show (1:Fin 4) ∈ ({1,3}:Set _) from Or.inl rfl) h12
  have hd10 := ge_superset sys (show (0:Fin 4) ∈ ({0,1}:Set _) from Or.inl rfl) h03
  have hd11 := ge_superset sys (show (0:Fin 4) ∈ ({0,2}:Set _) from Or.inl rfl) h03
  have hd12 := ge_superset sys (show (1:Fin 4) ∈ ({1,2}:Set _) from Or.inl rfl) h13
  have hd13 := ge_superset sys (show (1:Fin 4) ∈ ({1,2,3}:Set _) from Or.inl rfl) h10
  have hd14 := ge_superset sys (show (0:Fin 4) ∈ ({0,2,3}:Set _) from Or.inl rfl) h01
  have hd15 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,3}:Set _) from Or.inl rfl) h02
  have hd16 := ge_superset sys (show (0:Fin 4) ∈ ({0,1,2}:Set _) from Or.inl rfl) h03
  have hd17 := nge_singleton_pair sys h10 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd18 := nge_singleton_pair sys h10 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd19 := nge_singleton_pair sys h20 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd20 := nge_singleton_pair sys h01 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd21 := nge_singleton_pair sys h01 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd22 := nge_singleton_pair sys h21 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd23 := nge_singleton_pair sys h02 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd24 := nge_singleton_pair sys h02 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd25 := nge_singleton_pair sys h12 hn3
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd26 := nge_singleton_pair sys h03 hn1
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd27 := nge_singleton_pair sys h03 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd28 := nge_singleton_pair sys h13 hn2
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
    (by ext x; fin_cases x <;> simp_all) (by ext x; fin_cases x <;> simp_all)
  have hd29 := nge_superset sys
    (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd17
  have hd30 := nge_superset sys
    (show ({0,2}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hd20
  have hd31 := nge_superset sys
    (show ({0,1}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hd23
  have hd32 := nge_superset sys
    (show ({0,1}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hd26
  have hd33 : sys.ge ({0,1} : Set (Fin 4)) ({2,3} : Set _) := by
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
  have hd34 : sys.ge ({2,3} : Set (Fin 4)) ({0,1} : Set _) := by
    have h1 : sys.ge ({2,3} : Set (Fin 4)) ({0,2} : Set _) := by
      rw [sys.additive ({2,3} : Set (Fin 4)) {0,2},
          show ({2,3} : Set (Fin 4)) \ {0,2} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {2,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h30
    have h2 : sys.ge ({0,2} : Set _) ({0,1} : Set _) := by
      rw [sys.additive ({0,2} : Set (Fin 4)) {0,1},
          show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h21
    exact sys.trans _ _ _ h1 h2
  have hd35 : sys.ge ({0,2} : Set (Fin 4)) ({1,3} : Set _) := by
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
  have hd36 : sys.ge ({1,3} : Set (Fin 4)) ({0,2} : Set _) := by
    have h1 : sys.ge ({1,3} : Set (Fin 4)) ({0,1} : Set _) := by
      rw [sys.additive ({1,3} : Set (Fin 4)) {0,1},
          show ({1,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,1} : Set (Fin 4)) \ {1,3} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h30
    have h2 : sys.ge ({0,1} : Set _) ({0,2} : Set _) := by
      rw [sys.additive ({0,1} : Set (Fin 4)) {0,2},
          show ({0,1} : Set (Fin 4)) \ {0,2} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h12
    exact sys.trans _ _ _ h1 h2
  have hd37 : sys.ge ({0,3} : Set (Fin 4)) ({1,2} : Set _) := by
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
  have hd38 : sys.ge ({1,2} : Set (Fin 4)) ({0,3} : Set _) := by
    have h1 : sys.ge ({1,2} : Set (Fin 4)) ({0,1} : Set _) := by
      rw [sys.additive ({1,2} : Set (Fin 4)) {0,1},
          show ({1,2} : Set (Fin 4)) \ {0,1} = {(2 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,1} : Set (Fin 4)) \ {1,2} = {(0 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h20
    have h2 : sys.ge ({0,1} : Set _) ({0,3} : Set _) := by
      rw [sys.additive ({0,1} : Set (Fin 4)) {0,3},
          show ({0,1} : Set (Fin 4)) \ {0,3} = {(1 : Fin 4)} from by ext x; fin_cases x <;> simp_all,
          show ({0,3} : Set (Fin 4)) \ {0,1} = {(3 : Fin 4)} from by ext x; fin_cases x <;> simp_all]
      exact h13
    exact sys.trans _ _ _ h1 h2
  exact fin4_witness sys (1/4) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
    hn0 hn1 hn2 hn3
    (fin4_dispatch sys (1/4) (1/4) (1/4) (by linarith) (by linarith) (by linarith) (by linarith)
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
      ⟨fun _ => by linarith, fun _ => h20⟩
      ⟨fun _ => by linarith, fun _ => h03⟩
      ⟨fun _ => by linarith, fun _ => h30⟩
      ⟨fun _ => by linarith, fun _ => h12⟩
      ⟨fun _ => by linarith, fun _ => h21⟩
      ⟨fun _ => by linarith, fun _ => h13⟩
      ⟨fun _ => by linarith, fun _ => h31⟩
      ⟨fun _ => by linarith, fun _ => h23⟩
      ⟨fun _ => by linarith, fun _ => h32⟩
      ⟨fun h => absurd h hd17, fun h => by linarith⟩
      ⟨fun h => absurd h hd18, fun h => by linarith⟩
      ⟨fun h => absurd h hd19, fun h => by linarith⟩
      ⟨fun h => absurd h hd20, fun h => by linarith⟩
      ⟨fun h => absurd h hd21, fun h => by linarith⟩
      ⟨fun h => absurd h hd22, fun h => by linarith⟩
      ⟨fun h => absurd h hd23, fun h => by linarith⟩
      ⟨fun h => absurd h hd24, fun h => by linarith⟩
      ⟨fun h => absurd h hd25, fun h => by linarith⟩
      ⟨fun h => absurd h hd26, fun h => by linarith⟩
      ⟨fun h => absurd h hd27, fun h => by linarith⟩
      ⟨fun h => absurd h hd28, fun h => by linarith⟩
      ⟨fun _ => by linarith, fun _ => hd1⟩
      ⟨fun _ => by linarith, fun _ => hd2⟩
      ⟨fun _ => by linarith, fun _ => hd3⟩
      ⟨fun _ => by linarith, fun _ => hd4⟩
      ⟨fun _ => by linarith, fun _ => hd5⟩
      ⟨fun _ => by linarith, fun _ => hd6⟩
      ⟨fun _ => by linarith, fun _ => hd7⟩
      ⟨fun _ => by linarith, fun _ => hd8⟩
      ⟨fun _ => by linarith, fun _ => hd9⟩
      ⟨fun _ => by linarith, fun _ => hd10⟩
      ⟨fun _ => by linarith, fun _ => hd11⟩
      ⟨fun _ => by linarith, fun _ => hd12⟩
      ⟨fun h => absurd h hd29, fun h => by linarith⟩
      ⟨fun h => absurd h hd30, fun h => by linarith⟩
      ⟨fun h => absurd h hd31, fun h => by linarith⟩
      ⟨fun h => absurd h hd32, fun h => by linarith⟩
      ⟨fun _ => by linarith, fun _ => hd13⟩
      ⟨fun _ => by linarith, fun _ => hd14⟩
      ⟨fun _ => by linarith, fun _ => hd15⟩
      ⟨fun _ => by linarith, fun _ => hd16⟩
      ⟨fun _ => by linarith, fun _ => hd33⟩
      ⟨fun _ => by linarith, fun _ => hd34⟩
      ⟨fun _ => by linarith, fun _ => hd35⟩
      ⟨fun _ => by linarith, fun _ => hd36⟩
      ⟨fun _ => by linarith, fun _ => hd37⟩
      ⟨fun _ => by linarith, fun _ => hd38⟩)


end Core.Scale
