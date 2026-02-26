import Linglib.Core.Scales.EpistemicScale.Fin4.Defs

namespace Core.Scale

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000 in
/-- Case (3,1): 1 sub-case. -/
theorem fin4_case_31 (sys : EpistemicSystemFA (Fin 4))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 4)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 4)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 4)}) (hn3 : ¬sys.ge ∅ {(3 : Fin 4)})
    (h01 : sys.ge {(0 : Fin 4)} {1})
    (h10 : sys.ge {(1 : Fin 4)} {0})
    (h12 : sys.ge {(1 : Fin 4)} {2})
    (h21 : sys.ge {(2 : Fin 4)} {1})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (hng32 : ¬sys.ge {(3 : Fin 4)} {2})
    (h02 : sys.ge {(0 : Fin 4)} {2})
    (h20 : sys.ge {(2 : Fin 4)} {0})
    (h03 : sys.ge {(0 : Fin 4)} {3})
    (h13 : sys.ge {(1 : Fin 4)} {3})
    :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
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
  have hd17 := nge_singleton_pair sys h10 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd18 := nge_singleton_pair sys h10 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd19 := nge_singleton_pair sys h20 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd20 := nge_singleton_pair sys h01 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd21 := nge_singleton_pair sys h01 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd22 := nge_singleton_pair sys h21 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd23 := nge_singleton_pair sys h02 hn1 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd24 := nge_singleton_pair sys h02 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd25 := nge_singleton_pair sys h12 hn3 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd26 := nge_singleton_pair sys h03 hn1 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd27 := nge_singleton_pair sys h03 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd28 := nge_singleton_pair sys h13 hn2 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd29 := nge_superset sys
    (show ({1,2}:Set (Fin 4)) ⊆ {1,2,3} from fun x hx => by fin_cases x <;> simp_all) hd17
  have hd30 := nge_superset sys
    (show ({0,2}:Set (Fin 4)) ⊆ {0,2,3} from fun x hx => by fin_cases x <;> simp_all) hd20
  have hd31 := nge_superset sys
    (show ({0,1}:Set (Fin 4)) ⊆ {0,1,3} from fun x hx => by fin_cases x <;> simp_all) hd23
  have hd32 := nge_superset sys
    (show ({0}:Set (Fin 4)) ⊆ {0,1,2} from fun x hx => by fin_cases x <;> simp_all) hng30
  -- pair vs pair
  have hd33 := ge_pair_via_mid sys ({0,1} : Set _) ({2,3} : Set _) ({0,2} : Set _)
    h12 h03 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd34 := ge_pair_via_mid sys ({0,2} : Set _) ({1,3} : Set _) ({0,1} : Set _)
    h21 h03 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd35 := ge_pair_via_mid sys ({1,2} : Set _) ({0,3} : Set _) ({0,1} : Set _)
    h20 h13 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd36 := nge_pair_via_contra sys ({2,3} : Set _) ({0,1} : Set _) ({0,2} : Set _)
    h12 hng30 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd37 := nge_pair_via_contra sys ({1,3} : Set _) ({0,2} : Set _) ({0,1} : Set _)
    h21 hng30 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  have hd38 := nge_pair_via_contra sys ({0,3} : Set _) ({1,2} : Set _) ({0,1} : Set _)
    h20 hng31 (by sdiff) (by sdiff) (by sdiff) (by sdiff)
  -- Leaf: witness (11/42, 11/42, 11/42)
  exact fin4_witness sys (11/42) (11/42) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
    hn0 hn1 hn2 hn3
    (fin4_dispatch sys (11/42) (11/42) (11/42) (by linarith) (by linarith) (by linarith) (by linarith)
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
      (bp h01 (by linarith)) (bp h10 (by linarith)) (bp h02 (by linarith))
      (bp h20 (by linarith)) (bp h03 (by linarith)) (bn hng30 (fun h => by linarith))
      (bp h12 (by linarith)) (bp h21 (by linarith)) (bp h13 (by linarith))
      (bn hng31 (fun h => by linarith)) (bp h23 (by linarith)) (bn hng32 (fun h => by linarith))
      -- singleton ↛ pair (12)
      (bn hd17 (fun h => by linarith)) (bn hd18 (fun h => by linarith))
      (bn hd19 (fun h => by linarith)) (bn hd20 (fun h => by linarith))
      (bn hd21 (fun h => by linarith)) (bn hd22 (fun h => by linarith))
      (bn hd23 (fun h => by linarith)) (bn hd24 (fun h => by linarith))
      (bn hd25 (fun h => by linarith)) (bn hd26 (fun h => by linarith))
      (bn hd27 (fun h => by linarith)) (bn hd28 (fun h => by linarith))
      -- pair ← singleton (12)
      (bp hd1 (by linarith)) (bp hd2 (by linarith)) (bp hd3 (by linarith))
      (bp hd4 (by linarith)) (bp hd5 (by linarith)) (bp hd6 (by linarith))
      (bp hd7 (by linarith)) (bp hd8 (by linarith)) (bp hd9 (by linarith))
      (bp hd10 (by linarith)) (bp hd11 (by linarith)) (bp hd12 (by linarith))
      -- singleton ↛ triple (4)
      (bn hd29 (fun h => by linarith)) (bn hd30 (fun h => by linarith))
      (bn hd31 (fun h => by linarith)) (bn hd32 (fun h => by linarith))
      -- triple ← singleton (4)
      (bp hd13 (by linarith)) (bp hd14 (by linarith))
      (bp hd15 (by linarith)) (bp hd16 (by linarith))
      -- pair vs pair (6)
      (bp hd33 (by linarith)) (bn hd36 (fun h => by linarith))
      (bp hd34 (by linarith)) (bn hd37 (fun h => by linarith))
      (bn hd38 (fun h => by linarith)) (bp hd35 (by linarith)))


end Core.Scale
