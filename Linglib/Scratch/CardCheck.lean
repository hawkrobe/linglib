import Linglib.Core.Algebra.ConnesKreimer.DoubleCut

namespace ConnesKreimer.CardCheck

abbrev Atom := ULift (Fin 3)
abbrev a : Atom := ⟨0⟩
abbrev b : Atom := ⟨1⟩
abbrev c : Atom := ⟨2⟩
abbrev t : Atom := ⟨0⟩

/-- Tree with a deep `.trace` marker — the substrate-fix-stress test. -/
abbrev TT : DecoratedTree Atom :=
  .node (.node (.trace (.leaf t)) (.leaf c)) (.leaf b)

-- After substrate fix: GeoCut = LHS = RHS = 18 for the .trace-deep case.
example : Multiset.card (lhsRealCuts (R := ℚ) TT) = 18 := by decide
example : Multiset.card (rhsRealRealInner (R := ℚ) TT) = 18 := by decide
example : Fintype.card (GeoCut TT Layer.top) = 18 := by decide

-- No-trace case unchanged: T = .node (.leaf a) (.leaf b) still gives 9.
abbrev TNoTrace : DecoratedTree Atom := .node (.leaf a) (.leaf b)
example : Fintype.card (GeoCut TNoTrace Layer.top) = 9 := by decide
example : Multiset.card (lhsRealCuts (R := ℚ) TNoTrace) = 9 := by decide
example : Multiset.card (rhsRealRealInner (R := ℚ) TNoTrace) = 9 := by decide

end ConnesKreimer.CardCheck
