import Linglib.Core.Algebra.ConnesKreimer.DoubleCut

namespace ConnesKreimer.GeoCutCheck

abbrev Atom := ULift (Fin 2)
abbrev a : Atom := ⟨0⟩
abbrev b : Atom := ⟨1⟩

abbrev T : DecoratedTree Atom := .node (.leaf a) (.leaf b)

-- For T = .node (.leaf a) (.leaf b), root layer top:
-- Each .leaf has 1 GeoCut per layer, and node has #(lL ≤ top) × #(rL ≤ top) = 3×3 = 9.
example : Fintype.card (GeoCut T Layer.top) = 9 := by decide
example : Fintype.card (GeoCut T Layer.mid) = 4 := by decide  -- 2×2: lL∈{bot,mid}, rL∈{bot,mid}
example : Fintype.card (GeoCut T Layer.bot) = 1 := by decide  -- 1×1: only bot

end ConnesKreimer.GeoCutCheck
