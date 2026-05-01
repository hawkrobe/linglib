import Linglib.Typology.WordOrder

/-!
# K'iche' word-order profile @cite{mondloch-2017}

K'iche' is not coded in WALS Chs 81/82/83 (ISO `quc` is absent), so
the profile is grammar-grounded from @cite{mondloch-2017} Lesson 9
rather than via `WordOrderProfile.ofWALS`. Mondloch documents
verb-initial order: VS for intransitives and VOS for transitives —
the basic-order field uses `.vos` (the canonical transitive-clause
classification) per WALS practice.
-/

namespace Fragments.Mayan.Kiche

/-- K'iche' word-order profile, grammar-grounded from
    @cite{mondloch-2017} Lesson 9 ("the preferred word order
    appears to be: verb-subject", with VOS for transitives).
    Not in WALS Chs 81/82/83 — fields override `.notInWALS`. -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  { basicOrder := .vos
    svOrder := .vs
    ovOrder := .vo }

set_option maxRecDepth 4096 in
/-- Drift sentinel: the profile is internally consistent. -/
theorem wordOrder_consistent : wordOrder.IsConsistent := by decide

end Fragments.Mayan.Kiche
