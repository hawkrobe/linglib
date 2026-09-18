import Linglib.Semantics.Tense.Decomposition

/-!
# English tense fragment

The English simple past and present perfect in Kratzer's surface-tense decomposition: each
is a present tense pronoun with the perfect aspect, the simple past fusing the two morphemes
where the present perfect exposes the perfect through the auxiliary *have*, so that the simple
past can be used deictically.

## References

* [kratzer-1998]
-/

open Tense

namespace English.Tense

/-! ### Surface tense ([kratzer-1998]) -/

open _root_.Tense.Decomposition
open _root_.Tense

/-- The English simple past decomposes as an indexical present tense pronoun with the perfect
aspect, so the form can be used deictically. -/
def simplePastSurface : SurfaceTense where
  tensePronoun := indexicalPresent
  hasPerfect := true

/-- The English present perfect decomposes as the simple past does, with the perfect exposed
by the auxiliary *have*. -/
def presentPerfectSurface : SurfaceTense where
  tensePronoun := indexicalPresent
  hasPerfect := true

/-- English simple past can be deictic (from decomposition). -/
theorem simplePastSurface_deictic :
    simplePastSurface.canBeDeictic := by decide

/-- The underlying tense head is PRESENT, not PAST.
    Pastness comes from the PERF aspect head, not the tense. -/
theorem simplePastSurface_underlyingPresent :
    simplePastSurface.tensePronoun.constraint = _root_.Tense.present := rfl

/-- Simple past and present perfect share the same underlying decomposition:
    both are PRESENT + PERFECT. The difference is that simple past fuses
    the two morphemes while present perfect makes the PERF transparent
    via auxiliary "have". -/
theorem simplePast_presentPerfect_same_decomposition :
    simplePastSurface.tensePronoun = presentPerfectSurface.tensePronoun ∧
    simplePastSurface.hasPerfect = presentPerfectSurface.hasPerfect :=
  ⟨rfl, rfl⟩

end English.Tense
