import Linglib.Morphology.FusionTypology

/-!
# Thai Morphological Profile
[wals-2013]

WALS-derived profile for Thai (ISO `tha`). WALS F20A codes Thai as
`isolatingConcatenative`, a mixed type the local 3-way `Fusion` enum cannot
represent — `walsFusion` returns `none` and the fallback `.isolating` is
exercised. F21A returns `noCase`, mapping to `none`; the local `.noCase`
fallback is exercised. flexivity/bnExponence are left uncoded (`none`): no
consensus language-level value is stipulated for Thai.
-/

namespace Thai

open Morphology

/-- Thai: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Thai" "tha"
    (fusionFb        := .isolating)
    (exponenceFb     := .noCase)

example : morphProfile.iso = "tha" ∧ morphProfile.language = "Thai" := ⟨rfl, rfl⟩

end Thai
