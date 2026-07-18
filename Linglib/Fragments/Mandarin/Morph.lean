import Linglib.Morphology.MorphProfile

/-!
# Mandarin Chinese Morphological Profile
[wals-2013]

WALS-derived profile for Mandarin Chinese (ISO `cmn`). WALS F20A codes
Mandarin as `isolatingConcatenative`, a mixed type the local 3-way `Fusion`
enum cannot represent — `walsFusion` returns `none` and the fallback
`.isolating` is exercised. B&N 2001 flexivity/bnExponence are not stipulated
because the largely isolating typology renders them inapplicable.
-/

namespace Mandarin

open Morphology

/-- Mandarin Chinese: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Mandarin Chinese" "cmn"
    (fusionFb        := .isolating)
    (exponenceFb     := .monoexponential)

example : morphProfile.iso = "cmn" ∧ morphProfile.language = "Mandarin Chinese" :=
  ⟨rfl, rfl⟩

end Mandarin
