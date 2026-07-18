import Linglib.Morphology.FusionTypology

/-!
# Mandarin Chinese Morphological Profile
[wals-2013]

WALS-derived profile for Mandarin Chinese (ISO `cmn`). WALS F20A codes
Mandarin as `isolatingConcatenative`, a mixed type the local 3-way `Fusion`
enum cannot represent — `walsFusion` returns `none` and the fallback
`.isolating` is exercised. flexivity/bnExponence are left uncoded (`none`)
here — not because isolating voids them ([bickel-nichols-2007] pp. 186-187
attest both flexive-isolating and nonflexive-isolating formatives) but
because no consensus language-level value is stipulated for Mandarin.
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
