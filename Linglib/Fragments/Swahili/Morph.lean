import Linglib.Morphology.MorphProfile

/-!
# Swahili Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Swahili (ISO `swh`). B&N 2001 places Swahili in the
"agglutinating" cell (concatenative + nonflexive + separative); Swahili is
unusual among the 18-language sample in being weakly prefixing rather than
suffixing.
-/

namespace Swahili

open Morphology

/-- Swahili: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Swahili" "swh"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "swh" ∧ morphProfile.language = "Swahili" := ⟨rfl, rfl⟩

/-- B&N 2001 places Swahili in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Swahili
