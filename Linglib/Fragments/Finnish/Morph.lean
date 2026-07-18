import Linglib.Morphology.FusionTypology

/-!
# Finnish Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Finnish (ISO `fin`). B&N 2001 places Finnish in the
"agglutinating" cell (concatenative + nonflexive + separative).
-/

namespace Finnish

open Morphology

/-- Finnish: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Finnish" "fin"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "fin" ∧ morphProfile.language = "Finnish" := ⟨rfl, rfl⟩

/-- B&N 2001 places Finnish in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Finnish
