import Linglib.Morphology.MorphProfile

/-!
# Hungarian Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Hungarian (ISO `hun`). B&N 2001 places Hungarian
in the "agglutinating" cell (concatenative + nonflexive + separative).
-/

namespace Hungarian

open Morphology

/-- Hungarian: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Hungarian" "hun"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "hun" ∧ morphProfile.language = "Hungarian" := ⟨rfl, rfl⟩

/-- B&N 2001 places Hungarian in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Hungarian
