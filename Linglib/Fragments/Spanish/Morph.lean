import Linglib.Morphology.FusionTypology

/-!
# Spanish Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Spanish (ISO `spa`). B&N 2001 places Spanish in
the "fusional" cell (concatenative + flexive + cumulative).
-/

namespace Spanish

open Morphology

/-- Spanish: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Spanish" "spa"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

example : morphProfile.iso = "spa" ∧ morphProfile.language = "Spanish" := ⟨rfl, rfl⟩

/-- B&N 2001 places Spanish in the "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Spanish
