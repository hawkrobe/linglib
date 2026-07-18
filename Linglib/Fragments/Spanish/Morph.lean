import Linglib.Morphology.FusionTypology

/-!
# Spanish Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Spanish (ISO `spa`). Textbook-consensus classification: Spanish falls in the "fusional" cell (concatenative + flexive + cumulative).
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

/-- Textbook-consensus classification: Spanish falls in the "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Spanish
