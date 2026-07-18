import Linglib.Morphology.FusionTypology

/-!
# Hindi-Urdu Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Hindi-Urdu (ISO `hin`). Textbook-consensus classification: Hindi-Urdu falls in the "fusional" cell (concatenative + flexive + cumulative).
-/

namespace Hindi

open Morphology

/-- Hindi-Urdu: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Hindi-Urdu" "hin"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

example : morphProfile.iso = "hin" ∧ morphProfile.language = "Hindi-Urdu" := ⟨rfl, rfl⟩

/-- Textbook-consensus classification: Hindi-Urdu falls in the "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Hindi
