import Linglib.Morphology.MorphProfile

/-!
# Hindi-Urdu Morphological Profile
@cite{wals-2013} @cite{bickel-nichols-2001}

WALS-derived profile for Hindi-Urdu (ISO `hin`). B&N 2001 places Hindi-Urdu
in the "fusional" cell (concatenative + flexive + cumulative).
-/

namespace Hindi

open Morphology

/-- Hindi-Urdu: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Hindi-Urdu" "hin"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (verbSynthesisFb := .moderate)
    (locusFb         := .dependentMarking)
    (prefixSuffixFb  := .stronglySuffixing)
    (reduplicationFb := .noProductive)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

example : morphProfile.iso = "hin" ∧ morphProfile.language = "Hindi-Urdu" := ⟨rfl, rfl⟩

/-- B&N 2001 places Hindi-Urdu in the "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Hindi
