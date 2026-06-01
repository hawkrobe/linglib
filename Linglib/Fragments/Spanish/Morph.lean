import Linglib.Morphology.MorphProfile

/-!
# Spanish Morphological Profile
@cite{wals-2013} @cite{bickel-nichols-2001}

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
    (verbSynthesisFb := .moderate)
    (locusFb         := .dependentMarking)
    (prefixSuffixFb  := .stronglySuffixing)
    (reduplicationFb := .noProductive)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

example : morphProfile.iso = "spa" ∧ morphProfile.language = "Spanish" := ⟨rfl, rfl⟩

/-- B&N 2001 places Spanish in the "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Spanish
