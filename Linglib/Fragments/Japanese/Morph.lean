import Linglib.Morphology.MorphProfile

/-!
# Japanese Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Japanese (ISO `jpn`). B&N 2001 places Japanese
in the "agglutinating" cell (concatenative + nonflexive + separative).
-/

namespace Japanese

open Morphology

/-- Japanese: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Japanese" "jpn"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (verbSynthesisFb := .moderate)
    (locusFb         := .dependentMarking)
    (prefixSuffixFb  := .stronglySuffixing)
    (reduplicationFb := .noProductive)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "jpn" ∧ morphProfile.language = "Japanese" := ⟨rfl, rfl⟩

/-- B&N 2001 places Japanese in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Japanese
