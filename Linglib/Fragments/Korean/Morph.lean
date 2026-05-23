import Linglib.Morphology.MorphProfile

/-!
# Korean Morphological Profile
@cite{wals-2013} @cite{bickel-nichols-2001}

WALS-derived profile for Korean (ISO `kor`). B&N 2001 places Korean
in the "agglutinating" cell (concatenative + nonflexive + separative).
-/

namespace Fragments.Korean

open Morphology

/-- Korean: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Korean" "kor"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (verbSynthesisFb := .moderate)
    (locusFb         := .dependentMarking)
    (prefixSuffixFb  := .stronglySuffixing)
    (reduplicationFb := .noProductive)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "kor" ∧ morphProfile.language = "Korean" := ⟨rfl, rfl⟩

/-- B&N 2001 places Korean in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Fragments.Korean
