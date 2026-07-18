import Linglib.Morphology.MorphProfile

/-!
# Korean Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Korean (ISO `kor`). B&N 2001 places Korean
in the "agglutinating" cell (concatenative + nonflexive + separative).
-/

namespace Korean

open Morphology

/-- Korean: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Korean" "kor"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "kor" ∧ morphProfile.language = "Korean" := ⟨rfl, rfl⟩

/-- B&N 2001 places Korean in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Korean
