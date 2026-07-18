import Linglib.Morphology.FusionTypology

/-!
# English Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for English (ISO `eng`). B&N 2007 places English
in the "agglutinating" cell (concatenative + nonflexive + separative)
despite its small inflectional inventory; cf. [bickel-nichols-2007].
-/

namespace English

open Morphology

/-- English: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "English" "eng"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "eng" ∧ morphProfile.language = "English" := ⟨rfl, rfl⟩

/-- B&N 2007 places English in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end English
