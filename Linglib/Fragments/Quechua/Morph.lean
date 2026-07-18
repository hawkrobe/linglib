import Linglib.Morphology.FusionTypology

/-!
# Quechua (Imbabura) Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Imbabura Quechua (ISO `qvi`). Textbook-consensus
classification: Quechua falls in the "agglutinating" cell (concatenative +
nonflexive + separative).
Consistent with the Imbabura data used in the Negation and PolarityItems
fragments in this directory.
-/

namespace Quechua

open Morphology

/-- Quechua (Imbabura): WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Quechua (Imbabura)" "qvi"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "qvi" ∧ morphProfile.language = "Quechua (Imbabura)" :=
  ⟨rfl, rfl⟩

/-- Textbook-consensus classification: Quechua falls in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Quechua
