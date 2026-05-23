import Linglib.Morphology.MorphProfile

/-!
# Quechua (Imbabura) Morphological Profile
@cite{wals-2013} @cite{bickel-nichols-2001}

WALS-derived profile for Imbabura Quechua (ISO `qvi`). B&N 2001 places
Quechua in the "agglutinating" cell (concatenative + nonflexive + separative).
Consistent with the Imbabura data used in the Negation and PolarityItems
fragments in this directory.
-/

namespace Fragments.Quechua

open Morphology

/-- Quechua (Imbabura): WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Quechua (Imbabura)" "qvi"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (verbSynthesisFb := .high)
    (locusFb         := .dependentMarking)
    (prefixSuffixFb  := .stronglySuffixing)
    (reduplicationFb := .fullOnly)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "qvi" ∧ morphProfile.language = "Quechua (Imbabura)" :=
  ⟨rfl, rfl⟩

/-- B&N 2001 places Quechua in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Fragments.Quechua
