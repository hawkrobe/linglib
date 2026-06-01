import Linglib.Morphology.MorphProfile

/-!
# Tagalog Morphological Profile
@cite{wals-2013} @cite{bickel-nichols-2001}

WALS-derived profile for Tagalog (ISO `tgl`). B&N 2001 places Tagalog in
the "agglutinating" cell (concatenative + nonflexive + separative).
-/

namespace Tagalog

open Morphology

/-- Tagalog: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Tagalog" "tgl"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (verbSynthesisFb := .moderate)
    (locusFb         := .dependentMarking)
    (prefixSuffixFb  := .stronglySuffixing)
    (reduplicationFb := .noProductive)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "tgl" ∧ morphProfile.language = "Tagalog" := ⟨rfl, rfl⟩

/-- B&N 2001 places Tagalog in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Tagalog
