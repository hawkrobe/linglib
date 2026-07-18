import Linglib.Morphology.FusionTypology

/-!
# Tagalog Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Tagalog (ISO `tgl`). Textbook-consensus classification: Tagalog falls in the "agglutinating" cell (concatenative + nonflexive + separative).
-/

namespace Tagalog

open Morphology

/-- Tagalog: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Tagalog" "tgl"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "tgl" ∧ morphProfile.language = "Tagalog" := ⟨rfl, rfl⟩

/-- Textbook-consensus classification: Tagalog falls in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Tagalog
