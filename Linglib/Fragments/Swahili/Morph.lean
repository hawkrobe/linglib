import Linglib.Morphology.FusionTypology

/-!
# Swahili Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Swahili (ISO `swh`). Textbook-consensus classification: Swahili falls in the "agglutinating" cell (concatenative + nonflexive + separative); Swahili is
the sample's one weakly prefixing (rather than suffixing) member — the
18-language sample is linglib's own, not B&N's.
-/

namespace Swahili

open Morphology

/-- Swahili: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Swahili" "swh"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "swh" ∧ morphProfile.language = "Swahili" := ⟨rfl, rfl⟩

/-- Textbook-consensus classification: Swahili falls in the "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Swahili
