import Linglib.Morphology.FusionTypology

/-!
# Georgian Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Georgian (ISO `kat`). B&N 2001 places Georgian
in the "fusional" cell (concatenative + flexive + cumulative).
-/

namespace Georgian

open Morphology

/-- Georgian: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Georgian" "kat"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

example : morphProfile.iso = "kat" ∧ morphProfile.language = "Georgian" := ⟨rfl, rfl⟩

/-- B&N 2001 places Georgian in the "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Georgian
