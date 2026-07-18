import Linglib.Morphology.FusionTypology

/-!
# Russian Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Russian (ISO `rus`). B&N 2001 places Russian in the
canonical "fusional" cell (concatenative + flexive + cumulative); the genitive
singular *-ī ~ -ae ~ -ūs* class-conditioned allomorphy pattern cited by
B&N as the diagnostic for flexivity is the same pattern Russian instantiates
across declension classes.
-/

namespace Russian

open Morphology

/-- Russian: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Russian" "rus"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

example : morphProfile.iso = "rus" ∧ morphProfile.language = "Russian" := ⟨rfl, rfl⟩

/-- B&N 2001 places Russian in the canonical "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Russian
