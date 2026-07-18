import Linglib.Morphology.FusionTypology

/-!
# Turkish Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Turkish (ISO `tur`). B&N 2001 places Turkish in
the canonical "agglutinating" cell (concatenative + nonflexive + separative);
Turkish is the textbook example of rule-governed (vowel-harmony) suffix
allomorphy with no class-conditioned variation.
-/

namespace Turkish

open Morphology

/-- Turkish: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Turkish" "tur"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "tur" ∧ morphProfile.language = "Turkish" := ⟨rfl, rfl⟩

/-- B&N 2001 places Turkish in the canonical "agglutinating" cell. -/
example : morphProfile.IsAgglutinating := by decide

end Turkish
