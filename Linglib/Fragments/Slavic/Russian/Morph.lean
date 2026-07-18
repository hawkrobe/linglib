import Linglib.Morphology.FusionTypology

/-!
# Russian Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Russian (ISO `rus`). Textbook-consensus
classification: Russian falls in the "fusional" cell (concatenative +
flexive + cumulative). [bickel-nichols-2007] p. 187: "Russian case
desinences are mostly dependent on lexical declension classes and are
therefore ﬂexive" — *mostly*: the same page notes the dative, instrumental,
and locative plural formatives are invariant, so the language-level bit
summarizes a split system.
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

/-- Textbook-consensus classification: Russian falls in the canonical "fusional" cell. -/
example : morphProfile.IsFusional := by decide

end Russian
