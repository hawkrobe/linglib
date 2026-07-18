import Linglib.Morphology.FusionTypology

/-!
# Indonesian Morphological Profile
[wals-2013] [bickel-nichols-2001]

WALS-derived profile for Indonesian (ISO `ind`). WALS F20A codes Indonesian
as `exclusivelyIsolating`, which the local 3-way `Fusion` enum maps to
`.isolating`. The few productive affixes that do exist (*ber-*, *meN-*) are
nonflexive and separative — stipulated here for completeness, but they do
NOT place Indonesian in B&N's "agglutinating" cell since `IsAgglutinating`
requires `.concatenative` fusion.
-/

namespace Indonesian

open Morphology

/-- Indonesian: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Indonesian" "ind"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .nonflexive)
    (bnExponence     := some .separative)

example : morphProfile.iso = "ind" ∧ morphProfile.language = "Indonesian" := ⟨rfl, rfl⟩

/-- WALS F20A's `exclusivelyIsolating` verdict places Indonesian in the
    isolating cell, NOT the agglutinating one — the few productive affixes
    notwithstanding. The bridge theorem caught a Fragment-file editorial
    drift: previous fallback values implied agglutinating, but the actual
    WALS lookup overrides them. -/
example : ¬ morphProfile.IsAgglutinating := by decide
example : morphProfile.fusion = .isolating := by decide

end Indonesian
