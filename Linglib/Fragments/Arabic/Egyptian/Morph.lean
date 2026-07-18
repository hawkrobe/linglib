import Linglib.Morphology.FusionTypology

/-!
# Arabic (Egyptian) Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Egyptian Arabic (ISO `arz`, WALS code `aeg`).
WALS F20A codes Arabic as `ablautConcatenative`, mapping to the local
`.nonlinear` `Fusion` value. B&N flexive + cumulative are stipulated, but
the language is NOT in the "fusional" cell because that requires
`.concatenative` fusion — Arabic root-and-pattern templatic morphology
is the canonical non-concatenative case.
-/

namespace Arabic.Egyptian

open Morphology

/-- Arabic (Egyptian): WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. -/
def morphProfile : MorphProfile :=
  .fromWALS "Arabic (Egyptian)" "arz"
    (fusionFb        := .nonlinear)
    (exponenceFb     := .polyexponential)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

example : morphProfile.iso = "arz" ∧ morphProfile.language = "Arabic (Egyptian)" :=
  ⟨rfl, rfl⟩

/-- Arabic is NOT in the "fusional" cell despite being flexive + cumulative,
    because templatic root-and-pattern morphology is `.nonlinear`, not
    `.concatenative`. The `IsFusional` predicate correctly excludes it. -/
example : ¬ morphProfile.IsFusional := by decide

/-- Arabic is also not "agglutinating" — the same templatic morphology
    fails the concatenative requirement. -/
example : ¬ morphProfile.IsAgglutinating := by decide

end Arabic.Egyptian
