import Linglib.Morphology.FusionTypology

/-!
# Arabic (Egyptian) Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile for Egyptian Arabic (ISO `arz`, WALS code `aeg`).
WALS F20A codes Arabic as `ablautConcatenative` — a mixed category the
converter refuses — so `fusion` comes from the fallback `.nonlinear`:
root-and-pattern morphology is predominantly nonlinear, though person and
number inflection is concatenative ([bickel-nichols-2007] p. 183). The
flexive + cumulative values are textbook-consensus summary stipulations
(Semitic is [bickel-nichols-2007]'s flexive-nonlinear "introflexive"
type, p. 186; the chapter types formatives, not whole languages).
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

/-- Arabic is the "introflexive" type — flexive + nonlinear, the label
    [bickel-nichols-2007] p. 186 reserve for exactly this combination —
    hence neither agglutinating nor fusional (both require concatenative
    fusion). -/
example : morphProfile.IsIntroflexive ∧
    ¬ morphProfile.IsFusional ∧ ¬ morphProfile.IsAgglutinating := by decide

end Arabic.Egyptian
