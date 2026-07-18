import Linglib.Morphology.FusionTypology

/-!
# German Morphological Profile
[wals-2013] [bickel-nichols-2007]

WALS-derived profile (Ch 20A–29A, 21B, 62A, 79A/B, 80A) for German (ISO `deu`,
WALS code `ger`). The `flexivity := flexive` and `bnExponence := cumulative`
values are not derivable from any WALS chapter; they are textbook-consensus
summary stipulations (strong-verb ablaut is [bickel-nichols-2007]'s own
stem-flexivity example, p. 184 — though the same chapter's Table 3.5 puts
Germanic *weak* verbs in the no-stem-allomorphy row, so the language-level
bit summarizes a split system). Together with the WALS-derived
`fusion := concatenative` they place German in the traditional "fusional"
cell.

WALS F20A's `exclusivelyConcatenative` verdict samples a small set of formatives
and systematically under-weights ablaut (`singen` ~ `sang` ~ `gesungen`) and
umlaut (`Bruder` ~ `Brüder`); a process-based treatment would not classify
German as exclusively concatenative.
-/

namespace German

open Morphology

/-- German: WALS-derived `MorphProfile` via `MorphProfile.fromWALS`. Required-field
    fallbacks match WALS values (lookup wins when present); `flexivity` and
    `bnExponence` are textbook-consensus stipulations (see header). -/
def morphProfile : MorphProfile :=
  .fromWALS "German" "deu"
    (fusionFb        := .concatenative)
    (exponenceFb     := .monoexponential)
    (flexivity       := some .flexive)
    (bnExponence     := some .cumulative)

/-- Typo sentry for the ISO and language label. -/
example : morphProfile.iso = "deu" ∧ morphProfile.language = "German" := ⟨rfl, rfl⟩

/-- Textbook-consensus classification: German falls in the "fusional" cell. Bridge theorem made local
    so the per-language commitment is visible here, not only inside
    `BickelNichols2013.lean`'s 18-language aggregate. -/
example : morphProfile.IsFusional := by decide

end German
