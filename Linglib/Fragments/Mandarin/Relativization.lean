import Linglib.Syntax.RelativeClause.Basic

/-!
# Mandarin Relativization Fragment
[keenan-comrie-1977]

Two relative clause markers, both prenominal with the clause-final
particle *de*:
- gap in NP_rel (-case, covers SU/DO)
- retained pronoun in NP_rel (+case, covers DO–OCOMP; retention is
  optional at DO)

The two strategies overlap at DO, and the +case strategy reaches the
bottom of the Accessibility Hierarchy — a prenominal-RC language with
pronoun retention down to OCOMP, unlike the sample's other prenominal
languages (Korean, Japanese, Basque).

Data from [keenan-comrie-1977] Table 1 ("Chinese (spoken Pekingese)")
and Table 2 (retention pattern).
-/

namespace Mandarin

open RelativeClause

/-- Prenominal RC closed by the particle *de*; NP_rel is deleted (gap).
    Covers subject and direct object relativization.
    E.g., "[ _ mǎi shū de] rén" '[ _ buys book DE] person' = 'the person
    who buys books'. -/
def relDeGap : Marker :=
  { form := "de"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject, .directObject]
  , notes := "Particle de; NP_rel deleted" }

/-- Prenominal RC closed by *de* with a personal pronoun retained in
    NP_rel; the pronoun (with its coverb where applicable) expresses the
    relativized role, so the strategy is +case in [keenan-comrie-1977]'s
    sense. Covers DO–OCOMP per Table 1; Table 2 records retention as
    optional at DO and normal from IO down. -/
def relDeResumptive : Marker :=
  { form := "de"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .preNominal
  , positions := [.directObject, .indirectObject, .oblique, .genitive, .objComparison]
  , notes := "Particle de + retained pronoun; optional at DO" }

/-- All Mandarin relative clause markers. -/
def relMarkers : List Marker := [relDeGap, relDeResumptive]

end Mandarin
